import Erdos249257.DiagonalPincerCertificatesT64

-- Explicit full-window certificate for the earliest successful 72P sweep coordinate.
namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def seventyTwoBRFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem seventyTwoBRFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    seventyTwoBRFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [seventyTwoBRFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [seventyTwoBRFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then seventyTwoBRFastPow a n * seventyTwoBRFastPow a n * a
        else seventyTwoBRFastPow a n * seventyTwoBRFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_seventyTwoBR_2 : Nat.Prime 2 := by norm_num

private theorem prime_seventyTwoBR_3 : Nat.Prime 3 := by norm_num

private theorem prime_seventyTwoBR_5 : Nat.Prime 5 := by norm_num

private theorem prime_seventyTwoBR_7 : Nat.Prime 7 := by norm_num

private theorem prime_seventyTwoBR_11 : Nat.Prime 11 := by norm_num

private theorem prime_seventyTwoBR_13 : Nat.Prime 13 := by norm_num

private theorem prime_seventyTwoBR_17 : Nat.Prime 17 := by norm_num

private theorem prime_seventyTwoBR_19 : Nat.Prime 19 := by norm_num

private theorem prime_seventyTwoBR_23 : Nat.Prime 23 := by norm_num

private theorem prime_seventyTwoBR_29 : Nat.Prime 29 := by norm_num

private theorem prime_seventyTwoBR_31 : Nat.Prime 31 := by norm_num

private theorem prime_seventyTwoBR_37 : Nat.Prime 37 := by norm_num

private theorem prime_seventyTwoBR_41 : Nat.Prime 41 := by norm_num

private theorem prime_seventyTwoBR_43 : Nat.Prime 43 := by norm_num

private theorem prime_seventyTwoBR_47 : Nat.Prime 47 := by norm_num

private theorem prime_seventyTwoBR_53 : Nat.Prime 53 := by norm_num

private theorem prime_seventyTwoBR_59 : Nat.Prime 59 := by norm_num

private theorem prime_seventyTwoBR_61 : Nat.Prime 61 := by norm_num

private theorem prime_seventyTwoBR_67 : Nat.Prime 67 := by norm_num

private theorem prime_seventyTwoBR_71 : Nat.Prime 71 := by norm_num

private theorem prime_seventyTwoBR_73 : Nat.Prime 73 := by norm_num

private theorem prime_seventyTwoBR_79 : Nat.Prime 79 := by norm_num

private theorem prime_seventyTwoBR_83 : Nat.Prime 83 := by norm_num

private theorem prime_seventyTwoBR_89 : Nat.Prime 89 := by norm_num

private theorem prime_seventyTwoBR_97 : Nat.Prime 97 := by norm_num

private theorem prime_seventyTwoBR_101 : Nat.Prime 101 := by norm_num

private theorem prime_seventyTwoBR_103 : Nat.Prime 103 := by norm_num

private theorem prime_seventyTwoBR_107 : Nat.Prime 107 := by norm_num

private theorem prime_seventyTwoBR_109 : Nat.Prime 109 := by norm_num

private theorem prime_seventyTwoBR_113 : Nat.Prime 113 := by norm_num

private theorem prime_seventyTwoBR_127 : Nat.Prime 127 := by norm_num

private theorem prime_seventyTwoBR_131 : Nat.Prime 131 := by norm_num

private theorem prime_seventyTwoBR_137 : Nat.Prime 137 := by norm_num

private theorem prime_seventyTwoBR_139 : Nat.Prime 139 := by norm_num

private theorem prime_seventyTwoBR_149 : Nat.Prime 149 := by norm_num

private theorem prime_seventyTwoBR_151 : Nat.Prime 151 := by norm_num

private theorem prime_seventyTwoBR_157 : Nat.Prime 157 := by norm_num

private theorem prime_seventyTwoBR_163 : Nat.Prime 163 := by norm_num

private theorem prime_seventyTwoBR_167 : Nat.Prime 167 := by norm_num

private theorem prime_seventyTwoBR_173 : Nat.Prime 173 := by norm_num

private theorem prime_seventyTwoBR_179 : Nat.Prime 179 := by norm_num

private theorem prime_seventyTwoBR_181 : Nat.Prime 181 := by norm_num

private theorem prime_seventyTwoBR_191 : Nat.Prime 191 := by norm_num

private theorem prime_seventyTwoBR_193 : Nat.Prime 193 := by norm_num

private theorem prime_seventyTwoBR_197 : Nat.Prime 197 := by norm_num

private theorem prime_seventyTwoBR_199 : Nat.Prime 199 := by norm_num

private theorem prime_seventyTwoBR_211 : Nat.Prime 211 := by norm_num

private theorem prime_seventyTwoBR_223 : Nat.Prime 223 := by norm_num

private theorem prime_seventyTwoBR_227 : Nat.Prime 227 := by norm_num

private theorem prime_seventyTwoBR_229 : Nat.Prime 229 := by norm_num

private theorem prime_seventyTwoBR_233 : Nat.Prime 233 := by norm_num

private theorem prime_seventyTwoBR_239 : Nat.Prime 239 := by norm_num

private theorem prime_seventyTwoBR_241 : Nat.Prime 241 := by norm_num

private theorem prime_seventyTwoBR_257 : Nat.Prime 257 := by norm_num

private theorem prime_seventyTwoBR_263 : Nat.Prime 263 := by norm_num

private theorem prime_seventyTwoBR_269 : Nat.Prime 269 := by norm_num

private theorem prime_seventyTwoBR_277 : Nat.Prime 277 := by norm_num

private theorem prime_seventyTwoBR_281 : Nat.Prime 281 := by norm_num

private theorem prime_seventyTwoBR_293 : Nat.Prime 293 := by norm_num

private theorem prime_seventyTwoBR_307 : Nat.Prime 307 := by norm_num

private theorem prime_seventyTwoBR_311 : Nat.Prime 311 := by norm_num

private theorem prime_seventyTwoBR_313 : Nat.Prime 313 := by norm_num

private theorem prime_seventyTwoBR_317 : Nat.Prime 317 := by norm_num

private theorem prime_seventyTwoBR_331 : Nat.Prime 331 := by norm_num

private theorem prime_seventyTwoBR_337 : Nat.Prime 337 := by norm_num

private theorem prime_seventyTwoBR_347 : Nat.Prime 347 := by norm_num

private theorem prime_seventyTwoBR_349 : Nat.Prime 349 := by norm_num

private theorem prime_seventyTwoBR_367 : Nat.Prime 367 := by norm_num

private theorem prime_seventyTwoBR_379 : Nat.Prime 379 := by norm_num

private theorem prime_seventyTwoBR_383 : Nat.Prime 383 := by norm_num

private theorem prime_seventyTwoBR_389 : Nat.Prime 389 := by norm_num

private theorem prime_seventyTwoBR_397 : Nat.Prime 397 := by norm_num

private theorem prime_seventyTwoBR_401 : Nat.Prime 401 := by norm_num

private theorem prime_seventyTwoBR_409 : Nat.Prime 409 := by norm_num

private theorem prime_seventyTwoBR_419 : Nat.Prime 419 := by norm_num

private theorem prime_seventyTwoBR_421 : Nat.Prime 421 := by norm_num

private theorem prime_seventyTwoBR_433 : Nat.Prime 433 := by norm_num

private theorem prime_seventyTwoBR_439 : Nat.Prime 439 := by norm_num

private theorem prime_seventyTwoBR_463 : Nat.Prime 463 := by norm_num

private theorem prime_seventyTwoBR_491 : Nat.Prime 491 := by norm_num

private theorem prime_seventyTwoBR_499 : Nat.Prime 499 := by norm_num

private theorem prime_seventyTwoBR_503 : Nat.Prime 503 := by norm_num

private theorem prime_seventyTwoBR_541 : Nat.Prime 541 := by norm_num

private theorem prime_seventyTwoBR_557 : Nat.Prime 557 := by norm_num

private theorem prime_seventyTwoBR_607 : Nat.Prime 607 := by norm_num

private theorem prime_seventyTwoBR_617 : Nat.Prime 617 := by norm_num

private theorem prime_seventyTwoBR_619 : Nat.Prime 619 := by norm_num

private theorem prime_seventyTwoBR_631 : Nat.Prime 631 := by norm_num

private theorem prime_seventyTwoBR_643 : Nat.Prime 643 := by norm_num

private theorem prime_seventyTwoBR_647 : Nat.Prime 647 := by norm_num

private theorem prime_seventyTwoBR_683 : Nat.Prime 683 := by norm_num

private theorem prime_seventyTwoBR_709 : Nat.Prime 709 := by norm_num

private theorem prime_seventyTwoBR_733 : Nat.Prime 733 := by norm_num

private theorem prime_seventyTwoBR_739 : Nat.Prime 739 := by norm_num

private theorem prime_seventyTwoBR_751 : Nat.Prime 751 := by norm_num

private theorem prime_seventyTwoBR_757 : Nat.Prime 757 := by norm_num

private theorem prime_seventyTwoBR_773 : Nat.Prime 773 := by norm_num

private theorem prime_seventyTwoBR_797 : Nat.Prime 797 := by norm_num

private theorem prime_seventyTwoBR_811 : Nat.Prime 811 := by norm_num

private theorem prime_seventyTwoBR_853 : Nat.Prime 853 := by norm_num

private theorem prime_seventyTwoBR_883 : Nat.Prime 883 := by norm_num

private theorem prime_seventyTwoBR_911 : Nat.Prime 911 := by norm_num

private theorem prime_seventyTwoBR_919 : Nat.Prime 919 := by norm_num

private theorem prime_seventyTwoBR_929 : Nat.Prime 929 := by norm_num

private theorem prime_seventyTwoBR_971 : Nat.Prime 971 := by norm_num

private theorem prime_seventyTwoBR_1009 : Nat.Prime 1009 := by norm_num

private theorem prime_seventyTwoBR_1019 : Nat.Prime 1019 := by norm_num

private theorem prime_seventyTwoBR_1021 : Nat.Prime 1021 := by norm_num

private theorem prime_seventyTwoBR_1061 : Nat.Prime 1061 := by norm_num

private theorem prime_seventyTwoBR_1063 : Nat.Prime 1063 := by norm_num

private theorem prime_seventyTwoBR_1087 : Nat.Prime 1087 := by norm_num

private theorem prime_seventyTwoBR_1093 : Nat.Prime 1093 := by norm_num

private theorem prime_seventyTwoBR_1109 : Nat.Prime 1109 := by norm_num

private theorem prime_seventyTwoBR_1117 : Nat.Prime 1117 := by norm_num

private theorem prime_seventyTwoBR_1151 : Nat.Prime 1151 := by norm_num

private theorem prime_seventyTwoBR_1163 : Nat.Prime 1163 := by norm_num

private theorem prime_seventyTwoBR_1171 : Nat.Prime 1171 := by norm_num

private theorem prime_seventyTwoBR_1181 : Nat.Prime 1181 := by norm_num

private theorem prime_seventyTwoBR_1201 : Nat.Prime 1201 := by norm_num

private theorem prime_seventyTwoBR_1217 : Nat.Prime 1217 := by norm_num

private theorem prime_seventyTwoBR_1279 : Nat.Prime 1279 := by norm_num

private theorem prime_seventyTwoBR_1297 : Nat.Prime 1297 := by norm_num

private theorem prime_seventyTwoBR_1307 : Nat.Prime 1307 := by norm_num

private theorem prime_seventyTwoBR_1361 : Nat.Prime 1361 := by norm_num

private theorem prime_seventyTwoBR_1493 : Nat.Prime 1493 := by norm_num

private theorem prime_seventyTwoBR_1511 : Nat.Prime 1511 := by norm_num

private theorem prime_seventyTwoBR_1523 : Nat.Prime 1523 := by norm_num

private theorem prime_seventyTwoBR_1559 : Nat.Prime 1559 := by norm_num

private theorem prime_seventyTwoBR_1567 : Nat.Prime 1567 := by norm_num

private theorem prime_seventyTwoBR_1571 : Nat.Prime 1571 := by norm_num

private theorem prime_seventyTwoBR_1627 : Nat.Prime 1627 := by norm_num

private theorem prime_seventyTwoBR_1693 : Nat.Prime 1693 := by norm_num

private theorem prime_seventyTwoBR_1777 : Nat.Prime 1777 := by norm_num

private theorem prime_seventyTwoBR_1861 : Nat.Prime 1861 := by norm_num

private theorem prime_seventyTwoBR_1973 : Nat.Prime 1973 := by norm_num

private theorem prime_seventyTwoBR_1987 : Nat.Prime 1987 := by norm_num

private theorem prime_seventyTwoBR_1999 : Nat.Prime 1999 := by norm_num

private theorem prime_seventyTwoBR_2053 : Nat.Prime 2053 := by norm_num

private theorem prime_seventyTwoBR_2111 : Nat.Prime 2111 := by norm_num

private theorem prime_seventyTwoBR_2137 : Nat.Prime 2137 := by norm_num

private theorem prime_seventyTwoBR_2371 : Nat.Prime 2371 := by norm_num

private theorem prime_seventyTwoBR_2411 : Nat.Prime 2411 := by norm_num

private theorem prime_seventyTwoBR_2531 : Nat.Prime 2531 := by norm_num

private theorem prime_seventyTwoBR_2591 : Nat.Prime 2591 := by norm_num

private theorem prime_seventyTwoBR_2617 : Nat.Prime 2617 := by norm_num

private theorem prime_seventyTwoBR_2663 : Nat.Prime 2663 := by norm_num

private theorem prime_seventyTwoBR_2693 : Nat.Prime 2693 := by norm_num

private theorem prime_seventyTwoBR_2707 : Nat.Prime 2707 := by norm_num

private theorem prime_seventyTwoBR_2713 : Nat.Prime 2713 := by norm_num

private theorem prime_seventyTwoBR_2741 : Nat.Prime 2741 := by norm_num

private theorem prime_seventyTwoBR_2971 : Nat.Prime 2971 := by norm_num

private theorem prime_seventyTwoBR_3011 : Nat.Prime 3011 := by norm_num

private theorem prime_seventyTwoBR_3067 : Nat.Prime 3067 := by norm_num

private theorem prime_seventyTwoBR_3137 : Nat.Prime 3137 := by norm_num

private theorem prime_seventyTwoBR_3181 : Nat.Prime 3181 := by norm_num

private theorem prime_seventyTwoBR_3361 : Nat.Prime 3361 := by norm_num

private theorem prime_seventyTwoBR_3511 : Nat.Prime 3511 := by norm_num

private theorem prime_seventyTwoBR_3767 : Nat.Prime 3767 := by norm_num

private theorem prime_seventyTwoBR_4021 : Nat.Prime 4021 := by norm_num

private theorem prime_seventyTwoBR_4093 : Nat.Prime 4093 := by norm_num

private theorem prime_seventyTwoBR_4099 : Nat.Prime 4099 := by norm_num

private theorem prime_seventyTwoBR_4111 : Nat.Prime 4111 := by norm_num

private theorem prime_seventyTwoBR_4133 : Nat.Prime 4133 := by norm_num

private theorem prime_seventyTwoBR_4349 : Nat.Prime 4349 := by norm_num

private theorem prime_seventyTwoBR_4451 : Nat.Prime 4451 := by norm_num

private theorem prime_seventyTwoBR_4567 : Nat.Prime 4567 := by norm_num

private theorem prime_seventyTwoBR_4691 : Nat.Prime 4691 := by norm_num

private theorem prime_seventyTwoBR_4937 : Nat.Prime 4937 := by norm_num

private theorem prime_seventyTwoBR_4957 : Nat.Prime 4957 := by norm_num

private theorem prime_seventyTwoBR_4993 : Nat.Prime 4993 := by norm_num

private theorem prime_seventyTwoBR_5309 : Nat.Prime 5309 := by norm_num

private theorem prime_seventyTwoBR_5333 : Nat.Prime 5333 := by norm_num

private theorem prime_seventyTwoBR_5573 : Nat.Prime 5573 := by norm_num

private theorem prime_seventyTwoBR_5741 : Nat.Prime 5741 := by norm_num

private theorem prime_seventyTwoBR_5791 : Nat.Prime 5791 := by norm_num

private theorem prime_seventyTwoBR_5807 : Nat.Prime 5807 := by norm_num

private theorem prime_seventyTwoBR_6007 : Nat.Prime 6007 := by norm_num

private theorem prime_seventyTwoBR_6197 : Nat.Prime 6197 := by norm_num

private theorem prime_seventyTwoBR_6199 : Nat.Prime 6199 := by norm_num

private theorem prime_seventyTwoBR_6299 : Nat.Prime 6299 := by norm_num

private theorem prime_seventyTwoBR_6301 : Nat.Prime 6301 := by norm_num

private theorem prime_seventyTwoBR_6361 : Nat.Prime 6361 := by norm_num

private theorem prime_seventyTwoBR_6547 : Nat.Prime 6547 := by norm_num

private theorem prime_seventyTwoBR_6679 : Nat.Prime 6679 := by norm_num

private theorem prime_seventyTwoBR_6737 : Nat.Prime 6737 := by norm_num

private theorem prime_seventyTwoBR_6827 : Nat.Prime 6827 := by norm_num

private theorem prime_seventyTwoBR_6883 : Nat.Prime 6883 := by norm_num

private theorem prime_seventyTwoBR_7013 : Nat.Prime 7013 := by norm_num

private theorem prime_seventyTwoBR_7589 : Nat.Prime 7589 := by norm_num

private theorem prime_seventyTwoBR_8093 : Nat.Prime 8093 := by norm_num

private theorem prime_seventyTwoBR_8209 : Nat.Prime 8209 := by norm_num

private theorem prime_seventyTwoBR_8369 : Nat.Prime 8369 := by norm_num

private theorem prime_seventyTwoBR_8803 : Nat.Prime 8803 := by norm_num

private theorem prime_seventyTwoBR_8969 : Nat.Prime 8969 := by norm_num

private theorem prime_seventyTwoBR_9001 : Nat.Prime 9001 := by norm_num

private theorem prime_seventyTwoBR_9791 : Nat.Prime 9791 := by norm_num

private theorem prime_seventyTwoBR_9859 : Nat.Prime 9859 := by norm_num

private theorem prime_seventyTwoBR_9923 : Nat.Prime 9923 := by norm_num

private theorem prime_seventyTwoBR_9967 : Nat.Prime 9967 := by norm_num

private theorem prime_seventyTwoBR_10093 : Nat.Prime 10093 := by norm_num

private theorem prime_seventyTwoBR_10159 : Nat.Prime 10159 := by norm_num

private theorem prime_seventyTwoBR_10463 : Nat.Prime 10463 := by norm_num

private theorem prime_seventyTwoBR_10867 : Nat.Prime 10867 := by norm_num

private theorem prime_seventyTwoBR_11677 : Nat.Prime 11677 := by norm_num

private theorem prime_seventyTwoBR_11927 : Nat.Prime 11927 := by norm_num

private theorem prime_seventyTwoBR_12227 : Nat.Prime 12227 := by norm_num

private theorem prime_seventyTwoBR_12697 : Nat.Prime 12697 := by norm_num

private theorem prime_seventyTwoBR_12829 : Nat.Prime 12829 := by norm_num

private theorem prime_seventyTwoBR_12841 : Nat.Prime 12841 := by norm_num

private theorem prime_seventyTwoBR_13003 : Nat.Prime 13003 := by norm_num

private theorem prime_seventyTwoBR_13217 : Nat.Prime 13217 := by norm_num

private theorem prime_seventyTwoBR_13313 : Nat.Prime 13313 := by norm_num

private theorem prime_seventyTwoBR_13417 : Nat.Prime 13417 := by norm_num

private theorem prime_seventyTwoBR_13723 : Nat.Prime 13723 := by norm_num

private theorem prime_seventyTwoBR_14323 : Nat.Prime 14323 := by norm_num

private theorem prime_seventyTwoBR_14369 : Nat.Prime 14369 := by norm_num

private theorem prime_seventyTwoBR_14797 : Nat.Prime 14797 := by norm_num

private theorem prime_seventyTwoBR_14851 : Nat.Prime 14851 := by norm_num

private theorem prime_seventyTwoBR_15889 : Nat.Prime 15889 := by norm_num

private theorem prime_seventyTwoBR_16447 : Nat.Prime 16447 := by norm_num

private theorem prime_seventyTwoBR_16567 : Nat.Prime 16567 := by norm_num

private theorem prime_seventyTwoBR_17573 : Nat.Prime 17573 := by norm_num

private theorem prime_seventyTwoBR_17749 : Nat.Prime 17749 := by norm_num

private theorem prime_seventyTwoBR_18217 : Nat.Prime 18217 := by norm_num

private theorem prime_seventyTwoBR_18793 : Nat.Prime 18793 := by norm_num

private theorem prime_seventyTwoBR_19069 : Nat.Prime 19069 := by norm_num

private theorem prime_seventyTwoBR_19157 : Nat.Prime 19157 := by norm_num

private theorem prime_seventyTwoBR_19273 : Nat.Prime 19273 := by norm_num

private theorem prime_seventyTwoBR_19309 : Nat.Prime 19309 := by norm_num

private theorem prime_seventyTwoBR_19751 : Nat.Prime 19751 := by norm_num

private theorem prime_seventyTwoBR_19793 : Nat.Prime 19793 := by norm_num

private theorem prime_seventyTwoBR_20407 : Nat.Prime 20407 := by norm_num

private theorem prime_seventyTwoBR_20639 : Nat.Prime 20639 := by norm_num

private theorem prime_seventyTwoBR_21283 : Nat.Prime 21283 := by norm_num

private theorem prime_seventyTwoBR_21647 : Nat.Prime 21647 := by norm_num

private theorem prime_seventyTwoBR_21859 : Nat.Prime 21859 := by norm_num

private theorem prime_seventyTwoBR_21863 : Nat.Prime 21863 := by norm_num

private theorem prime_seventyTwoBR_23167 : Nat.Prime 23167 := by norm_num

private theorem prime_seventyTwoBR_23761 : Nat.Prime 23761 := by norm_num

private theorem prime_seventyTwoBR_23833 : Nat.Prime 23833 := by norm_num

private theorem prime_seventyTwoBR_23977 : Nat.Prime 23977 := by norm_num

private theorem prime_seventyTwoBR_24407 : Nat.Prime 24407 := by norm_num

private theorem prime_seventyTwoBR_24631 : Nat.Prime 24631 := by norm_num

private theorem prime_seventyTwoBR_25733 : Nat.Prime 25733 := by norm_num

private theorem prime_seventyTwoBR_26177 : Nat.Prime 26177 := by norm_num

private theorem prime_seventyTwoBR_26263 : Nat.Prime 26263 := by norm_num

private theorem prime_seventyTwoBR_26321 : Nat.Prime 26321 := by norm_num

private theorem prime_seventyTwoBR_26987 : Nat.Prime 26987 := by norm_num

private theorem prime_seventyTwoBR_30059 : Nat.Prime 30059 := by norm_num

private theorem prime_seventyTwoBR_31667 : Nat.Prime 31667 := by norm_num

private theorem prime_seventyTwoBR_32749 : Nat.Prime 32749 := by norm_num

private theorem prime_seventyTwoBR_33461 : Nat.Prime 33461 := by norm_num

private theorem prime_seventyTwoBR_33623 : Nat.Prime 33623 := by norm_num

private theorem prime_seventyTwoBR_33997 : Nat.Prime 33997 := by norm_num

private theorem prime_seventyTwoBR_34513 : Nat.Prime 34513 := by norm_num

private theorem prime_seventyTwoBR_38867 : Nat.Prime 38867 := by norm_num

private theorem prime_seventyTwoBR_39439 : Nat.Prime 39439 := by norm_num

private theorem prime_seventyTwoBR_39761 : Nat.Prime 39761 := by norm_num

private theorem prime_seventyTwoBR_39929 : Nat.Prime 39929 := by norm_num

private theorem prime_seventyTwoBR_40499 : Nat.Prime 40499 := by norm_num

private theorem prime_seventyTwoBR_41201 : Nat.Prime 41201 := by norm_num

private theorem prime_seventyTwoBR_41957 : Nat.Prime 41957 := by norm_num

private theorem prime_seventyTwoBR_43271 : Nat.Prime 43271 := by norm_num

private theorem prime_seventyTwoBR_44839 : Nat.Prime 44839 := by norm_num

private theorem prime_seventyTwoBR_46349 : Nat.Prime 46349 := by norm_num

private theorem prime_seventyTwoBR_49783 : Nat.Prime 49783 := by norm_num

private theorem prime_seventyTwoBR_51521 : Nat.Prime 51521 := by norm_num

private theorem prime_seventyTwoBR_52673 : Nat.Prime 52673 := by norm_num

private theorem prime_seventyTwoBR_53359 : Nat.Prime 53359 := by norm_num

private theorem prime_seventyTwoBR_57119 : Nat.Prime 57119 := by norm_num

private theorem prime_seventyTwoBR_57331 : Nat.Prime 57331 := by norm_num

private theorem prime_seventyTwoBR_58031 : Nat.Prime 58031 := by norm_num

private theorem prime_seventyTwoBR_65563 : Nat.Prime 65563 := by norm_num

private theorem prime_seventyTwoBR_67189 : Nat.Prime 67189 := by norm_num

private theorem prime_seventyTwoBR_74383 : Nat.Prime 74383 := by norm_num

private theorem prime_seventyTwoBR_85243 : Nat.Prime 85243 := by norm_num

private theorem prime_seventyTwoBR_85577 : Nat.Prime 85577 := by norm_num

private theorem prime_seventyTwoBR_85831 : Nat.Prime 85831 := by norm_num

private theorem prime_seventyTwoBR_88591 : Nat.Prime 88591 := by norm_num

private theorem prime_seventyTwoBR_89599 : Nat.Prime 89599 := by norm_num

private theorem prime_seventyTwoBR_94687 : Nat.Prime 94687 := by norm_num

private theorem prime_seventyTwoBR_97039 : Nat.Prime 97039 := by norm_num

private theorem prime_seventyTwoBR_98327 : Nat.Prime 98327 := by norm_num

private theorem prime_seventyTwoBR_104527 : Nat.Prime 104527 := by norm_num

private theorem prime_seventyTwoBR_105649 : Nat.Prime 105649 := by norm_num

private theorem prime_seventyTwoBR_107509 : Nat.Prime 107509 := by norm_num

private theorem prime_seventyTwoBR_111893 : Nat.Prime 111893 := by norm_num

private theorem prime_seventyTwoBR_114661 : Nat.Prime 114661 := by norm_num

private theorem prime_seventyTwoBR_115679 : Nat.Prime 115679 := by norm_num

private theorem prime_seventyTwoBR_118361 : Nat.Prime 118361 := by norm_num

private theorem prime_seventyTwoBR_124919 : Nat.Prime 124919 := by norm_num

private theorem prime_seventyTwoBR_129707 : Nat.Prime 129707 := by norm_num

private theorem prime_seventyTwoBR_138841 : Nat.Prime 138841 := by norm_num

private theorem prime_seventyTwoBR_141961 : Nat.Prime 141961 := by norm_num

private theorem prime_seventyTwoBR_149767 : Nat.Prime 149767 := by norm_num

private theorem prime_seventyTwoBR_150587 : Nat.Prime 150587 := by norm_num

private theorem prime_seventyTwoBR_150767 : Nat.Prime 150767 := by norm_num

private theorem prime_seventyTwoBR_153133 : Nat.Prime 153133 := by norm_num

private theorem prime_seventyTwoBR_155009 : Nat.Prime 155009 := by norm_num

private theorem prime_seventyTwoBR_162623 : Nat.Prime 162623 := by norm_num

private theorem prime_seventyTwoBR_163909 : Nat.Prime 163909 := by norm_num

private theorem prime_seventyTwoBR_168253 : Nat.Prime 168253 := by norm_num

private theorem prime_seventyTwoBR_169937 : Nat.Prime 169937 := by norm_num

private theorem prime_seventyTwoBR_196177 : Nat.Prime 196177 := by norm_num

private theorem prime_seventyTwoBR_205213 : Nat.Prime 205213 := by norm_num

private theorem prime_seventyTwoBR_205721 : Nat.Prime 205721 := by norm_num

private theorem prime_seventyTwoBR_210967 : Nat.Prime 210967 := by norm_num

private theorem prime_seventyTwoBR_213919 : Nat.Prime 213919 := by norm_num

private theorem prime_seventyTwoBR_214987 : Nat.Prime 214987 := by norm_num

private theorem prime_seventyTwoBR_226099 : Nat.Prime 226099 := by norm_num

private theorem prime_seventyTwoBR_241963 : Nat.Prime 241963 := by norm_num

private theorem prime_seventyTwoBR_244147 : Nat.Prime 244147 := by norm_num

private theorem prime_seventyTwoBR_247099 : Nat.Prime 247099 := by norm_num

private theorem prime_seventyTwoBR_252823 : Nat.Prime 252823 := by norm_num

private theorem prime_seventyTwoBR_255049 : Nat.Prime 255049 := by norm_num

private theorem prime_seventyTwoBR_257713 : Nat.Prime 257713 := by norm_num

private theorem prime_seventyTwoBR_269189 : Nat.Prime 269189 := by norm_num

private theorem prime_seventyTwoBR_273601 : Nat.Prime 273601 := by norm_num

private theorem prime_seventyTwoBR_309571 : Nat.Prime 309571 := by norm_num

private theorem prime_seventyTwoBR_315373 : Nat.Prime 315373 := by norm_num

private theorem prime_seventyTwoBR_333139 : Nat.Prime 333139 := by norm_num

private theorem prime_seventyTwoBR_333457 : Nat.Prime 333457 := by norm_num

private theorem prime_seventyTwoBR_338839 : Nat.Prime 338839 := by norm_num

private theorem prime_seventyTwoBR_352883 : Nat.Prime 352883 := by norm_num

private theorem prime_seventyTwoBR_374887 : Nat.Prime 374887 := by norm_num

private theorem prime_seventyTwoBR_381167 : Nat.Prime 381167 := by norm_num

private theorem prime_seventyTwoBR_382331 : Nat.Prime 382331 := by norm_num

private theorem prime_seventyTwoBR_443753 : Nat.Prime 443753 := by norm_num

private theorem prime_seventyTwoBR_501173 : Nat.Prime 501173 := by norm_num

private theorem prime_seventyTwoBR_525391 : Nat.Prime 525391 := by norm_num

private theorem prime_seventyTwoBR_565109 : Nat.Prime 565109 := by norm_num

private theorem prime_seventyTwoBR_594749 : Nat.Prime 594749 := by norm_num

private theorem prime_seventyTwoBR_624797 : Nat.Prime 624797 := by norm_num

private theorem prime_seventyTwoBR_648917 : Nat.Prime 648917 := by norm_num

private theorem prime_seventyTwoBR_652019 : Nat.Prime 652019 := by norm_num

private theorem prime_seventyTwoBR_666937 : Nat.Prime 666937 := by norm_num

private theorem prime_seventyTwoBR_831553 : Nat.Prime 831553 := by norm_num

private theorem prime_seventyTwoBR_906211 : Nat.Prime 906211 := by norm_num

private theorem prime_seventyTwoBR_915919 : Nat.Prime 915919 := by norm_num

private theorem prime_seventyTwoBR_965467 : Nat.Prime 965467 := by norm_num

private theorem prime_seventyTwoBR_1004117 : Nat.Prime 1004117 := by norm_num

private theorem prime_seventyTwoBR_1187089 : Nat.Prime 1187089 := by norm_num

private theorem prime_seventyTwoBR_1196519 : Nat.Prime 1196519 := by norm_num

private theorem prime_seventyTwoBR_1245617 : Nat.Prime 1245617 := by norm_num

private theorem prime_seventyTwoBR_1248151 : Nat.Prime 1248151 := by norm_num

private theorem prime_seventyTwoBR_1573699 : Nat.Prime 1573699 := by norm_num

private theorem prime_seventyTwoBR_1634441 : Nat.Prime 1634441 := by norm_num

private theorem prime_seventyTwoBR_1640953 : Nat.Prime 1640953 := by norm_num

private theorem prime_seventyTwoBR_1655531 : Nat.Prime 1655531 := by norm_num

private theorem prime_seventyTwoBR_1669223 : Nat.Prime 1669223 := by norm_num

private theorem prime_seventyTwoBR_1702121 : Nat.Prime 1702121 := by norm_num

private theorem prime_seventyTwoBR_1720151 : Nat.Prime 1720151 := by norm_num

private theorem prime_seventyTwoBR_1750733 : Nat.Prime 1750733 := by norm_num

private theorem prime_seventyTwoBR_1841699 : Nat.Prime 1841699 := by norm_num

private theorem prime_seventyTwoBR_1896221 : Nat.Prime 1896221 := by norm_num

private theorem prime_seventyTwoBR_1901567 : Nat.Prime 1901567 := by norm_num

private theorem prime_seventyTwoBR_1996487 : Nat.Prime 1996487 := by norm_num

private theorem prime_seventyTwoBR_2027569 : Nat.Prime 2027569 := by norm_num

private theorem prime_seventyTwoBR_2261887 : Nat.Prime 2261887 := by norm_num

private theorem prime_seventyTwoBR_2659073 : Nat.Prime 2659073 := by norm_num

private theorem prime_seventyTwoBR_2703917 : Nat.Prime 2703917 := by norm_num

private theorem prime_seventyTwoBR_2855557 : Nat.Prime 2855557 := by norm_num

private theorem prime_seventyTwoBR_2903767 : Nat.Prime 2903767 := by norm_num

private theorem prime_seventyTwoBR_3097769 : Nat.Prime 3097769 := by norm_num

private theorem prime_seventyTwoBR_3116837 : Nat.Prime 3116837 := by norm_num

private theorem prime_seventyTwoBR_3160741 : Nat.Prime 3160741 := by norm_num

private theorem prime_seventyTwoBR_3207013 : Nat.Prime 3207013 := by norm_num

private theorem prime_seventyTwoBR_3316057 : Nat.Prime 3316057 := by norm_num

private theorem prime_seventyTwoBR_3717893 : Nat.Prime 3717893 := by norm_num

private theorem prime_seventyTwoBR_3726991 : Nat.Prime 3726991 := by norm_num

private theorem prime_seventyTwoBR_3757451 : Nat.Prime 3757451 := by norm_num

private theorem prime_seventyTwoBR_3934369 : Nat.Prime 3934369 := by norm_num

private theorem prime_seventyTwoBR_4159583 : Nat.Prime 4159583 := by norm_num

private theorem prime_seventyTwoBR_4366031 : Nat.Prime 4366031 := by norm_num

private theorem prime_seventyTwoBR_4505783 : Nat.Prime 4505783 := by norm_num

private theorem prime_seventyTwoBR_4920437 : Nat.Prime 4920437 := by norm_num

private theorem prime_seventyTwoBR_5082037 : Nat.Prime 5082037 := by norm_num

private theorem prime_seventyTwoBR_5333437 : Nat.Prime 5333437 := by norm_num

private theorem prime_seventyTwoBR_5449541 : Nat.Prime 5449541 := by norm_num

private theorem prime_seventyTwoBR_5988289 : Nat.Prime 5988289 := by norm_num

private theorem prime_seventyTwoBR_6034139 : Nat.Prime 6034139 := by norm_num

private theorem prime_seventyTwoBR_6271151 : Nat.Prime 6271151 := by norm_num

private theorem prime_seventyTwoBR_6424757 : Nat.Prime 6424757 := by norm_num

private theorem prime_seventyTwoBR_6432109 : Nat.Prime 6432109 := by norm_num

private theorem prime_seventyTwoBR_6538561 : Nat.Prime 6538561 := by norm_num

private theorem prime_seventyTwoBR_6840203 : Nat.Prime 6840203 := by norm_num

private theorem prime_seventyTwoBR_7171237 : Nat.Prime 7171237 := by norm_num

private theorem prime_seventyTwoBR_7280279 : Nat.Prime 7280279 := by norm_num

private theorem prime_seventyTwoBR_7421569 : Nat.Prime 7421569 := by norm_num

private theorem prime_seventyTwoBR_7621213 : Nat.Prime 7621213 := by norm_num

private theorem prime_seventyTwoBR_7624307 : Nat.Prime 7624307 := by norm_num

private theorem prime_seventyTwoBR_7774579 : Nat.Prime 7774579 := by norm_num

private theorem prime_seventyTwoBR_7909259 : Nat.Prime 7909259 := by norm_num

private theorem prime_seventyTwoBR_7922129 : Nat.Prime 7922129 := by norm_num

private theorem prime_seventyTwoBR_8219353 : Nat.Prime 8219353 := by norm_num

private theorem prime_seventyTwoBR_8307437 : Nat.Prime 8307437 := by norm_num

private theorem prime_seventyTwoBR_8531371 : Nat.Prime 8531371 := by norm_num

private theorem prime_seventyTwoBR_8573167 : Nat.Prime 8573167 := by norm_num

private theorem prime_seventyTwoBR_8607563 : Nat.Prime 8607563 := by norm_num

private theorem prime_seventyTwoBR_9001199 : Nat.Prime 9001199 := by norm_num

private theorem prime_seventyTwoBR_9705901 : Nat.Prime 9705901 := by norm_num

private theorem prime_seventyTwoBR_10249391 : Nat.Prime 10249391 := by norm_num

private theorem prime_seventyTwoBR_10340039 : Nat.Prime 10340039 := by norm_num

private theorem prime_seventyTwoBR_10622747 : Nat.Prime 10622747 := by norm_num

private theorem prime_seventyTwoBR_10864429 : Nat.Prime 10864429 := by norm_num

private theorem prime_seventyTwoBR_11210077 : Nat.Prime 11210077 := by norm_num

private theorem prime_seventyTwoBR_11304973 : Nat.Prime 11304973 := by norm_num

private theorem prime_seventyTwoBR_11498537 : Nat.Prime 11498537 := by norm_num

private theorem prime_seventyTwoBR_12816061 : Nat.Prime 12816061 := by norm_num

private theorem prime_seventyTwoBR_13082767 : Nat.Prime 13082767 := by norm_num

private theorem prime_seventyTwoBR_13275277 : Nat.Prime 13275277 := by norm_num

private theorem prime_seventyTwoBR_13522879 : Nat.Prime 13522879 := by norm_num

private theorem prime_seventyTwoBR_14018747 : Nat.Prime 14018747 := by norm_num

private theorem prime_seventyTwoBR_14438953 : Nat.Prime 14438953 := by norm_num

private theorem prime_seventyTwoBR_16994501 : Nat.Prime 16994501 := by norm_num

private theorem prime_seventyTwoBR_17278427 : Nat.Prime 17278427 := by norm_num

private theorem prime_seventyTwoBR_18320791 : Nat.Prime 18320791 := by norm_num

private theorem prime_seventyTwoBR_19135531 : Nat.Prime 19135531 := by norm_num

private theorem prime_seventyTwoBR_19371817 : Nat.Prime 19371817 := by norm_num

private theorem prime_seventyTwoBR_21131977 : Nat.Prime 21131977 := by norm_num

private theorem prime_seventyTwoBR_21161051 : Nat.Prime 21161051 := by norm_num

private theorem prime_seventyTwoBR_25995383 : Nat.Prime 25995383 := by norm_num

private theorem prime_seventyTwoBR_26516779 : Nat.Prime 26516779 := by norm_num

private theorem prime_seventyTwoBR_26820593 : Nat.Prime 26820593 := by norm_num

private theorem prime_seventyTwoBR_27012893 : Nat.Prime 27012893 := by norm_num

private theorem prime_seventyTwoBR_27222109 : Nat.Prime 27222109 := by norm_num

private theorem prime_seventyTwoBR_29270629 : Nat.Prime 29270629 := by norm_num

private theorem prime_seventyTwoBR_34292669 : Nat.Prime 34292669 := by
  apply lucas_primality 34292669 (2 : ZMod 34292669)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (8573167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (8573167, 1)] : List FactorBlock).map factorBlockValue).prod) = 34292669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_8573167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 34292669) ^ 17146334 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 34292669) ^ 4 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_34855157 : Nat.Prime 34855157 := by
  apply lucas_primality 34855157 (2 : ZMod 34855157)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (61, 1), (20407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (61, 1), (20407, 1)] : List FactorBlock).map factorBlockValue).prod) = 34855157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_61
      · exact prime_seventyTwoBR_20407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 34855157) ^ 17427578 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 34855157) ^ 4979308 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 34855157) ^ 571396 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 34855157) ^ 1708 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_36478751 : Nat.Prime 36478751 := by
  apply lucas_primality 36478751 (7 : ZMod 36478751)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 4), (7, 1), (11, 1), (379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 4), (7, 1), (11, 1), (379, 1)] : List FactorBlock).map factorBlockValue).prod) = 36478751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_11
      · exact prime_seventyTwoBR_379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 36478751) ^ 18239375 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 36478751) ^ 7295750 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 36478751) ^ 5211250 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 36478751) ^ 3316250 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 36478751) ^ 96250 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_36838247 : Nat.Prime 36838247 := by
  apply lucas_primality 36838247 (5 : ZMod 36838247)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (439, 1), (41957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (439, 1), (41957, 1)] : List FactorBlock).map factorBlockValue).prod) = 36838247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_439
      · exact prime_seventyTwoBR_41957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 36838247) ^ 18419123 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 36838247) ^ 83914 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 36838247) ^ 878 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_37145327 : Nat.Prime 37145327 := by
  apply lucas_primality 37145327 (5 : ZMod 37145327)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (233, 1), (1009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (233, 1), (1009, 1)] : List FactorBlock).map factorBlockValue).prod) = 37145327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_79
      · exact prime_seventyTwoBR_233
      · exact prime_seventyTwoBR_1009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 37145327) ^ 18572663 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 37145327) ^ 470194 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 37145327) ^ 159422 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 37145327) ^ 36814 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_40990639 : Nat.Prime 40990639 := by
  apply lucas_primality 40990639 (3 : ZMod 40990639)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (17, 1), (19, 1), (1627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (17, 1), (19, 1), (1627, 1)] : List FactorBlock).map factorBlockValue).prod) = 40990639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_13
      · exact prime_seventyTwoBR_17
      · exact prime_seventyTwoBR_19
      · exact prime_seventyTwoBR_1627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 40990639) ^ 20495319 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 40990639) ^ 13663546 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 40990639) ^ 3153126 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 40990639) ^ 2411214 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 40990639) ^ 2157402 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 40990639) ^ 25194 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_41348669 : Nat.Prime 41348669 := by
  apply lucas_primality 41348669 (2 : ZMod 41348669)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (333457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (333457, 1)] : List FactorBlock).map factorBlockValue).prod) = 41348669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_31
      · exact prime_seventyTwoBR_333457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 41348669) ^ 20674334 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 41348669) ^ 1333828 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 41348669) ^ 124 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_44986441 : Nat.Prime 44986441 := by
  apply lucas_primality 44986441 (14 : ZMod 44986441)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (374887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (374887, 1)] : List FactorBlock).map factorBlockValue).prod) = 44986441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_374887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 44986441) ^ 22493220 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (14 : ZMod 44986441) ^ 14995480 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (14 : ZMod 44986441) ^ 8997288 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (14 : ZMod 44986441) ^ 120 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_47716351 : Nat.Prime 47716351 := by
  apply lucas_primality 47716351 (11 : ZMod 47716351)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (11, 3), (239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (11, 3), (239, 1)] : List FactorBlock).map factorBlockValue).prod) = 47716351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_11
      · exact prime_seventyTwoBR_239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 47716351) ^ 23858175 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (11 : ZMod 47716351) ^ 15905450 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (11 : ZMod 47716351) ^ 9543270 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (11 : ZMod 47716351) ^ 4337850 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (11 : ZMod 47716351) ^ 199650 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_54091517 : Nat.Prime 54091517 := by
  apply lucas_primality 54091517 (2 : ZMod 54091517)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13522879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13522879, 1)] : List FactorBlock).map factorBlockValue).prod) = 54091517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_13522879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 54091517) ^ 27045758 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 54091517) ^ 4 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_59249473 : Nat.Prime 59249473 := by
  apply lucas_primality 59249473 (5 : ZMod 59249473)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (23, 1), (13417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (23, 1), (13417, 1)] : List FactorBlock).map factorBlockValue).prod) = 59249473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_23
      · exact prime_seventyTwoBR_13417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 59249473) ^ 29624736 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 59249473) ^ 19749824 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 59249473) ^ 2576064 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 59249473) ^ 4416 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_69516613 : Nat.Prime 69516613 := by
  apply lucas_primality 69516613 (6 : ZMod 69516613)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (349, 1), (503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (349, 1), (503, 1)] : List FactorBlock).map factorBlockValue).prod) = 69516613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_11
      · exact prime_seventyTwoBR_349
      · exact prime_seventyTwoBR_503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 69516613) ^ 34758306 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 69516613) ^ 23172204 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 69516613) ^ 6319692 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 69516613) ^ 199188 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 69516613) ^ 138204 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_75274373 : Nat.Prime 75274373 := by
  apply lucas_primality 75274373 (2 : ZMod 75274373)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (648917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (648917, 1)] : List FactorBlock).map factorBlockValue).prod) = 75274373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_29
      · exact prime_seventyTwoBR_648917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 75274373) ^ 37637186 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 75274373) ^ 2595668 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 75274373) ^ 116 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_76557353 : Nat.Prime 76557353 := by
  apply lucas_primality 76557353 (3 : ZMod 76557353)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (197, 1), (1567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (197, 1), (1567, 1)] : List FactorBlock).map factorBlockValue).prod) = 76557353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_31
      · exact prime_seventyTwoBR_197
      · exact prime_seventyTwoBR_1567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 76557353) ^ 38278676 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 76557353) ^ 2469592 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 76557353) ^ 388616 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 76557353) ^ 48856 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_77487269 : Nat.Prime 77487269 := by
  apply lucas_primality 77487269 (2 : ZMod 77487269)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19371817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19371817, 1)] : List FactorBlock).map factorBlockValue).prod) = 77487269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_19371817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 77487269) ^ 38743634 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 77487269) ^ 4 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_78614959 : Nat.Prime 78614959 := by
  apply lucas_primality 78614959 (6 : ZMod 78614959)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (313, 1), (1021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (313, 1), (1021, 1)] : List FactorBlock).map factorBlockValue).prod) = 78614959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_41
      · exact prime_seventyTwoBR_313
      · exact prime_seventyTwoBR_1021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 78614959) ^ 39307479 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 78614959) ^ 26204986 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 78614959) ^ 1917438 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 78614959) ^ 251166 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 78614959) ^ 76998 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_78624367 : Nat.Prime 78624367 := by
  apply lucas_primality 78624367 (3 : ZMod 78624367)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (67, 1), (131, 1), (1493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (67, 1), (131, 1), (1493, 1)] : List FactorBlock).map factorBlockValue).prod) = 78624367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_67
      · exact prime_seventyTwoBR_131
      · exact prime_seventyTwoBR_1493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 78624367) ^ 39312183 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 78624367) ^ 26208122 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 78624367) ^ 1173498 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 78624367) ^ 600186 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 78624367) ^ 52662 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_79724609 : Nat.Prime 79724609 := by
  apply lucas_primality 79724609 (3 : ZMod 79724609)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (19, 1), (65563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (19, 1), (65563, 1)] : List FactorBlock).map factorBlockValue).prod) = 79724609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_19
      · exact prime_seventyTwoBR_65563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 79724609) ^ 39862304 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 79724609) ^ 4196032 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 79724609) ^ 1216 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_80994743 : Nat.Prime 80994743 := by
  apply lucas_primality 80994743 (5 : ZMod 80994743)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (709, 1), (57119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (709, 1), (57119, 1)] : List FactorBlock).map factorBlockValue).prod) = 80994743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_709
      · exact prime_seventyTwoBR_57119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 80994743) ^ 40497371 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 80994743) ^ 114238 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 80994743) ^ 1418 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_84527909 : Nat.Prime 84527909 := by
  apply lucas_primality 84527909 (2 : ZMod 84527909)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (21131977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (21131977, 1)] : List FactorBlock).map factorBlockValue).prod) = 84527909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_21131977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 84527909) ^ 42263954 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 84527909) ^ 4 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_94427569 : Nat.Prime 94427569 := by
  apply lucas_primality 94427569 (13 : ZMod 94427569)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (19, 1), (34513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (19, 1), (34513, 1)] : List FactorBlock).map factorBlockValue).prod) = 94427569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_19
      · exact prime_seventyTwoBR_34513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 94427569) ^ 47213784 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (13 : ZMod 94427569) ^ 31475856 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (13 : ZMod 94427569) ^ 4969872 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (13 : ZMod 94427569) ^ 2736 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_97173101 : Nat.Prime 97173101 := by
  apply lucas_primality 97173101 (2 : ZMod 97173101)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (37, 1), (26263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (37, 1), (26263, 1)] : List FactorBlock).map factorBlockValue).prod) = 97173101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_37
      · exact prime_seventyTwoBR_26263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 97173101) ^ 48586550 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 97173101) ^ 19434620 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 97173101) ^ 2626300 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 97173101) ^ 3700 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_99769661 : Nat.Prime 99769661 := by
  apply lucas_primality 99769661 (2 : ZMod 99769661)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1217, 1), (4099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1217, 1), (4099, 1)] : List FactorBlock).map factorBlockValue).prod) = 99769661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_1217
      · exact prime_seventyTwoBR_4099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 99769661) ^ 49884830 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 99769661) ^ 19953932 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 99769661) ^ 81980 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 99769661) ^ 24340 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_100318943 : Nat.Prime 100318943 := by
  apply lucas_primality 100318943 (5 : ZMod 100318943)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2111, 1), (23761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2111, 1), (23761, 1)] : List FactorBlock).map factorBlockValue).prod) = 100318943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_2111
      · exact prime_seventyTwoBR_23761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 100318943) ^ 50159471 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 100318943) ^ 47522 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 100318943) ^ 4222 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_100580761 : Nat.Prime 100580761 := by
  apply lucas_primality 100580761 (11 : ZMod 100580761)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (7, 1), (167, 1), (239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (7, 1), (167, 1), (239, 1)] : List FactorBlock).map factorBlockValue).prod) = 100580761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_167
      · exact prime_seventyTwoBR_239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 100580761) ^ 50290380 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (11 : ZMod 100580761) ^ 33526920 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (11 : ZMod 100580761) ^ 20116152 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (11 : ZMod 100580761) ^ 14368680 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (11 : ZMod 100580761) ^ 602280 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (11 : ZMod 100580761) ^ 420840 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_103201937 : Nat.Prime 103201937 := by
  apply lucas_primality 103201937 (3 : ZMod 103201937)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (797, 1), (8093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (797, 1), (8093, 1)] : List FactorBlock).map factorBlockValue).prod) = 103201937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_797
      · exact prime_seventyTwoBR_8093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 103201937) ^ 51600968 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 103201937) ^ 129488 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 103201937) ^ 12752 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_104842123 : Nat.Prime 104842123 := by
  apply lucas_primality 104842123 (2 : ZMod 104842123)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (257, 1), (883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (257, 1), (883, 1)] : List FactorBlock).map factorBlockValue).prod) = 104842123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_11
      · exact prime_seventyTwoBR_257
      · exact prime_seventyTwoBR_883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 104842123) ^ 52421061 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 104842123) ^ 34947374 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 104842123) ^ 14977446 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 104842123) ^ 9531102 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 104842123) ^ 407946 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 104842123) ^ 118734 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_108193333 : Nat.Prime 108193333 := by
  apply lucas_primality 108193333 (2 : ZMod 108193333)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (43, 1), (127, 2)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (43, 1), (127, 2)] : List FactorBlock).map factorBlockValue).prod) = 108193333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_13
      · exact prime_seventyTwoBR_43
      · exact prime_seventyTwoBR_127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 108193333) ^ 54096666 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 108193333) ^ 36064444 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 108193333) ^ 8322564 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 108193333) ^ 2516124 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 108193333) ^ 851916 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_108614503 : Nat.Prime 108614503 := by
  apply lucas_primality 108614503 (3 : ZMod 108614503)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (6034139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (6034139, 1)] : List FactorBlock).map factorBlockValue).prod) = 108614503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_6034139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 108614503) ^ 54307251 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 108614503) ^ 36204834 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 108614503) ^ 18 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_112190861 : Nat.Prime 112190861 := by
  apply lucas_primality 112190861 (2 : ZMod 112190861)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (31, 1), (59, 1), (3067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (31, 1), (59, 1), (3067, 1)] : List FactorBlock).map factorBlockValue).prod) = 112190861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_31
      · exact prime_seventyTwoBR_59
      · exact prime_seventyTwoBR_3067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 112190861) ^ 56095430 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 112190861) ^ 22438172 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 112190861) ^ 3619060 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 112190861) ^ 1901540 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 112190861) ^ 36580 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_116750789 : Nat.Prime 116750789 := by
  apply lucas_primality 116750789 (2 : ZMod 116750789)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (83, 1), (4567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (83, 1), (4567, 1)] : List FactorBlock).map factorBlockValue).prod) = 116750789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_11
      · exact prime_seventyTwoBR_83
      · exact prime_seventyTwoBR_4567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 116750789) ^ 58375394 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 116750789) ^ 16678684 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 116750789) ^ 10613708 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 116750789) ^ 1406636 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 116750789) ^ 25564 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_117082517 : Nat.Prime 117082517 := by
  apply lucas_primality 117082517 (2 : ZMod 117082517)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29270629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29270629, 1)] : List FactorBlock).map factorBlockValue).prod) = 117082517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_29270629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 117082517) ^ 58541258 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 117082517) ^ 4 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_121323583 : Nat.Prime 121323583 := by
  apply lucas_primality 121323583 (5 : ZMod 121323583)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (191, 1), (1307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (191, 1), (1307, 1)] : List FactorBlock).map factorBlockValue).prod) = 121323583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_191
      · exact prime_seventyTwoBR_1307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 121323583) ^ 60661791 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 121323583) ^ 40441194 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 121323583) ^ 635202 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 121323583) ^ 92826 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_125423021 : Nat.Prime 125423021 := by
  apply lucas_primality 125423021 (3 : ZMod 125423021)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (6271151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (6271151, 1)] : List FactorBlock).map factorBlockValue).prod) = 125423021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_6271151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 125423021) ^ 62711510 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 125423021) ^ 25084604 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 125423021) ^ 20 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_133592203 : Nat.Prime 133592203 := by
  apply lucas_primality 133592203 (14 : ZMod 133592203)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (607, 1), (12227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (607, 1), (12227, 1)] : List FactorBlock).map factorBlockValue).prod) = 133592203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_607
      · exact prime_seventyTwoBR_12227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 133592203) ^ 66796101 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (14 : ZMod 133592203) ^ 44530734 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (14 : ZMod 133592203) ^ 220086 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (14 : ZMod 133592203) ^ 10926 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_143722157 : Nat.Prime 143722157 := by
  apply lucas_primality 143722157 (2 : ZMod 143722157)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (1117, 1), (1693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (1117, 1), (1693, 1)] : List FactorBlock).map factorBlockValue).prod) = 143722157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_19
      · exact prime_seventyTwoBR_1117
      · exact prime_seventyTwoBR_1693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 143722157) ^ 71861078 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 143722157) ^ 7564324 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 143722157) ^ 128668 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 143722157) ^ 84892 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_144820051 : Nat.Prime 144820051 := by
  apply lucas_primality 144820051 (2 : ZMod 144820051)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (965467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (965467, 1)] : List FactorBlock).map factorBlockValue).prod) = 144820051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_965467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 144820051) ^ 72410025 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 144820051) ^ 48273350 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 144820051) ^ 28964010 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 144820051) ^ 150 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_162174191 : Nat.Prime 162174191 := by
  apply lucas_primality 162174191 (7 : ZMod 162174191)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (181, 1), (89599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (181, 1), (89599, 1)] : List FactorBlock).map factorBlockValue).prod) = 162174191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_181
      · exact prime_seventyTwoBR_89599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 162174191) ^ 81087095 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 162174191) ^ 32434838 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 162174191) ^ 895990 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 162174191) ^ 1810 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_186120703 : Nat.Prime 186120703 := by
  apply lucas_primality 186120703 (6 : ZMod 186120703)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (10340039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (10340039, 1)] : List FactorBlock).map factorBlockValue).prod) = 186120703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_10340039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 186120703) ^ 93060351 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 186120703) ^ 62040234 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 186120703) ^ 18 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_187690163 : Nat.Prime 187690163 := by
  apply lucas_primality 187690163 (2 : ZMod 187690163)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (8531371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (8531371, 1)] : List FactorBlock).map factorBlockValue).prod) = 187690163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_11
      · exact prime_seventyTwoBR_8531371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 187690163) ^ 93845081 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 187690163) ^ 17062742 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 187690163) ^ 22 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_214361111 : Nat.Prime 214361111 := by
  apply lucas_primality 214361111 (37 : ZMod 214361111)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (151, 1), (141961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (151, 1), (141961, 1)] : List FactorBlock).map factorBlockValue).prod) = 214361111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_151
      · exact prime_seventyTwoBR_141961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (37 : ZMod 214361111) ^ 107180555 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (37 : ZMod 214361111) ^ 42872222 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (37 : ZMod 214361111) ^ 1419610 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (37 : ZMod 214361111) ^ 1510 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_225337051 : Nat.Prime 225337051 := by
  apply lucas_primality 225337051 (2 : ZMod 225337051)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (61, 1), (8209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (61, 1), (8209, 1)] : List FactorBlock).map factorBlockValue).prod) = 225337051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_61
      · exact prime_seventyTwoBR_8209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 225337051) ^ 112668525 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 225337051) ^ 75112350 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 225337051) ^ 45067410 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 225337051) ^ 3694050 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 225337051) ^ 27450 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_241897979 : Nat.Prime 241897979 := by
  apply lucas_primality 241897979 (2 : ZMod 241897979)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17278427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17278427, 1)] : List FactorBlock).map factorBlockValue).prod) = 241897979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_17278427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 241897979) ^ 120948989 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 241897979) ^ 34556854 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 241897979) ^ 14 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_258819923 : Nat.Prime 258819923 := by
  apply lucas_primality 258819923 (2 : ZMod 258819923)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (229, 1), (565109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (229, 1), (565109, 1)] : List FactorBlock).map factorBlockValue).prod) = 258819923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_229
      · exact prime_seventyTwoBR_565109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 258819923) ^ 129409961 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 258819923) ^ 1130218 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 258819923) ^ 458 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_276109697 : Nat.Prime 276109697 := by
  apply lucas_primality 276109697 (3 : ZMod 276109697)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (29, 1), (74383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (29, 1), (74383, 1)] : List FactorBlock).map factorBlockValue).prod) = 276109697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_29
      · exact prime_seventyTwoBR_74383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 276109697) ^ 138054848 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 276109697) ^ 9521024 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 276109697) ^ 3712 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_279144527 : Nat.Prime 279144527 := by
  apply lucas_primality 279144527 (5 : ZMod 279144527)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (139, 1), (1004117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (139, 1), (1004117, 1)] : List FactorBlock).map factorBlockValue).prod) = 279144527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_139
      · exact prime_seventyTwoBR_1004117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 279144527) ^ 139572263 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 279144527) ^ 2008234 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 279144527) ^ 278 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_288985369 : Nat.Prime 288985369 := by
  apply lucas_primality 288985369 (31 : ZMod 288985369)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (1720151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (1720151, 1)] : List FactorBlock).map factorBlockValue).prod) = 288985369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_1720151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (31 : ZMod 288985369) ^ 144492684 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (31 : ZMod 288985369) ^ 96328456 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (31 : ZMod 288985369) ^ 41283624 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (31 : ZMod 288985369) ^ 168 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_300773807 : Nat.Prime 300773807 := by
  apply lucas_primality 300773807 (5 : ZMod 300773807)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (6538561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (6538561, 1)] : List FactorBlock).map factorBlockValue).prod) = 300773807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_23
      · exact prime_seventyTwoBR_6538561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 300773807) ^ 150386903 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 300773807) ^ 13077122 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 300773807) ^ 46 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_324549103 : Nat.Prime 324549103 := by
  apply lucas_primality 324549103 (5 : ZMod 324549103)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (54091517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (54091517, 1)] : List FactorBlock).map factorBlockValue).prod) = 324549103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_54091517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 324549103) ^ 162274551 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 324549103) ^ 108183034 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 324549103) ^ 6 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_347361757 : Nat.Prime 347361757 := by
  apply lucas_primality 347361757 (5 : ZMod 347361757)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (227, 1), (18217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (227, 1), (18217, 1)] : List FactorBlock).map factorBlockValue).prod) = 347361757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_227
      · exact prime_seventyTwoBR_18217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 347361757) ^ 173680878 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 347361757) ^ 115787252 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 347361757) ^ 49623108 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 347361757) ^ 1530228 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 347361757) ^ 19068 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_351381713 : Nat.Prime 351381713 := by
  apply lucas_primality 351381713 (3 : ZMod 351381713)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (1996487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (1996487, 1)] : List FactorBlock).map factorBlockValue).prod) = 351381713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_11
      · exact prime_seventyTwoBR_1996487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 351381713) ^ 175690856 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 351381713) ^ 31943792 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 351381713) ^ 176 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_368686991 : Nat.Prime 368686991 := by
  apply lucas_primality 368686991 (7 : ZMod 368686991)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (17, 1), (491, 1), (631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (17, 1), (491, 1), (631, 1)] : List FactorBlock).map factorBlockValue).prod) = 368686991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_17
      · exact prime_seventyTwoBR_491
      · exact prime_seventyTwoBR_631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 368686991) ^ 184343495 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 368686991) ^ 73737398 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 368686991) ^ 52669570 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 368686991) ^ 21687470 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 368686991) ^ 750890 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 368686991) ^ 584290 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_369024659 : Nat.Prime 369024659 := by
  apply lucas_primality 369024659 (2 : ZMod 369024659)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12841, 1), (14369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12841, 1), (14369, 1)] : List FactorBlock).map factorBlockValue).prod) = 369024659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_12841
      · exact prime_seventyTwoBR_14369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 369024659) ^ 184512329 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 369024659) ^ 28738 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 369024659) ^ 25682 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_377181059 : Nat.Prime 377181059 := by
  apply lucas_primality 377181059 (2 : ZMod 377181059)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (193, 1), (23833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (193, 1), (23833, 1)] : List FactorBlock).map factorBlockValue).prod) = 377181059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_41
      · exact prime_seventyTwoBR_193
      · exact prime_seventyTwoBR_23833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 377181059) ^ 188590529 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 377181059) ^ 9199538 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 377181059) ^ 1954306 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 377181059) ^ 15826 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_409689829 : Nat.Prime 409689829 := by
  apply lucas_primality 409689829 (2 : ZMod 409689829)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (263, 1), (43271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (263, 1), (43271, 1)] : List FactorBlock).map factorBlockValue).prod) = 409689829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_263
      · exact prime_seventyTwoBR_43271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 409689829) ^ 204844914 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 409689829) ^ 136563276 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 409689829) ^ 1557756 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 409689829) ^ 9468 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_425097209 : Nat.Prime 425097209 := by
  apply lucas_primality 425097209 (3 : ZMod 425097209)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (347, 1), (153133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (347, 1), (153133, 1)] : List FactorBlock).map factorBlockValue).prod) = 425097209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_347
      · exact prime_seventyTwoBR_153133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 425097209) ^ 212548604 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 425097209) ^ 1225064 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 425097209) ^ 2776 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_436944407 : Nat.Prime 436944407 := by
  apply lucas_primality 436944407 (5 : ZMod 436944407)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (11498537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (11498537, 1)] : List FactorBlock).map factorBlockValue).prod) = 436944407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_19
      · exact prime_seventyTwoBR_11498537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 436944407) ^ 218472203 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 436944407) ^ 22997074 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 436944407) ^ 38 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_455502017 : Nat.Prime 455502017 := by
  apply lucas_primality 455502017 (3 : ZMod 455502017)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (179, 1), (39761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (179, 1), (39761, 1)] : List FactorBlock).map factorBlockValue).prod) = 455502017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_179
      · exact prime_seventyTwoBR_39761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 455502017) ^ 227751008 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 455502017) ^ 2544704 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 455502017) ^ 11456 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_495983533 : Nat.Prime 495983533 := by
  apply lucas_primality 495983533 (2 : ZMod 495983533)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (3757451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (3757451, 1)] : List FactorBlock).map factorBlockValue).prod) = 495983533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_11
      · exact prime_seventyTwoBR_3757451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 495983533) ^ 247991766 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 495983533) ^ 165327844 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 495983533) ^ 45089412 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 495983533) ^ 132 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_509835031 : Nat.Prime 509835031 := by
  apply lucas_primality 509835031 (3 : ZMod 509835031)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (16994501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (16994501, 1)] : List FactorBlock).map factorBlockValue).prod) = 509835031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_16994501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 509835031) ^ 254917515 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 509835031) ^ 169945010 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 509835031) ^ 101967006 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 509835031) ^ 30 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_535375567 : Nat.Prime 535375567 := by
  apply lucas_primality 535375567 (3 : ZMod 535375567)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (2703917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (2703917, 1)] : List FactorBlock).map factorBlockValue).prod) = 535375567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_11
      · exact prime_seventyTwoBR_2703917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 535375567) ^ 267687783 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 535375567) ^ 178458522 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 535375567) ^ 48670506 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 535375567) ^ 198 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_629458829 : Nat.Prime 629458829 := by
  apply lucas_primality 629458829 (2 : ZMod 629458829)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (1181, 1), (7013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (1181, 1), (7013, 1)] : List FactorBlock).map factorBlockValue).prod) = 629458829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_19
      · exact prime_seventyTwoBR_1181
      · exact prime_seventyTwoBR_7013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 629458829) ^ 314729414 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 629458829) ^ 33129412 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 629458829) ^ 532988 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 629458829) ^ 89756 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_645036629 : Nat.Prime 645036629 := by
  apply lucas_primality 645036629 (2 : ZMod 645036629)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (6547, 1), (24631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (6547, 1), (24631, 1)] : List FactorBlock).map factorBlockValue).prod) = 645036629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_6547
      · exact prime_seventyTwoBR_24631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 645036629) ^ 322518314 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 645036629) ^ 98524 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 645036629) ^ 26188 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_686125807 : Nat.Prime 686125807 := by
  apply lucas_primality 686125807 (5 : ZMod 686125807)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1163, 1), (98327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1163, 1), (98327, 1)] : List FactorBlock).map factorBlockValue).prod) = 686125807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_1163
      · exact prime_seventyTwoBR_98327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 686125807) ^ 343062903 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 686125807) ^ 228708602 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 686125807) ^ 589962 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 686125807) ^ 6978 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_758988863 : Nat.Prime 758988863 := by
  apply lucas_primality 758988863 (5 : ZMod 758988863)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (6432109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (6432109, 1)] : List FactorBlock).map factorBlockValue).prod) = 758988863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_59
      · exact prime_seventyTwoBR_6432109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 758988863) ^ 379494431 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 758988863) ^ 12864218 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 758988863) ^ 118 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_773416417 : Nat.Prime 773416417 := by
  apply lucas_primality 773416417 (5 : ZMod 773416417)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (1279, 1), (6299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (1279, 1), (6299, 1)] : List FactorBlock).map factorBlockValue).prod) = 773416417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_1279
      · exact prime_seventyTwoBR_6299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 773416417) ^ 386708208 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 773416417) ^ 257805472 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 773416417) ^ 604704 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 773416417) ^ 122784 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_825655997 : Nat.Prime 825655997 := by
  apply lucas_primality 825655997 (2 : ZMod 825655997)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (1181, 1), (15889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (1181, 1), (15889, 1)] : List FactorBlock).map factorBlockValue).prod) = 825655997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_11
      · exact prime_seventyTwoBR_1181
      · exact prime_seventyTwoBR_15889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 825655997) ^ 412827998 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 825655997) ^ 75059636 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 825655997) ^ 699116 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 825655997) ^ 51964 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_862332943 : Nat.Prime 862332943 := by
  apply lucas_primality 862332943 (3 : ZMod 862332943)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (143722157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (143722157, 1)] : List FactorBlock).map factorBlockValue).prod) = 862332943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_143722157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 862332943) ^ 431166471 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 862332943) ^ 287444314 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 862332943) ^ 6 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_866337181 : Nat.Prime 866337181 := by
  apply lucas_primality 866337181 (2 : ZMod 866337181)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (14438953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (14438953, 1)] : List FactorBlock).map factorBlockValue).prod) = 866337181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_14438953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 866337181) ^ 433168590 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 866337181) ^ 288779060 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 866337181) ^ 173267436 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 866337181) ^ 60 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_880933951 : Nat.Prime 880933951 := by
  apply lucas_primality 880933951 (6 : ZMod 880933951)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (13, 1), (150587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (13, 1), (150587, 1)] : List FactorBlock).map factorBlockValue).prod) = 880933951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_13
      · exact prime_seventyTwoBR_150587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 880933951) ^ 440466975 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 880933951) ^ 293644650 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 880933951) ^ 176186790 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 880933951) ^ 67764150 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 880933951) ^ 5850 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_1321039283 : Nat.Prime 1321039283 := by
  apply lucas_primality 1321039283 (2 : ZMod 1321039283)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (7421569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (7421569, 1)] : List FactorBlock).map factorBlockValue).prod) = 1321039283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_89
      · exact prime_seventyTwoBR_7421569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1321039283) ^ 660519641 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1321039283) ^ 14843138 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1321039283) ^ 178 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_1329891569 : Nat.Prime 1329891569 := by
  apply lucas_primality 1329891569 (3 : ZMod 1329891569)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (31, 1), (463, 1), (5791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (31, 1), (463, 1), (5791, 1)] : List FactorBlock).map factorBlockValue).prod) = 1329891569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_31
      · exact prime_seventyTwoBR_463
      · exact prime_seventyTwoBR_5791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1329891569) ^ 664945784 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1329891569) ^ 42899728 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1329891569) ^ 2872336 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1329891569) ^ 229648 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_1331147143 : Nat.Prime 1331147143 := by
  apply lucas_primality 1331147143 (5 : ZMod 1331147143)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (13, 1), (1896221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (13, 1), (1896221, 1)] : List FactorBlock).map factorBlockValue).prod) = 1331147143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_13
      · exact prime_seventyTwoBR_1896221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1331147143) ^ 665573571 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1331147143) ^ 443715714 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1331147143) ^ 102395934 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1331147143) ^ 702 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_1352022307 : Nat.Prime 1352022307 := by
  apply lucas_primality 1352022307 (3 : ZMod 1352022307)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (225337051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (225337051, 1)] : List FactorBlock).map factorBlockValue).prod) = 1352022307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_225337051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1352022307) ^ 676011153 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1352022307) ^ 450674102 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1352022307) ^ 6 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_1352707259 : Nat.Prime 1352707259 := by
  apply lucas_primality 1352707259 (2 : ZMod 1352707259)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (31, 1), (3116837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (31, 1), (3116837, 1)] : List FactorBlock).map factorBlockValue).prod) = 1352707259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_31
      · exact prime_seventyTwoBR_3116837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1352707259) ^ 676353629 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1352707259) ^ 193243894 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1352707259) ^ 43635718 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1352707259) ^ 434 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_1354667519 : Nat.Prime 1354667519 := by
  apply lucas_primality 1354667519 (7 : ZMod 1354667519)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1777, 1), (381167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1777, 1), (381167, 1)] : List FactorBlock).map factorBlockValue).prod) = 1354667519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_1777
      · exact prime_seventyTwoBR_381167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1354667519) ^ 677333759 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1354667519) ^ 762334 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1354667519) ^ 3554 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_1597465091 : Nat.Prime 1597465091 := by
  apply lucas_primality 1597465091 (2 : ZMod 1597465091)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (19, 1), (131, 1), (4937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (19, 1), (131, 1), (4937, 1)] : List FactorBlock).map factorBlockValue).prod) = 1597465091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_13
      · exact prime_seventyTwoBR_19
      · exact prime_seventyTwoBR_131
      · exact prime_seventyTwoBR_4937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1597465091) ^ 798732545 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1597465091) ^ 319493018 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1597465091) ^ 122881930 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1597465091) ^ 84077110 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1597465091) ^ 12194390 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1597465091) ^ 323570 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_1876910501 : Nat.Prime 1876910501 := by
  apply lucas_primality 1876910501 (2 : ZMod 1876910501)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 3), (17, 2), (31, 1), (419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 3), (17, 2), (31, 1), (419, 1)] : List FactorBlock).map factorBlockValue).prod) = 1876910501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_17
      · exact prime_seventyTwoBR_31
      · exact prime_seventyTwoBR_419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1876910501) ^ 938455250 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1876910501) ^ 375382100 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1876910501) ^ 110406500 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1876910501) ^ 60545500 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1876910501) ^ 4479500 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_1926863401 : Nat.Prime 1926863401 := by
  apply lucas_primality 1926863401 (23 : ZMod 1926863401)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (7, 1), (11, 1), (179, 1), (233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (7, 1), (11, 1), (179, 1), (233, 1)] : List FactorBlock).map factorBlockValue).prod) = 1926863401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_11
      · exact prime_seventyTwoBR_179
      · exact prime_seventyTwoBR_233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 1926863401) ^ 963431700 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (23 : ZMod 1926863401) ^ 642287800 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (23 : ZMod 1926863401) ^ 385372680 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (23 : ZMod 1926863401) ^ 275266200 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (23 : ZMod 1926863401) ^ 175169400 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (23 : ZMod 1926863401) ^ 10764600 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (23 : ZMod 1926863401) ^ 8269800 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_2201218853 : Nat.Prime 2201218853 := by
  apply lucas_primality 2201218853 (3 : ZMod 2201218853)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (78614959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (78614959, 1)] : List FactorBlock).map factorBlockValue).prod) = 2201218853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_78614959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2201218853) ^ 1100609426 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 2201218853) ^ 314459836 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 2201218853) ^ 28 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_2669118827 : Nat.Prime 2669118827 := by
  apply lucas_primality 2669118827 (2 : ZMod 2669118827)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (121323583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (121323583, 1)] : List FactorBlock).map factorBlockValue).prod) = 2669118827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_11
      · exact prime_seventyTwoBR_121323583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2669118827) ^ 1334559413 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2669118827) ^ 242647166 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2669118827) ^ 22 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_2886826487 : Nat.Prime 2886826487 := by
  apply lucas_primality 2886826487 (5 : ZMod 2886826487)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83, 1), (1171, 1), (14851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83, 1), (1171, 1), (14851, 1)] : List FactorBlock).map factorBlockValue).prod) = 2886826487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_83
      · exact prime_seventyTwoBR_1171
      · exact prime_seventyTwoBR_14851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2886826487) ^ 1443413243 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 2886826487) ^ 34781042 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 2886826487) ^ 2465266 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 2886826487) ^ 194386 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_3209048819 : Nat.Prime 3209048819 := by
  apply lucas_primality 3209048819 (2 : ZMod 3209048819)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (137, 1), (2693, 1), (4349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (137, 1), (2693, 1), (4349, 1)] : List FactorBlock).map factorBlockValue).prod) = 3209048819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_137
      · exact prime_seventyTwoBR_2693
      · exact prime_seventyTwoBR_4349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3209048819) ^ 1604524409 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 3209048819) ^ 23423714 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 3209048819) ^ 1191626 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 3209048819) ^ 737882 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_3467824429 : Nat.Prime 3467824429 := by
  apply lucas_primality 3467824429 (2 : ZMod 3467824429)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (288985369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (288985369, 1)] : List FactorBlock).map factorBlockValue).prod) = 3467824429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_288985369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3467824429) ^ 1733912214 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 3467824429) ^ 1155941476 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 3467824429) ^ 12 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_3854434097 : Nat.Prime 3854434097 := by
  apply lucas_primality 3854434097 (3 : ZMod 3854434097)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (181, 1), (331, 1), (4021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (181, 1), (331, 1), (4021, 1)] : List FactorBlock).map factorBlockValue).prod) = 3854434097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_181
      · exact prime_seventyTwoBR_331
      · exact prime_seventyTwoBR_4021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3854434097) ^ 1927217048 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 3854434097) ^ 21295216 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 3854434097) ^ 11644816 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 3854434097) ^ 958576 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_3865535759 : Nat.Prime 3865535759 := by
  apply lucas_primality 3865535759 (7 : ZMod 3865535759)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (276109697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (276109697, 1)] : List FactorBlock).map factorBlockValue).prod) = 3865535759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_276109697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 3865535759) ^ 1932767879 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 3865535759) ^ 552219394 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 3865535759) ^ 14 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_5213521837 : Nat.Prime 5213521837 := by
  apply lucas_primality 5213521837 (6 : ZMod 5213521837)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (144820051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (144820051, 1)] : List FactorBlock).map factorBlockValue).prod) = 5213521837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_144820051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 5213521837) ^ 2606760918 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 5213521837) ^ 1737840612 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 5213521837) ^ 36 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_5218213277 : Nat.Prime 5218213277 := by
  apply lucas_primality 5218213277 (2 : ZMod 5218213277)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (137, 1), (501173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (137, 1), (501173, 1)] : List FactorBlock).map factorBlockValue).prod) = 5218213277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_19
      · exact prime_seventyTwoBR_137
      · exact prime_seventyTwoBR_501173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5218213277) ^ 2609106638 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5218213277) ^ 274642804 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5218213277) ^ 38089148 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5218213277) ^ 10412 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_6384001733 : Nat.Prime 6384001733 := by
  apply lucas_primality 6384001733 (2 : ZMod 6384001733)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (16447, 1), (97039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (16447, 1), (97039, 1)] : List FactorBlock).map factorBlockValue).prod) = 6384001733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_16447
      · exact prime_seventyTwoBR_97039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6384001733) ^ 3192000866 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 6384001733) ^ 388156 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 6384001733) ^ 65788 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_6447546199 : Nat.Prime 6447546199 := by
  apply lucas_primality 6447546199 (3 : ZMod 6447546199)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (47, 1), (7621213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (47, 1), (7621213, 1)] : List FactorBlock).map factorBlockValue).prod) = 6447546199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_47
      · exact prime_seventyTwoBR_7621213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6447546199) ^ 3223773099 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 6447546199) ^ 2149182066 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 6447546199) ^ 137181834 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 6447546199) ^ 846 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_7444734581 : Nat.Prime 7444734581 := by
  apply lucas_primality 7444734581 (2 : ZMod 7444734581)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (223, 1), (1669223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (223, 1), (1669223, 1)] : List FactorBlock).map factorBlockValue).prod) = 7444734581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_223
      · exact prime_seventyTwoBR_1669223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7444734581) ^ 3722367290 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 7444734581) ^ 1488946916 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 7444734581) ^ 33384460 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 7444734581) ^ 4460 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_7865448131 : Nat.Prime 7865448131 := by
  apply lucas_primality 7865448131 (2 : ZMod 7865448131)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (311, 1), (617, 1), (4099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (311, 1), (617, 1), (4099, 1)] : List FactorBlock).map factorBlockValue).prod) = 7865448131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_311
      · exact prime_seventyTwoBR_617
      · exact prime_seventyTwoBR_4099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7865448131) ^ 3932724065 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 7865448131) ^ 1573089626 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 7865448131) ^ 25290830 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 7865448131) ^ 12747890 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 7865448131) ^ 1918870 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_8406056809 : Nat.Prime 8406056809 := by
  apply lucas_primality 8406056809 (7 : ZMod 8406056809)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (116750789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (116750789, 1)] : List FactorBlock).map factorBlockValue).prod) = 8406056809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_116750789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 8406056809) ^ 4203028404 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 8406056809) ^ 2802018936 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 8406056809) ^ 72 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_9056208809 : Nat.Prime 9056208809 := by
  apply lucas_primality 9056208809 (3 : ZMod 9056208809)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (1523, 1), (23977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (1523, 1), (23977, 1)] : List FactorBlock).map factorBlockValue).prod) = 9056208809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_31
      · exact prime_seventyTwoBR_1523
      · exact prime_seventyTwoBR_23977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9056208809) ^ 4528104404 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 9056208809) ^ 292135768 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 9056208809) ^ 5946296 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 9056208809) ^ 377704 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_9252373021 : Nat.Prime 9252373021 := by
  apply lucas_primality 9252373021 (2 : ZMod 9252373021)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (14018747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (14018747, 1)] : List FactorBlock).map factorBlockValue).prod) = 9252373021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_11
      · exact prime_seventyTwoBR_14018747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9252373021) ^ 4626186510 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 9252373021) ^ 3084124340 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 9252373021) ^ 1850474604 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 9252373021) ^ 841124820 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 9252373021) ^ 660 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_12069793889 : Nat.Prime 12069793889 := by
  apply lucas_primality 12069793889 (3 : ZMod 12069793889)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (377181059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (377181059, 1)] : List FactorBlock).map factorBlockValue).prod) = 12069793889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_377181059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 12069793889) ^ 6034896944 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 12069793889) ^ 32 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_12768003467 : Nat.Prime 12768003467 := by
  apply lucas_primality 12768003467 (2 : ZMod 12768003467)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6384001733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6384001733, 1)] : List FactorBlock).map factorBlockValue).prod) = 12768003467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_6384001733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 12768003467) ^ 6384001733 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 12768003467) ^ 2 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_15325729031 : Nat.Prime 15325729031 := by
  apply lucas_primality 15325729031 (7 : ZMod 15325729031)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (79, 1), (1093, 1), (17749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (79, 1), (1093, 1), (17749, 1)] : List FactorBlock).map factorBlockValue).prod) = 15325729031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_79
      · exact prime_seventyTwoBR_1093
      · exact prime_seventyTwoBR_17749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 15325729031) ^ 7662864515 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 15325729031) ^ 3065145806 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 15325729031) ^ 193996570 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 15325729031) ^ 14021710 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 15325729031) ^ 863470 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_17095984189 : Nat.Prime 17095984189 := by
  apply lucas_primality 17095984189 (10 : ZMod 17095984189)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (139, 1), (10249391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (139, 1), (10249391, 1)] : List FactorBlock).map factorBlockValue).prod) = 17095984189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_139
      · exact prime_seventyTwoBR_10249391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 17095984189) ^ 8547992094 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (10 : ZMod 17095984189) ^ 5698661396 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (10 : ZMod 17095984189) ^ 122992692 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (10 : ZMod 17095984189) ^ 1668 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_22971825017 : Nat.Prime 22971825017 := by
  apply lucas_primality 22971825017 (3 : ZMod 22971825017)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (241, 1), (1702121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (241, 1), (1702121, 1)] : List FactorBlock).map factorBlockValue).prod) = 22971825017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_241
      · exact prime_seventyTwoBR_1702121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 22971825017) ^ 11485912508 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 22971825017) ^ 3281689288 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 22971825017) ^ 95318776 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 22971825017) ^ 13496 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_26380067683 : Nat.Prime 26380067683 := by
  apply lucas_primality 26380067683 (2 : ZMod 26380067683)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31667, 1), (138841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31667, 1), (138841, 1)] : List FactorBlock).map factorBlockValue).prod) = 26380067683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_31667
      · exact prime_seventyTwoBR_138841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 26380067683) ^ 13190033841 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 26380067683) ^ 8793355894 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 26380067683) ^ 833046 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 26380067683) ^ 190002 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_28838330863 : Nat.Prime 28838330863 := by
  apply lucas_primality 28838330863 (5 : ZMod 28838330863)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (436944407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (436944407, 1)] : List FactorBlock).map factorBlockValue).prod) = 28838330863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_11
      · exact prime_seventyTwoBR_436944407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 28838330863) ^ 14419165431 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 28838330863) ^ 9612776954 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 28838330863) ^ 2621666442 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 28838330863) ^ 66 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_28957446827 : Nat.Prime 28957446827 := by
  apply lucas_primality 28957446827 (2 : ZMod 28957446827)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (37, 1), (5082037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (37, 1), (5082037, 1)] : List FactorBlock).map factorBlockValue).prod) = 28957446827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_11
      · exact prime_seventyTwoBR_37
      · exact prime_seventyTwoBR_5082037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 28957446827) ^ 14478723413 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 28957446827) ^ 4136778118 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 28957446827) ^ 2632495166 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 28957446827) ^ 782633698 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 28957446827) ^ 5698 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_30296320787 : Nat.Prime 30296320787 := by
  apply lucas_primality 30296320787 (2 : ZMod 30296320787)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (151, 1), (100318943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (151, 1), (100318943, 1)] : List FactorBlock).map factorBlockValue).prod) = 30296320787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_151
      · exact prime_seventyTwoBR_100318943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30296320787) ^ 15148160393 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 30296320787) ^ 200637886 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 30296320787) ^ 302 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_32073918229 : Nat.Prime 32073918229 := by
  apply lucas_primality 32073918229 (2 : ZMod 32073918229)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (80994743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (80994743, 1)] : List FactorBlock).map factorBlockValue).prod) = 32073918229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_11
      · exact prime_seventyTwoBR_80994743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32073918229) ^ 16036959114 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 32073918229) ^ 10691306076 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 32073918229) ^ 2915810748 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 32073918229) ^ 396 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_32612785729 : Nat.Prime 32612785729 := by
  apply lucas_primality 32612785729 (11 : ZMod 32612785729)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (631, 1), (269189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (631, 1), (269189, 1)] : List FactorBlock).map factorBlockValue).prod) = 32612785729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_631
      · exact prime_seventyTwoBR_269189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 32612785729) ^ 16306392864 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (11 : ZMod 32612785729) ^ 10870928576 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (11 : ZMod 32612785729) ^ 51684288 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (11 : ZMod 32612785729) ^ 121152 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_33624227237 : Nat.Prime 33624227237 := by
  apply lucas_primality 33624227237 (2 : ZMod 33624227237)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (8406056809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (8406056809, 1)] : List FactorBlock).map factorBlockValue).prod) = 33624227237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_8406056809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 33624227237) ^ 16812113618 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 33624227237) ^ 4 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_36371981119 : Nat.Prime 36371981119 := by
  apply lucas_primality 36371981119 (3 : ZMod 36371981119)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (43, 1), (12816061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (43, 1), (12816061, 1)] : List FactorBlock).map factorBlockValue).prod) = 36371981119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_11
      · exact prime_seventyTwoBR_43
      · exact prime_seventyTwoBR_12816061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 36371981119) ^ 18185990559 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 36371981119) ^ 12123993706 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 36371981119) ^ 3306543738 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 36371981119) ^ 845860026 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 36371981119) ^ 2838 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_36453496813 : Nat.Prime 36453496813 := by
  apply lucas_primality 36453496813 (5 : ZMod 36453496813)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (31, 1), (619, 1), (6883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (31, 1), (619, 1), (6883, 1)] : List FactorBlock).map factorBlockValue).prod) = 36453496813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_23
      · exact prime_seventyTwoBR_31
      · exact prime_seventyTwoBR_619
      · exact prime_seventyTwoBR_6883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 36453496813) ^ 18226748406 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 36453496813) ^ 12151165604 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 36453496813) ^ 1584934644 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 36453496813) ^ 1175919252 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 36453496813) ^ 58890948 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 36453496813) ^ 5296164 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_41563403633 : Nat.Prime 41563403633 := by
  apply lucas_primality 41563403633 (3 : ZMod 41563403633)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (17, 1), (41, 1), (3726991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (17, 1), (41, 1), (3726991, 1)] : List FactorBlock).map factorBlockValue).prod) = 41563403633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_17
      · exact prime_seventyTwoBR_41
      · exact prime_seventyTwoBR_3726991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 41563403633) ^ 20781701816 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 41563403633) ^ 2444906096 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 41563403633) ^ 1013741552 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 41563403633) ^ 11152 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_42866374921 : Nat.Prime 42866374921 := by
  apply lucas_primality 42866374921 (14 : ZMod 42866374921)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (43, 1), (8307437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (43, 1), (8307437, 1)] : List FactorBlock).map factorBlockValue).prod) = 42866374921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_43
      · exact prime_seventyTwoBR_8307437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 42866374921) ^ 21433187460 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (14 : ZMod 42866374921) ^ 14288791640 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (14 : ZMod 42866374921) ^ 8573274984 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (14 : ZMod 42866374921) ^ 996892440 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (14 : ZMod 42866374921) ^ 5160 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_50423032727 : Nat.Prime 50423032727 := by
  apply lucas_primality 50423032727 (5 : ZMod 50423032727)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (67, 1), (199, 1), (397, 1), (433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (67, 1), (199, 1), (397, 1), (433, 1)] : List FactorBlock).map factorBlockValue).prod) = 50423032727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_11
      · exact prime_seventyTwoBR_67
      · exact prime_seventyTwoBR_199
      · exact prime_seventyTwoBR_397
      · exact prime_seventyTwoBR_433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 50423032727) ^ 25211516363 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 50423032727) ^ 4583912066 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 50423032727) ^ 752582578 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 50423032727) ^ 253382074 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 50423032727) ^ 127010158 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 50423032727) ^ 116450422 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_54368616979 : Nat.Prime 54368616979 := by
  apply lucas_primality 54368616979 (3 : ZMod 54368616979)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (2707, 1), (85831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (2707, 1), (85831, 1)] : List FactorBlock).map factorBlockValue).prod) = 54368616979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_13
      · exact prime_seventyTwoBR_2707
      · exact prime_seventyTwoBR_85831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 54368616979) ^ 27184308489 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 54368616979) ^ 18122872326 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 54368616979) ^ 4182201306 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 54368616979) ^ 20084454 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 54368616979) ^ 633438 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_56896035799 : Nat.Prime 56896035799 := by
  apply lucas_primality 56896035799 (3 : ZMod 56896035799)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (1354667519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (1354667519, 1)] : List FactorBlock).map factorBlockValue).prod) = 56896035799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_1354667519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 56896035799) ^ 28448017899 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 56896035799) ^ 18965345266 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 56896035799) ^ 8128005114 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 56896035799) ^ 42 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_66160195903 : Nat.Prime 66160195903 := by
  apply lucas_primality 66160195903 (3 : ZMod 66160195903)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (83, 1), (4920437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (83, 1), (4920437, 1)] : List FactorBlock).map factorBlockValue).prod) = 66160195903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_83
      · exact prime_seventyTwoBR_4920437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 66160195903) ^ 33080097951 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 66160195903) ^ 22053398634 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 66160195903) ^ 797110794 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 66160195903) ^ 13446 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_84135581429 : Nat.Prime 84135581429 := by
  apply lucas_primality 84135581429 (2 : ZMod 84135581429)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (233, 1), (1019, 1), (88591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (233, 1), (1019, 1), (88591, 1)] : List FactorBlock).map factorBlockValue).prod) = 84135581429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_233
      · exact prime_seventyTwoBR_1019
      · exact prime_seventyTwoBR_88591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 84135581429) ^ 42067790714 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 84135581429) ^ 361096916 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 84135581429) ^ 82566812 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 84135581429) ^ 949708 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_91903246489 : Nat.Prime 91903246489 := by
  apply lucas_primality 91903246489 (7 : ZMod 91903246489)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (149, 1), (2855557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (149, 1), (2855557, 1)] : List FactorBlock).map factorBlockValue).prod) = 91903246489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_149
      · exact prime_seventyTwoBR_2855557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 91903246489) ^ 45951623244 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 91903246489) ^ 30634415496 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 91903246489) ^ 616800312 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 91903246489) ^ 32184 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_93431848567 : Nat.Prime 93431848567 := by
  apply lucas_primality 93431848567 (6 : ZMod 93431848567)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (19, 1), (117082517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (19, 1), (117082517, 1)] : List FactorBlock).map factorBlockValue).prod) = 93431848567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_19
      · exact prime_seventyTwoBR_117082517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 93431848567) ^ 46715924283 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 93431848567) ^ 31143949522 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 93431848567) ^ 13347406938 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 93431848567) ^ 4917465714 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 93431848567) ^ 798 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_97728416413 : Nat.Prime 97728416413 := by
  apply lucas_primality 97728416413 (2 : ZMod 97728416413)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (239, 1), (3097769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (239, 1), (3097769, 1)] : List FactorBlock).map factorBlockValue).prod) = 97728416413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_11
      · exact prime_seventyTwoBR_239
      · exact prime_seventyTwoBR_3097769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 97728416413) ^ 48864208206 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 97728416413) ^ 32576138804 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 97728416413) ^ 8884401492 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 97728416413) ^ 408905508 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 97728416413) ^ 31548 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_116346787969 : Nat.Prime 116346787969 := by
  apply lucas_primality 116346787969 (14 : ZMod 116346787969)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (17, 1), (73, 1), (244147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (17, 1), (73, 1), (244147, 1)] : List FactorBlock).map factorBlockValue).prod) = 116346787969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_17
      · exact prime_seventyTwoBR_73
      · exact prime_seventyTwoBR_244147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 116346787969) ^ 58173393984 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (14 : ZMod 116346787969) ^ 38782262656 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (14 : ZMod 116346787969) ^ 6843928704 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (14 : ZMod 116346787969) ^ 1593791616 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (14 : ZMod 116346787969) ^ 476544 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_183682749779 : Nat.Prime 183682749779 := by
  apply lucas_primality 183682749779 (2 : ZMod 183682749779)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (17, 1), (109, 1), (4505783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (17, 1), (109, 1), (4505783, 1)] : List FactorBlock).map factorBlockValue).prod) = 183682749779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_11
      · exact prime_seventyTwoBR_17
      · exact prime_seventyTwoBR_109
      · exact prime_seventyTwoBR_4505783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 183682749779) ^ 91841374889 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 183682749779) ^ 16698431798 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 183682749779) ^ 10804867634 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 183682749779) ^ 1685162842 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 183682749779) ^ 40766 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_194613870523 : Nat.Prime 194613870523 := by
  apply lucas_primality 194613870523 (3 : ZMod 194613870523)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (263, 1), (733, 1), (168253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (263, 1), (733, 1), (168253, 1)] : List FactorBlock).map factorBlockValue).prod) = 194613870523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_263
      · exact prime_seventyTwoBR_733
      · exact prime_seventyTwoBR_168253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 194613870523) ^ 97306935261 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 194613870523) ^ 64871290174 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 194613870523) ^ 739976694 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 194613870523) ^ 265503234 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 194613870523) ^ 1156674 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_196484010223 : Nat.Prime 196484010223 := by
  apply lucas_primality 196484010223 (6 : ZMod 196484010223)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (337, 1), (97173101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (337, 1), (97173101, 1)] : List FactorBlock).map factorBlockValue).prod) = 196484010223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_337
      · exact prime_seventyTwoBR_97173101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 196484010223) ^ 98242005111 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 196484010223) ^ 65494670074 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 196484010223) ^ 583038606 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 196484010223) ^ 2022 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_235012169101 : Nat.Prime 235012169101 := by
  apply lucas_primality 235012169101 (6 : ZMod 235012169101)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (29, 1), (27012893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (29, 1), (27012893, 1)] : List FactorBlock).map factorBlockValue).prod) = 235012169101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_29
      · exact prime_seventyTwoBR_27012893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 235012169101) ^ 117506084550 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 235012169101) ^ 78337389700 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 235012169101) ^ 47002433820 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 235012169101) ^ 8103867900 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 235012169101) ^ 8700 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_254085392293 : Nat.Prime 254085392293 := by
  apply lucas_primality 254085392293 (5 : ZMod 254085392293)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (191, 1), (211, 1), (525391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (191, 1), (211, 1), (525391, 1)] : List FactorBlock).map factorBlockValue).prod) = 254085392293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_191
      · exact prime_seventyTwoBR_211
      · exact prime_seventyTwoBR_525391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 254085392293) ^ 127042696146 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 254085392293) ^ 84695130764 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 254085392293) ^ 1330290012 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 254085392293) ^ 1204196172 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 254085392293) ^ 483612 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_257142995393 : Nat.Prime 257142995393 := by
  apply lucas_primality 257142995393 (3 : ZMod 257142995393)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (1511, 1), (2659073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (1511, 1), (2659073, 1)] : List FactorBlock).map factorBlockValue).prod) = 257142995393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_1511
      · exact prime_seventyTwoBR_2659073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 257142995393) ^ 128571497696 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 257142995393) ^ 170180672 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 257142995393) ^ 96704 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_286396685797 : Nat.Prime 286396685797 := by
  apply lucas_primality 286396685797 (2 : ZMod 286396685797)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (61, 1), (919, 1), (32749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (61, 1), (919, 1), (32749, 1)] : List FactorBlock).map factorBlockValue).prod) = 286396685797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_13
      · exact prime_seventyTwoBR_61
      · exact prime_seventyTwoBR_919
      · exact prime_seventyTwoBR_32749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 286396685797) ^ 143198342898 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 286396685797) ^ 95465561932 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 286396685797) ^ 22030514292 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 286396685797) ^ 4695027636 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 286396685797) ^ 311639484 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 286396685797) ^ 8745204 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_335540433331 : Nat.Prime 335540433331 := by
  apply lucas_primality 335540433331 (2 : ZMod 335540433331)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (29, 1), (103, 1), (1248151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (29, 1), (103, 1), (1248151, 1)] : List FactorBlock).map factorBlockValue).prod) = 335540433331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_29
      · exact prime_seventyTwoBR_103
      · exact prime_seventyTwoBR_1248151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 335540433331) ^ 167770216665 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 335540433331) ^ 111846811110 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 335540433331) ^ 67108086666 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 335540433331) ^ 11570359770 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 335540433331) ^ 3257674110 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 335540433331) ^ 268830 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_338387384323 : Nat.Prime 338387384323 := by
  apply lucas_primality 338387384323 (2 : ZMod 338387384323)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (13, 1), (43, 1), (11210077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (13, 1), (43, 1), (11210077, 1)] : List FactorBlock).map factorBlockValue).prod) = 338387384323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_13
      · exact prime_seventyTwoBR_43
      · exact prime_seventyTwoBR_11210077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 338387384323) ^ 169193692161 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 338387384323) ^ 112795794774 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 338387384323) ^ 26029798794 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 338387384323) ^ 7869474054 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 338387384323) ^ 30186 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_384295435879 : Nat.Prime 384295435879 := by
  apply lucas_primality 384295435879 (6 : ZMod 384295435879)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (127, 1), (4691, 1), (107509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (127, 1), (4691, 1), (107509, 1)] : List FactorBlock).map factorBlockValue).prod) = 384295435879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_127
      · exact prime_seventyTwoBR_4691
      · exact prime_seventyTwoBR_107509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 384295435879) ^ 192147717939 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 384295435879) ^ 128098478626 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 384295435879) ^ 3025948314 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 384295435879) ^ 81921858 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 384295435879) ^ 3574542 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_390586677059 : Nat.Prime 390586677059 := by
  apply lucas_primality 390586677059 (2 : ZMod 390586677059)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (113, 1), (269, 1), (6424757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (113, 1), (269, 1), (6424757, 1)] : List FactorBlock).map factorBlockValue).prod) = 390586677059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_113
      · exact prime_seventyTwoBR_269
      · exact prime_seventyTwoBR_6424757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 390586677059) ^ 195293338529 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 390586677059) ^ 3456519266 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 390586677059) ^ 1451995082 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 390586677059) ^ 60794 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_428806784507 : Nat.Prime 428806784507 := by
  apply lucas_primality 428806784507 (2 : ZMod 428806784507)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1571, 1), (2591, 1), (52673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1571, 1), (2591, 1), (52673, 1)] : List FactorBlock).map factorBlockValue).prod) = 428806784507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_1571
      · exact prime_seventyTwoBR_2591
      · exact prime_seventyTwoBR_52673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 428806784507) ^ 214403392253 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 428806784507) ^ 272951486 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 428806784507) ^ 165498566 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 428806784507) ^ 8140922 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_468634028243 : Nat.Prime 468634028243 := by
  apply lucas_primality 468634028243 (2 : ZMod 468634028243)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (307, 1), (13313, 1), (57331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (307, 1), (13313, 1), (57331, 1)] : List FactorBlock).map factorBlockValue).prod) = 468634028243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_307
      · exact prime_seventyTwoBR_13313
      · exact prime_seventyTwoBR_57331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 468634028243) ^ 234317014121 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 468634028243) ^ 1526495206 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 468634028243) ^ 35201234 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 468634028243) ^ 8174182 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_472738310459 : Nat.Prime 472738310459 := by
  apply lucas_primality 472738310459 (2 : ZMod 472738310459)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (38867, 1), (196177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (38867, 1), (196177, 1)] : List FactorBlock).map factorBlockValue).prod) = 472738310459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_31
      · exact prime_seventyTwoBR_38867
      · exact prime_seventyTwoBR_196177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 472738310459) ^ 236369155229 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 472738310459) ^ 15249622918 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 472738310459) ^ 12162974 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 472738310459) ^ 2409754 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_498362156783 : Nat.Prime 498362156783 := by
  apply lucas_primality 498362156783 (7 : ZMod 498362156783)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (29, 1), (67, 1), (18320791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (29, 1), (67, 1), (18320791, 1)] : List FactorBlock).map factorBlockValue).prod) = 498362156783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_29
      · exact prime_seventyTwoBR_67
      · exact prime_seventyTwoBR_18320791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 498362156783) ^ 249181078391 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 498362156783) ^ 71194593826 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 498362156783) ^ 17184901958 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 498362156783) ^ 7438241146 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 498362156783) ^ 27202 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_568960357991 : Nat.Prime 568960357991 := by
  apply lucas_primality 568960357991 (7 : ZMod 568960357991)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (56896035799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (56896035799, 1)] : List FactorBlock).map factorBlockValue).prod) = 568960357991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_56896035799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 568960357991) ^ 284480178995 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 568960357991) ^ 113792071598 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 568960357991) ^ 10 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_705995944763 : Nat.Prime 705995944763 := by
  apply lucas_primality 705995944763 (2 : ZMod 705995944763)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (233, 1), (347, 1), (4366031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (233, 1), (347, 1), (4366031, 1)] : List FactorBlock).map factorBlockValue).prod) = 705995944763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_233
      · exact prime_seventyTwoBR_347
      · exact prime_seventyTwoBR_4366031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 705995944763) ^ 352997972381 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 705995944763) ^ 3030025514 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 705995944763) ^ 2034570446 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 705995944763) ^ 161702 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_766303515253 : Nat.Prime 766303515253 := by
  apply lucas_primality 766303515253 (5 : ZMod 766303515253)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (11, 1), (645036629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (11, 1), (645036629, 1)] : List FactorBlock).map factorBlockValue).prod) = 766303515253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_11
      · exact prime_seventyTwoBR_645036629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 766303515253) ^ 383151757626 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 766303515253) ^ 255434505084 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 766303515253) ^ 69663955932 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 766303515253) ^ 1188 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_1198181055347 : Nat.Prime 1198181055347 := by
  apply lucas_primality 1198181055347 (2 : ZMod 1198181055347)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (1493, 1), (36478751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (1493, 1), (36478751, 1)] : List FactorBlock).map factorBlockValue).prod) = 1198181055347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_11
      · exact prime_seventyTwoBR_1493
      · exact prime_seventyTwoBR_36478751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1198181055347) ^ 599090527673 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1198181055347) ^ 108925550486 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1198181055347) ^ 802532522 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1198181055347) ^ 32846 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_1271782981709 : Nat.Prime 1271782981709 := by
  apply lucas_primality 1271782981709 (2 : ZMod 1271782981709)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (367, 1), (866337181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (367, 1), (866337181, 1)] : List FactorBlock).map factorBlockValue).prod) = 1271782981709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_367
      · exact prime_seventyTwoBR_866337181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1271782981709) ^ 635891490854 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1271782981709) ^ 3465348724 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1271782981709) ^ 1468 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_1436062671877 : Nat.Prime 1436062671877 := by
  apply lucas_primality 1436062671877 (2 : ZMod 1436062671877)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (17095984189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (17095984189, 1)] : List FactorBlock).map factorBlockValue).prod) = 1436062671877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_17095984189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1436062671877) ^ 718031335938 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1436062671877) ^ 478687557292 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1436062671877) ^ 205151810268 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1436062671877) ^ 84 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_1600481967397 : Nat.Prime 1600481967397 := by
  apply lucas_primality 1600481967397 (5 : ZMod 1600481967397)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (173, 1), (2713, 1), (21859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (173, 1), (2713, 1), (21859, 1)] : List FactorBlock).map factorBlockValue).prod) = 1600481967397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_13
      · exact prime_seventyTwoBR_173
      · exact prime_seventyTwoBR_2713
      · exact prime_seventyTwoBR_21859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1600481967397) ^ 800240983698 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1600481967397) ^ 533493989132 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1600481967397) ^ 123113997492 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1600481967397) ^ 9251340852 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1600481967397) ^ 589930692 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1600481967397) ^ 73218444 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_2258680852507 : Nat.Prime 2258680852507 := by
  apply lucas_primality 2258680852507 (2 : ZMod 2258680852507)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (28957446827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (28957446827, 1)] : List FactorBlock).map factorBlockValue).prod) = 2258680852507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_13
      · exact prime_seventyTwoBR_28957446827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2258680852507) ^ 1129340426253 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2258680852507) ^ 752893617502 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2258680852507) ^ 173744680962 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2258680852507) ^ 78 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_2398473531371 : Nat.Prime 2398473531371 := by
  apply lucas_primality 2398473531371 (6 : ZMod 2398473531371)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (103, 1), (2663, 1), (124919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (103, 1), (2663, 1), (124919, 1)] : List FactorBlock).map factorBlockValue).prod) = 2398473531371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_103
      · exact prime_seventyTwoBR_2663
      · exact prime_seventyTwoBR_124919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2398473531371) ^ 1199236765685 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 2398473531371) ^ 479694706274 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 2398473531371) ^ 342639075910 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 2398473531371) ^ 23286150790 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 2398473531371) ^ 900665990 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 2398473531371) ^ 19200230 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_2489405028797 : Nat.Prime 2489405028797 := by
  apply lucas_primality 2489405028797 (2 : ZMod 2489405028797)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (23, 1), (3865535759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (23, 1), (3865535759, 1)] : List FactorBlock).map factorBlockValue).prod) = 2489405028797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_23
      · exact prime_seventyTwoBR_3865535759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2489405028797) ^ 1244702514398 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2489405028797) ^ 355629289828 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2489405028797) ^ 108235001252 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2489405028797) ^ 644 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_2898499391071 : Nat.Prime 2898499391071 := by
  apply lucas_primality 2898499391071 (11 : ZMod 2898499391071)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (47, 1), (108193333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (47, 1), (108193333, 1)] : List FactorBlock).map factorBlockValue).prod) = 2898499391071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_19
      · exact prime_seventyTwoBR_47
      · exact prime_seventyTwoBR_108193333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2898499391071) ^ 1449249695535 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (11 : ZMod 2898499391071) ^ 966166463690 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (11 : ZMod 2898499391071) ^ 579699878214 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (11 : ZMod 2898499391071) ^ 152552599530 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (11 : ZMod 2898499391071) ^ 61670199810 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (11 : ZMod 2898499391071) ^ 26790 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_4235270203739 : Nat.Prime 4235270203739 := by
  apply lucas_primality 4235270203739 (2 : ZMod 4235270203739)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1109, 1), (13217, 1), (20639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1109, 1), (13217, 1), (20639, 1)] : List FactorBlock).map factorBlockValue).prod) = 4235270203739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_1109
      · exact prime_seventyTwoBR_13217
      · exact prime_seventyTwoBR_20639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4235270203739) ^ 2117635101869 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 4235270203739) ^ 605038600534 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 4235270203739) ^ 3818999282 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 4235270203739) ^ 320441114 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 4235270203739) ^ 205207142 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_5198239012037 : Nat.Prime 5198239012037 := by
  apply lucas_primality 5198239012037 (2 : ZMod 5198239012037)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (1151, 1), (8369, 1), (19273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (1151, 1), (8369, 1), (19273, 1)] : List FactorBlock).map factorBlockValue).prod) = 5198239012037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_1151
      · exact prime_seventyTwoBR_8369
      · exact prime_seventyTwoBR_19273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5198239012037) ^ 2599119506018 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5198239012037) ^ 742605573148 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5198239012037) ^ 4516280636 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5198239012037) ^ 621130244 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5198239012037) ^ 269716132 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_5823777031781 : Nat.Prime 5823777031781 := by
  apply lucas_primality 5823777031781 (2 : ZMod 5823777031781)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (15325729031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (15325729031, 1)] : List FactorBlock).map factorBlockValue).prod) = 5823777031781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_19
      · exact prime_seventyTwoBR_15325729031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5823777031781) ^ 2911888515890 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5823777031781) ^ 1164755406356 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5823777031781) ^ 306514580620 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5823777031781) ^ 380 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_5835942767267 : Nat.Prime 5835942767267 := by
  apply lucas_primality 5835942767267 (2 : ZMod 5835942767267)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (8969, 1), (5333437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (8969, 1), (5333437, 1)] : List FactorBlock).map factorBlockValue).prod) = 5835942767267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_61
      · exact prime_seventyTwoBR_8969
      · exact prime_seventyTwoBR_5333437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5835942767267) ^ 2917971383633 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5835942767267) ^ 95671192906 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5835942767267) ^ 650679314 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5835942767267) ^ 1094218 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_7232809240883 : Nat.Prime 7232809240883 := by
  apply lucas_primality 7232809240883 (2 : ZMod 7232809240883)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (101, 1), (4993, 1), (7171237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (101, 1), (4993, 1), (7171237, 1)] : List FactorBlock).map factorBlockValue).prod) = 7232809240883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_101
      · exact prime_seventyTwoBR_4993
      · exact prime_seventyTwoBR_7171237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7232809240883) ^ 3616404620441 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 7232809240883) ^ 71611972682 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 7232809240883) ^ 1448589874 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 7232809240883) ^ 1008586 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_8206168525403 : Nat.Prime 8206168525403 := by
  apply lucas_primality 8206168525403 (2 : ZMod 8206168525403)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11677, 1), (351381713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11677, 1), (351381713, 1)] : List FactorBlock).map factorBlockValue).prod) = 8206168525403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_11677
      · exact prime_seventyTwoBR_351381713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 8206168525403) ^ 4103084262701 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 8206168525403) ^ 702763426 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 8206168525403) ^ 23354 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_11812908052481 : Nat.Prime 11812908052481 := by
  apply lucas_primality 11812908052481 (3 : ZMod 11812908052481)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 12), (5, 1), (31, 1), (619, 1), (30059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 12), (5, 1), (31, 1), (619, 1), (30059, 1)] : List FactorBlock).map factorBlockValue).prod) = 11812908052481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_31
      · exact prime_seventyTwoBR_619
      · exact prime_seventyTwoBR_30059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11812908052481) ^ 5906454026240 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 11812908052481) ^ 2362581610496 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 11812908052481) ^ 381061550080 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 11812908052481) ^ 19083857920 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 11812908052481) ^ 392990720 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_12866516760341 : Nat.Prime 12866516760341 := by
  apply lucas_primality 12866516760341 (2 : ZMod 12866516760341)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (59, 1), (113, 1), (6737, 1), (14323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (59, 1), (113, 1), (6737, 1), (14323, 1)] : List FactorBlock).map factorBlockValue).prod) = 12866516760341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_59
      · exact prime_seventyTwoBR_113
      · exact prime_seventyTwoBR_6737
      · exact prime_seventyTwoBR_14323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12866516760341) ^ 6433258380170 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 12866516760341) ^ 2573303352068 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 12866516760341) ^ 218076555260 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 12866516760341) ^ 113862980180 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 12866516760341) ^ 1909828820 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 12866516760341) ^ 898311580 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_15534460026461 : Nat.Prime 15534460026461 := by
  apply lucas_primality 15534460026461 (2 : ZMod 15534460026461)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (129707, 1), (5988289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (129707, 1), (5988289, 1)] : List FactorBlock).map factorBlockValue).prod) = 15534460026461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_129707
      · exact prime_seventyTwoBR_5988289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15534460026461) ^ 7767230013230 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 15534460026461) ^ 3106892005292 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 15534460026461) ^ 119765780 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 15534460026461) ^ 2594140 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_17514493277783 : Nat.Prime 17514493277783 := by
  apply lucas_primality 17514493277783 (5 : ZMod 17514493277783)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (10867, 1), (25995383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (10867, 1), (25995383, 1)] : List FactorBlock).map factorBlockValue).prod) = 17514493277783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_31
      · exact prime_seventyTwoBR_10867
      · exact prime_seventyTwoBR_25995383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 17514493277783) ^ 8757246638891 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 17514493277783) ^ 564983654122 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 17514493277783) ^ 1611713746 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 17514493277783) ^ 673754 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_21995128891363 : Nat.Prime 21995128891363 := by
  apply lucas_primality 21995128891363 (5 : ZMod 21995128891363)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 2), (30296320787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 2), (30296320787, 1)] : List FactorBlock).map factorBlockValue).prod) = 21995128891363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_11
      · exact prime_seventyTwoBR_30296320787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 21995128891363) ^ 10997564445681 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 21995128891363) ^ 7331709630454 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 21995128891363) ^ 1999557171942 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 21995128891363) ^ 726 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_22323809801603 : Nat.Prime 22323809801603 := by
  apply lucas_primality 22323809801603 (2 : ZMod 22323809801603)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (179, 1), (241963, 1), (257713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (179, 1), (241963, 1), (257713, 1)] : List FactorBlock).map factorBlockValue).prod) = 22323809801603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_179
      · exact prime_seventyTwoBR_241963
      · exact prime_seventyTwoBR_257713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 22323809801603) ^ 11161904900801 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 22323809801603) ^ 124714021238 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 22323809801603) ^ 92261254 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 22323809801603) ^ 86622754 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_23625816104963 : Nat.Prime 23625816104963 := by
  apply lucas_primality 23625816104963 (2 : ZMod 23625816104963)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11812908052481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11812908052481, 1)] : List FactorBlock).map factorBlockValue).prod) = 23625816104963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_11812908052481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 23625816104963) ^ 11812908052481 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 23625816104963) ^ 2 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_25191008205553 : Nat.Prime 25191008205553 := by
  apply lucas_primality 25191008205553 (5 : ZMod 25191008205553)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (61, 1), (409689829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (61, 1), (409689829, 1)] : List FactorBlock).map factorBlockValue).prod) = 25191008205553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_61
      · exact prime_seventyTwoBR_409689829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 25191008205553) ^ 12595504102776 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 25191008205553) ^ 8397002735184 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 25191008205553) ^ 3598715457936 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 25191008205553) ^ 412967347632 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 25191008205553) ^ 61488 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_25472100263881 : Nat.Prime 25472100263881 := by
  apply lucas_primality 25472100263881 (7 : ZMod 25472100263881)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (157, 1), (1352022307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (157, 1), (1352022307, 1)] : List FactorBlock).map factorBlockValue).prod) = 25472100263881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_157
      · exact prime_seventyTwoBR_1352022307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 25472100263881) ^ 12736050131940 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 25472100263881) ^ 8490700087960 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 25472100263881) ^ 5094420052776 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 25472100263881) ^ 162242676840 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 25472100263881) ^ 18840 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_34291061048723 : Nat.Prime 34291061048723 := by
  apply lucas_primality 34291061048723 (2 : ZMod 34291061048723)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (409, 1), (541, 1), (77487269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (409, 1), (541, 1), (77487269, 1)] : List FactorBlock).map factorBlockValue).prod) = 34291061048723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_409
      · exact prime_seventyTwoBR_541
      · exact prime_seventyTwoBR_77487269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 34291061048723) ^ 17145530524361 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 34291061048723) ^ 83841225058 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 34291061048723) ^ 63384586042 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 34291061048723) ^ 442538 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_34465504125049 : Nat.Prime 34465504125049 := by
  apply lucas_primality 34465504125049 (11 : ZMod 34465504125049)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1436062671877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1436062671877, 1)] : List FactorBlock).map factorBlockValue).prod) = 34465504125049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_1436062671877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 34465504125049) ^ 17232752062524 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (11 : ZMod 34465504125049) ^ 11488501375016 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (11 : ZMod 34465504125049) ^ 24 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_54782252335133 : Nat.Prime 54782252335133 := by
  apply lucas_primality 54782252335133 (2 : ZMod 54782252335133)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (61, 1), (32073918229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (61, 1), (32073918229, 1)] : List FactorBlock).map factorBlockValue).prod) = 54782252335133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_61
      · exact prime_seventyTwoBR_32073918229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 54782252335133) ^ 27391126167566 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 54782252335133) ^ 7826036047876 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 54782252335133) ^ 898069710412 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 54782252335133) ^ 1708 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_55958451195197 : Nat.Prime 55958451195197 := by
  apply lucas_primality 55958451195197 (2 : ZMod 55958451195197)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (1271782981709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (1271782981709, 1)] : List FactorBlock).map factorBlockValue).prod) = 55958451195197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_11
      · exact prime_seventyTwoBR_1271782981709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 55958451195197) ^ 27979225597598 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 55958451195197) ^ 5087131926836 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 55958451195197) ^ 44 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_62227215969521 : Nat.Prime 62227215969521 := by
  apply lucas_primality 62227215969521 (3 : ZMod 62227215969521)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (7, 1), (5807, 1), (19135531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (7, 1), (5807, 1), (19135531, 1)] : List FactorBlock).map factorBlockValue).prod) = 62227215969521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_5807
      · exact prime_seventyTwoBR_19135531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 62227215969521) ^ 31113607984760 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 62227215969521) ^ 12445443193904 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 62227215969521) ^ 8889602281360 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 62227215969521) ^ 10715897360 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 62227215969521) ^ 3251920 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_82161502361167 : Nat.Prime 82161502361167 := by
  apply lucas_primality 82161502361167 (3 : ZMod 82161502361167)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (149, 1), (91903246489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (149, 1), (91903246489, 1)] : List FactorBlock).map factorBlockValue).prod) = 82161502361167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_149
      · exact prime_seventyTwoBR_91903246489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 82161502361167) ^ 41080751180583 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 82161502361167) ^ 27387167453722 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 82161502361167) ^ 551419478934 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 82161502361167) ^ 894 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_83305849508647 : Nat.Prime 83305849508647 := by
  apply lucas_primality 83305849508647 (3 : ZMod 83305849508647)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (5741, 1), (40990639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (5741, 1), (40990639, 1)] : List FactorBlock).map factorBlockValue).prod) = 83305849508647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_59
      · exact prime_seventyTwoBR_5741
      · exact prime_seventyTwoBR_40990639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 83305849508647) ^ 41652924754323 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 83305849508647) ^ 27768616502882 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 83305849508647) ^ 1411963550994 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 83305849508647) ^ 14510686206 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 83305849508647) ^ 2032314 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_90347234100281 : Nat.Prime 90347234100281 := by
  apply lucas_primality 90347234100281 (6 : ZMod 90347234100281)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (2258680852507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (2258680852507, 1)] : List FactorBlock).map factorBlockValue).prod) = 90347234100281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_2258680852507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 90347234100281) ^ 45173617050140 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 90347234100281) ^ 18069446820056 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 90347234100281) ^ 40 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_105659154950243 : Nat.Prime 105659154950243 := by
  apply lucas_primality 105659154950243 (2 : ZMod 105659154950243)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 2), (79, 1), (137, 1), (2903767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 2), (79, 1), (137, 1), (2903767, 1)] : List FactorBlock).map factorBlockValue).prod) = 105659154950243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_41
      · exact prime_seventyTwoBR_79
      · exact prime_seventyTwoBR_137
      · exact prime_seventyTwoBR_2903767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 105659154950243) ^ 52829577475121 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 105659154950243) ^ 2577052559762 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 105659154950243) ^ 1337457657598 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 105659154950243) ^ 771234707666 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 105659154950243) ^ 36386926 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_108893318030291 : Nat.Prime 108893318030291 := by
  apply lucas_primality 108893318030291 (6 : ZMod 108893318030291)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (163, 1), (6883, 1), (9705901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (163, 1), (6883, 1), (9705901, 1)] : List FactorBlock).map factorBlockValue).prod) = 108893318030291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_163
      · exact prime_seventyTwoBR_6883
      · exact prime_seventyTwoBR_9705901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 108893318030291) ^ 54446659015145 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 108893318030291) ^ 21778663606058 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 108893318030291) ^ 668057165830 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 108893318030291) ^ 15820618630 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 108893318030291) ^ 11219290 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_109564504670267 : Nat.Prime 109564504670267 := by
  apply lucas_primality 109564504670267 (2 : ZMod 109564504670267)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (54782252335133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (54782252335133, 1)] : List FactorBlock).map factorBlockValue).prod) = 109564504670267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_54782252335133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 109564504670267) ^ 54782252335133 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 109564504670267) ^ 2 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_124454431939043 : Nat.Prime 124454431939043 := by
  apply lucas_primality 124454431939043 (2 : ZMod 124454431939043)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (62227215969521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (62227215969521, 1)] : List FactorBlock).map factorBlockValue).prod) = 124454431939043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_62227215969521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 124454431939043) ^ 62227215969521 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 124454431939043) ^ 2 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_154657376772029 : Nat.Prime 154657376772029 := by
  apply lucas_primality 154657376772029 (2 : ZMod 154657376772029)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (6361, 1), (19157, 1), (24407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (6361, 1), (19157, 1), (24407, 1)] : List FactorBlock).map factorBlockValue).prod) = 154657376772029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_13
      · exact prime_seventyTwoBR_6361
      · exact prime_seventyTwoBR_19157
      · exact prime_seventyTwoBR_24407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 154657376772029) ^ 77328688386014 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 154657376772029) ^ 11896721290156 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 154657376772029) ^ 24313374748 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 154657376772029) ^ 8073152204 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 154657376772029) ^ 6336599204 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_214534624085303 : Nat.Prime 214534624085303 := by
  apply lucas_primality 214534624085303 (5 : ZMod 214534624085303)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (853, 1), (1876910501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (853, 1), (1876910501, 1)] : List FactorBlock).map factorBlockValue).prod) = 214534624085303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_67
      · exact prime_seventyTwoBR_853
      · exact prime_seventyTwoBR_1876910501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 214534624085303) ^ 107267312042651 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 214534624085303) ^ 3202009314706 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 214534624085303) ^ 251506007134 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 214534624085303) ^ 114302 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_227253143493049 : Nat.Prime 227253143493049 := by
  apply lucas_primality 227253143493049 (17 : ZMod 227253143493049)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (498362156783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (498362156783, 1)] : List FactorBlock).map factorBlockValue).prod) = 227253143493049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_19
      · exact prime_seventyTwoBR_498362156783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 227253143493049) ^ 113626571746524 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (17 : ZMod 227253143493049) ^ 75751047831016 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (17 : ZMod 227253143493049) ^ 11960691762792 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (17 : ZMod 227253143493049) ^ 456 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_314653641426613 : Nat.Prime 314653641426613 := by
  apply lucas_primality 314653641426613 (2 : ZMod 314653641426613)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (3767, 1), (773416417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (3767, 1), (773416417, 1)] : List FactorBlock).map factorBlockValue).prod) = 314653641426613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_3767
      · exact prime_seventyTwoBR_773416417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 314653641426613) ^ 157326820713306 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 314653641426613) ^ 104884547142204 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 314653641426613) ^ 83528973036 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 314653641426613) ^ 406836 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_332200132244641 : Nat.Prime 332200132244641 := by
  apply lucas_primality 332200132244641 (14 : ZMod 332200132244641)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (11, 1), (19, 1), (223, 1), (2053, 1), (2411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (11, 1), (19, 1), (223, 1), (2053, 1), (2411, 1)] : List FactorBlock).map factorBlockValue).prod) = 332200132244641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_11
      · exact prime_seventyTwoBR_19
      · exact prime_seventyTwoBR_223
      · exact prime_seventyTwoBR_2053
      · exact prime_seventyTwoBR_2411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 332200132244641) ^ 166100066122320 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (14 : ZMod 332200132244641) ^ 110733377414880 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (14 : ZMod 332200132244641) ^ 66440026448928 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (14 : ZMod 332200132244641) ^ 30200012022240 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (14 : ZMod 332200132244641) ^ 17484217486560 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (14 : ZMod 332200132244641) ^ 1489686691680 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (14 : ZMod 332200132244641) ^ 161812046880 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (14 : ZMod 332200132244641) ^ 137785206240 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_374781957371617 : Nat.Prime 374781957371617 := by
  apply lucas_primality 374781957371617 (5 : ZMod 374781957371617)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (17, 1), (347, 1), (3137, 1), (210967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (17, 1), (347, 1), (3137, 1), (210967, 1)] : List FactorBlock).map factorBlockValue).prod) = 374781957371617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_17
      · exact prime_seventyTwoBR_347
      · exact prime_seventyTwoBR_3137
      · exact prime_seventyTwoBR_210967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 374781957371617) ^ 187390978685808 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 374781957371617) ^ 124927319123872 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 374781957371617) ^ 22045997492448 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 374781957371617) ^ 1080063277728 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 374781957371617) ^ 119471455968 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 374781957371617) ^ 1776495648 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_454896020843983 : Nat.Prime 454896020843983 := by
  apply lucas_primality 454896020843983 (5 : ZMod 454896020843983)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (89, 1), (2531, 1), (112190861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (89, 1), (2531, 1), (112190861, 1)] : List FactorBlock).map factorBlockValue).prod) = 454896020843983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_89
      · exact prime_seventyTwoBR_2531
      · exact prime_seventyTwoBR_112190861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 454896020843983) ^ 227448010421991 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 454896020843983) ^ 151632006947994 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 454896020843983) ^ 5111191245438 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 454896020843983) ^ 179729759322 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 454896020843983) ^ 4054662 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_505623993688193 : Nat.Prime 505623993688193 := by
  apply lucas_primality 505623993688193 (3 : ZMod 505623993688193)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (757, 1), (5218213277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (757, 1), (5218213277, 1)] : List FactorBlock).map factorBlockValue).prod) = 505623993688193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_757
      · exact prime_seventyTwoBR_5218213277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 505623993688193) ^ 252811996844096 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 505623993688193) ^ 667931299456 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 505623993688193) ^ 96896 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_710437001783099 : Nat.Prime 710437001783099 := by
  apply lucas_primality 710437001783099 (2 : ZMod 710437001783099)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (89, 1), (383, 1), (4093, 1), (149767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (89, 1), (383, 1), (4093, 1), (149767, 1)] : List FactorBlock).map factorBlockValue).prod) = 710437001783099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_17
      · exact prime_seventyTwoBR_89
      · exact prime_seventyTwoBR_383
      · exact prime_seventyTwoBR_4093
      · exact prime_seventyTwoBR_149767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 710437001783099) ^ 355218500891549 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 710437001783099) ^ 41790411869594 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 710437001783099) ^ 7982438222282 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 710437001783099) ^ 1854926897606 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 710437001783099) ^ 173573662786 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 710437001783099) ^ 4743615094 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_755330037212851 : Nat.Prime 755330037212851 := by
  apply lucas_primality 755330037212851 (3 : ZMod 755330037212851)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (11, 1), (71, 1), (6447546199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (11, 1), (71, 1), (6447546199, 1)] : List FactorBlock).map factorBlockValue).prod) = 755330037212851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_11
      · exact prime_seventyTwoBR_71
      · exact prime_seventyTwoBR_6447546199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 755330037212851) ^ 377665018606425 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 755330037212851) ^ 251776679070950 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 755330037212851) ^ 151066007442570 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 755330037212851) ^ 68666367019350 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 755330037212851) ^ 10638451228350 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 755330037212851) ^ 117150 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_1113448659805109 : Nat.Prime 1113448659805109 := by
  apply lucas_primality 1113448659805109 (2 : ZMod 1113448659805109)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (263, 1), (277, 1), (347361757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (263, 1), (277, 1), (347361757, 1)] : List FactorBlock).map factorBlockValue).prod) = 1113448659805109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_11
      · exact prime_seventyTwoBR_263
      · exact prime_seventyTwoBR_277
      · exact prime_seventyTwoBR_347361757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1113448659805109) ^ 556724329902554 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1113448659805109) ^ 101222605436828 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1113448659805109) ^ 4233645094316 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1113448659805109) ^ 4019670252004 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1113448659805109) ^ 3205444 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_1241186668654763 : Nat.Prime 1241186668654763 := by
  apply lucas_primality 1241186668654763 (2 : ZMod 1241186668654763)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (223, 1), (419, 1), (971, 1), (6840203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (223, 1), (419, 1), (971, 1), (6840203, 1)] : List FactorBlock).map factorBlockValue).prod) = 1241186668654763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_223
      · exact prime_seventyTwoBR_419
      · exact prime_seventyTwoBR_971
      · exact prime_seventyTwoBR_6840203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1241186668654763) ^ 620593334327381 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1241186668654763) ^ 5565859500694 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1241186668654763) ^ 2962259352398 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1241186668654763) ^ 1278256095422 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1241186668654763) ^ 181454654 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_1255755767761513 : Nat.Prime 1255755767761513 := by
  apply lucas_primality 1255755767761513 (11 : ZMod 1255755767761513)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (31, 1), (53, 1), (313, 1), (11304973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (31, 1), (53, 1), (313, 1), (11304973, 1)] : List FactorBlock).map factorBlockValue).prod) = 1255755767761513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_31
      · exact prime_seventyTwoBR_53
      · exact prime_seventyTwoBR_313
      · exact prime_seventyTwoBR_11304973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1255755767761513) ^ 627877883880756 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (11 : ZMod 1255755767761513) ^ 418585255920504 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (11 : ZMod 1255755767761513) ^ 40508250572952 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (11 : ZMod 1255755767761513) ^ 23693505052104 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (11 : ZMod 1255755767761513) ^ 4011999258024 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (11 : ZMod 1255755767761513) ^ 111079944 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_1279596625790489 : Nat.Prime 1279596625790489 := by
  apply lucas_primality 1279596625790489 (3 : ZMod 1279596625790489)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (41, 1), (6007, 1), (7589, 1), (85577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (41, 1), (6007, 1), (7589, 1), (85577, 1)] : List FactorBlock).map factorBlockValue).prod) = 1279596625790489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_41
      · exact prime_seventyTwoBR_6007
      · exact prime_seventyTwoBR_7589
      · exact prime_seventyTwoBR_85577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1279596625790489) ^ 639798312895244 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1279596625790489) ^ 31209673799768 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1279596625790489) ^ 213017583784 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1279596625790489) ^ 168612020792 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1279596625790489) ^ 14952576344 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_1403164992731303 : Nat.Prime 1403164992731303 := by
  apply lucas_primality 1403164992731303 (5 : ZMod 1403164992731303)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (97, 1), (7232809240883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (97, 1), (7232809240883, 1)] : List FactorBlock).map factorBlockValue).prod) = 1403164992731303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_97
      · exact prime_seventyTwoBR_7232809240883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1403164992731303) ^ 701582496365651 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1403164992731303) ^ 14465618481766 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1403164992731303) ^ 194 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_1531056745347641 : Nat.Prime 1531056745347641 := by
  apply lucas_primality 1531056745347641 (6 : ZMod 1531056745347641)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (349, 1), (4957, 1), (3160741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (349, 1), (4957, 1), (3160741, 1)] : List FactorBlock).map factorBlockValue).prod) = 1531056745347641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_349
      · exact prime_seventyTwoBR_4957
      · exact prime_seventyTwoBR_3160741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1531056745347641) ^ 765528372673820 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 1531056745347641) ^ 306211349069528 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 1531056745347641) ^ 218722392192520 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 1531056745347641) ^ 4386982078360 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 1531056745347641) ^ 308867610520 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 1531056745347641) ^ 484398040 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_1613299776822703 : Nat.Prime 1613299776822703 := by
  apply lucas_primality 1613299776822703 (3 : ZMod 1613299776822703)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (21863, 1), (455502017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (21863, 1), (455502017, 1)] : List FactorBlock).map factorBlockValue).prod) = 1613299776822703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_21863
      · exact prime_seventyTwoBR_455502017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1613299776822703) ^ 806649888411351 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1613299776822703) ^ 537766592274234 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1613299776822703) ^ 73791326754 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1613299776822703) ^ 3541806 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_1633299661310827 : Nat.Prime 1633299661310827 := by
  apply lucas_primality 1633299661310827 (2 : ZMod 1633299661310827)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (73, 1), (1201, 1), (1973, 1), (1573699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (73, 1), (1201, 1), (1973, 1), (1573699, 1)] : List FactorBlock).map factorBlockValue).prod) = 1633299661310827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_73
      · exact prime_seventyTwoBR_1201
      · exact prime_seventyTwoBR_1973
      · exact prime_seventyTwoBR_1573699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1633299661310827) ^ 816649830655413 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1633299661310827) ^ 544433220436942 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1633299661310827) ^ 22373967963162 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1633299661310827) ^ 1359949759626 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1633299661310827) ^ 827825474562 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1633299661310827) ^ 1037872974 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_2430460956692609 : Nat.Prime 2430460956692609 := by
  apply lucas_primality 2430460956692609 (3 : ZMod 2430460956692609)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (7, 1), (41, 1), (66160195903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (7, 1), (41, 1), (66160195903, 1)] : List FactorBlock).map factorBlockValue).prod) = 2430460956692609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_41
      · exact prime_seventyTwoBR_66160195903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2430460956692609) ^ 1215230478346304 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 2430460956692609) ^ 347208708098944 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 2430460956692609) ^ 59279535529088 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 2430460956692609) ^ 36736 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_2933565821357749 : Nat.Prime 2933565821357749 := by
  apply lucas_primality 2933565821357749 (2 : ZMod 2933565821357749)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (12866516760341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (12866516760341, 1)] : List FactorBlock).map factorBlockValue).prod) = 2933565821357749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_19
      · exact prime_seventyTwoBR_12866516760341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2933565821357749) ^ 1466782910678874 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2933565821357749) ^ 977855273785916 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2933565821357749) ^ 154398201124092 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2933565821357749) ^ 228 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_3210623017014349 : Nat.Prime 3210623017014349 := by
  apply lucas_primality 3210623017014349 (7 : ZMod 3210623017014349)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 5), (13, 1), (254085392293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 5), (13, 1), (254085392293, 1)] : List FactorBlock).map factorBlockValue).prod) = 3210623017014349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_13
      · exact prime_seventyTwoBR_254085392293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 3210623017014349) ^ 1605311508507174 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 3210623017014349) ^ 1070207672338116 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 3210623017014349) ^ 246971001308796 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 3210623017014349) ^ 12636 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_3616457187859687 : Nat.Prime 3616457187859687 := by
  apply lucas_primality 3616457187859687 (3 : ZMod 3616457187859687)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (22323809801603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (22323809801603, 1)] : List FactorBlock).map factorBlockValue).prod) = 3616457187859687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_22323809801603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3616457187859687) ^ 1808228593929843 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 3616457187859687) ^ 1205485729286562 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 3616457187859687) ^ 162 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_6699550171183439 : Nat.Prime 6699550171183439 := by
  apply lucas_primality 6699550171183439 (11 : ZMod 6699550171183439)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (167, 1), (1571, 1), (12768003467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (167, 1), (1571, 1), (12768003467, 1)] : List FactorBlock).map factorBlockValue).prod) = 6699550171183439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_167
      · exact prime_seventyTwoBR_1571
      · exact prime_seventyTwoBR_12768003467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 6699550171183439) ^ 3349775085591719 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (11 : ZMod 6699550171183439) ^ 40117066893314 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (11 : ZMod 6699550171183439) ^ 4264513157978 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (11 : ZMod 6699550171183439) ^ 524714 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_10007712458567627 : Nat.Prime 10007712458567627 := by
  apply lucas_primality 10007712458567627 (2 : ZMod 10007712458567627)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (454896020843983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (454896020843983, 1)] : List FactorBlock).map factorBlockValue).prod) = 10007712458567627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_11
      · exact prime_seventyTwoBR_454896020843983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 10007712458567627) ^ 5003856229283813 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 10007712458567627) ^ 909792041687966 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 10007712458567627) ^ 22 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_12819812537981759 : Nat.Prime 12819812537981759 := by
  apply lucas_primality 12819812537981759 (7 : ZMod 12819812537981759)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67189, 1), (214987, 1), (443753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67189, 1), (214987, 1), (443753, 1)] : List FactorBlock).map factorBlockValue).prod) = 12819812537981759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_67189
      · exact prime_seventyTwoBR_214987
      · exact prime_seventyTwoBR_443753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 12819812537981759) ^ 6409906268990879 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 12819812537981759) ^ 190802252422 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 12819812537981759) ^ 59630640634 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 12819812537981759) ^ 28889523086 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_13689987513294731 : Nat.Prime 13689987513294731 := by
  apply lucas_primality 13689987513294731 (2 : ZMod 13689987513294731)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (124454431939043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (124454431939043, 1)] : List FactorBlock).map factorBlockValue).prod) = 13689987513294731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_11
      · exact prime_seventyTwoBR_124454431939043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13689987513294731) ^ 6844993756647365 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 13689987513294731) ^ 2737997502658946 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 13689987513294731) ^ 1244544319390430 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 13689987513294731) ^ 110 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_15834585403763041 : Nat.Prime 15834585403763041 := by
  apply lucas_primality 15834585403763041 (7 : ZMod 15834585403763041)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (383, 1), (23167, 1), (3717893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (383, 1), (23167, 1), (3717893, 1)] : List FactorBlock).map factorBlockValue).prod) = 15834585403763041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_383
      · exact prime_seventyTwoBR_23167
      · exact prime_seventyTwoBR_3717893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 15834585403763041) ^ 7917292701881520 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 15834585403763041) ^ 5278195134587680 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 15834585403763041) ^ 3166917080752608 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 15834585403763041) ^ 41343565022880 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 15834585403763041) ^ 683497449120 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 15834585403763041) ^ 4259021280 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_21812790670809041 : Nat.Prime 21812790670809041 := by
  apply lucas_primality 21812790670809041 (3 : ZMod 21812790670809041)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (7, 1), (105649, 1), (368686991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (7, 1), (105649, 1), (368686991, 1)] : List FactorBlock).map factorBlockValue).prod) = 21812790670809041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_105649
      · exact prime_seventyTwoBR_368686991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 21812790670809041) ^ 10906395335404520 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 21812790670809041) ^ 4362558134161808 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 21812790670809041) ^ 3116112952972720 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 21812790670809041) ^ 206464714960 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 21812790670809041) ^ 59163440 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_22475569890821699 : Nat.Prime 22475569890821699 := by
  apply lucas_primality 22475569890821699 (2 : ZMod 22475569890821699)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (47, 1), (49783, 1), (686125807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (47, 1), (49783, 1), (686125807, 1)] : List FactorBlock).map factorBlockValue).prod) = 22475569890821699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_47
      · exact prime_seventyTwoBR_49783
      · exact prime_seventyTwoBR_686125807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22475569890821699) ^ 11237784945410849 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 22475569890821699) ^ 3210795698688814 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 22475569890821699) ^ 478203614698334 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 22475569890821699) ^ 451470781006 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 22475569890821699) ^ 32757214 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_27817473315656539 : Nat.Prime 27817473315656539 := by
  apply lucas_primality 27817473315656539 (2 : ZMod 27817473315656539)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (4567, 1), (338387384323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (4567, 1), (338387384323, 1)] : List FactorBlock).map factorBlockValue).prod) = 27817473315656539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_4567
      · exact prime_seventyTwoBR_338387384323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 27817473315656539) ^ 13908736657828269 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 27817473315656539) ^ 9272491105218846 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 27817473315656539) ^ 6090972917814 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 27817473315656539) ^ 82206 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_37471800127765889 : Nat.Prime 37471800127765889 := by
  apply lucas_primality 37471800127765889 (3 : ZMod 37471800127765889)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (101, 1), (2898499391071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (101, 1), (2898499391071, 1)] : List FactorBlock).map factorBlockValue).prod) = 37471800127765889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_101
      · exact prime_seventyTwoBR_2898499391071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 37471800127765889) ^ 18735900063882944 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 37471800127765889) ^ 371007922057088 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 37471800127765889) ^ 12928 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_39316878497239253 : Nat.Prime 39316878497239253 := by
  apply lucas_primality 39316878497239253 (2 : ZMod 39316878497239253)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (13, 1), (11927, 1), (9056208809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (13, 1), (11927, 1), (9056208809, 1)] : List FactorBlock).map factorBlockValue).prod) = 39316878497239253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_13
      · exact prime_seventyTwoBR_11927
      · exact prime_seventyTwoBR_9056208809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 39316878497239253) ^ 19658439248619626 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 39316878497239253) ^ 5616696928177036 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 39316878497239253) ^ 3024375269018404 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 39316878497239253) ^ 3296460006476 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 39316878497239253) ^ 4341428 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_48933549083352151 : Nat.Prime 48933549083352151 := by
  apply lucas_primality 48933549083352151 (7 : ZMod 48933549083352151)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (7, 1), (15534460026461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (7, 1), (15534460026461, 1)] : List FactorBlock).map factorBlockValue).prod) = 48933549083352151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_15534460026461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 48933549083352151) ^ 24466774541676075 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 48933549083352151) ^ 16311183027784050 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 48933549083352151) ^ 9786709816670430 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 48933549083352151) ^ 6990507011907450 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 48933549083352151) ^ 3150 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_53185988589328711 : Nat.Prime 53185988589328711 := by
  apply lucas_primality 53185988589328711 (6 : ZMod 53185988589328711)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (19, 1), (8969, 1), (3467824429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (19, 1), (8969, 1), (3467824429, 1)] : List FactorBlock).map factorBlockValue).prod) = 53185988589328711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_19
      · exact prime_seventyTwoBR_8969
      · exact prime_seventyTwoBR_3467824429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 53185988589328711) ^ 26592994294664355 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 53185988589328711) ^ 17728662863109570 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 53185988589328711) ^ 10637197717865742 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 53185988589328711) ^ 2799262557333090 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 53185988589328711) ^ 5929979773590 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 53185988589328711) ^ 15336990 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_63040124235040409 : Nat.Prime 63040124235040409 := by
  apply lucas_primality 63040124235040409 (3 : ZMod 63040124235040409)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (79, 1), (7624307, 1), (13082767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (79, 1), (7624307, 1), (13082767, 1)] : List FactorBlock).map factorBlockValue).prod) = 63040124235040409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_79
      · exact prime_seventyTwoBR_7624307
      · exact prime_seventyTwoBR_13082767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 63040124235040409) ^ 31520062117520204 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 63040124235040409) ^ 797976256139752 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 63040124235040409) ^ 8268308744 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 63040124235040409) ^ 4818562024 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_70436048370411391 : Nat.Prime 70436048370411391 := by
  apply lucas_primality 70436048370411391 (3 : ZMod 70436048370411391)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (315373, 1), (7444734581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (315373, 1), (7444734581, 1)] : List FactorBlock).map factorBlockValue).prod) = 70436048370411391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_315373
      · exact prime_seventyTwoBR_7444734581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 70436048370411391) ^ 35218024185205695 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 70436048370411391) ^ 23478682790137130 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 70436048370411391) ^ 14087209674082278 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 70436048370411391) ^ 223342037430 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 70436048370411391) ^ 9461190 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_76646007751338589 : Nat.Prime 76646007751338589 := by
  apply lucas_primality 76646007751338589 (6 : ZMod 76646007751338589)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (59, 1), (229, 1), (472738310459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (59, 1), (229, 1), (472738310459, 1)] : List FactorBlock).map factorBlockValue).prod) = 76646007751338589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_59
      · exact prime_seventyTwoBR_229
      · exact prime_seventyTwoBR_472738310459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 76646007751338589) ^ 38323003875669294 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 76646007751338589) ^ 25548669250446196 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 76646007751338589) ^ 1299084877141332 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 76646007751338589) ^ 334698723804972 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 76646007751338589) ^ 162132 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_109428142733632777 : Nat.Prime 109428142733632777 := by
  apply lucas_primality 109428142733632777 (5 : ZMod 109428142733632777)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (179, 1), (25472100263881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (179, 1), (25472100263881, 1)] : List FactorBlock).map factorBlockValue).prod) = 109428142733632777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_179
      · exact prime_seventyTwoBR_25472100263881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 109428142733632777) ^ 54714071366816388 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 109428142733632777) ^ 36476047577877592 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 109428142733632777) ^ 611330406333144 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 109428142733632777) ^ 4296 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_153304251163993169 : Nat.Prime 153304251163993169 := by
  apply lucas_primality 153304251163993169 (3 : ZMod 153304251163993169)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (21647, 1), (252823, 1), (1750733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (21647, 1), (252823, 1), (1750733, 1)] : List FactorBlock).map factorBlockValue).prod) = 153304251163993169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_21647
      · exact prime_seventyTwoBR_252823
      · exact prime_seventyTwoBR_1750733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 153304251163993169) ^ 76652125581996584 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 153304251163993169) ^ 7082009108144 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 153304251163993169) ^ 606369876016 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 153304251163993169) ^ 87565751696 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_179804559126573593 : Nat.Prime 179804559126573593 := by
  apply lucas_primality 179804559126573593 (3 : ZMod 179804559126573593)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (22475569890821699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (22475569890821699, 1)] : List FactorBlock).map factorBlockValue).prod) = 179804559126573593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_22475569890821699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 179804559126573593) ^ 89902279563286796 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 179804559126573593) ^ 8 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_207666064086254551 : Nat.Prime 207666064086254551 := by
  apply lucas_primality 207666064086254551 (7 : ZMod 207666064086254551)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (7, 1), (557, 1), (309571, 1), (382331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (7, 1), (557, 1), (309571, 1), (382331, 1)] : List FactorBlock).map factorBlockValue).prod) = 207666064086254551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_557
      · exact prime_seventyTwoBR_309571
      · exact prime_seventyTwoBR_382331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 207666064086254551) ^ 103833032043127275 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 207666064086254551) ^ 69222021362084850 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 207666064086254551) ^ 41533212817250910 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 207666064086254551) ^ 29666580583750650 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 207666064086254551) ^ 372829558503150 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 207666064086254551) ^ 670818856050 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 207666064086254551) ^ 543157798050 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_258699985223221219 : Nat.Prime 258699985223221219 := by
  apply lucas_primality 258699985223221219 (10 : ZMod 258699985223221219)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1634441, 1), (26380067683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1634441, 1), (26380067683, 1)] : List FactorBlock).map factorBlockValue).prod) = 258699985223221219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_1634441
      · exact prime_seventyTwoBR_26380067683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 258699985223221219) ^ 129349992611610609 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (10 : ZMod 258699985223221219) ^ 86233328407740406 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (10 : ZMod 258699985223221219) ^ 158280406098 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (10 : ZMod 258699985223221219) ^ 9806646 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_336477040989663803 : Nat.Prime 336477040989663803 := by
  apply lucas_primality 336477040989663803 (2 : ZMod 336477040989663803)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (915919, 1), (183682749779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (915919, 1), (183682749779, 1)] : List FactorBlock).map factorBlockValue).prod) = 336477040989663803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_915919
      · exact prime_seventyTwoBR_183682749779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 336477040989663803) ^ 168238520494831901 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 336477040989663803) ^ 367365499558 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 336477040989663803) ^ 1831838 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_463851579150316801 : Nat.Prime 463851579150316801 := by
  apply lucas_primality 463851579150316801 (7 : ZMod 463851579150316801)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 3), (5, 2), (338839, 1), (7922129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 3), (5, 2), (338839, 1), (7922129, 1)] : List FactorBlock).map factorBlockValue).prod) = 463851579150316801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_338839
      · exact prime_seventyTwoBR_7922129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 463851579150316801) ^ 231925789575158400 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 463851579150316801) ^ 154617193050105600 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 463851579150316801) ^ 92770315830063360 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 463851579150316801) ^ 1368943891200 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 463851579150316801) ^ 58551379200 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_549199920203943571 : Nat.Prime 549199920203943571 := by
  apply lucas_primality 549199920203943571 (3 : ZMod 549199920203943571)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (1901567, 1), (3209048819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (1901567, 1), (3209048819, 1)] : List FactorBlock).map factorBlockValue).prod) = 549199920203943571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_1901567
      · exact prime_seventyTwoBR_3209048819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 549199920203943571) ^ 274599960101971785 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 549199920203943571) ^ 183066640067981190 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 549199920203943571) ^ 109839984040788714 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 549199920203943571) ^ 288814393710 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 549199920203943571) ^ 171141030 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_607133031219019337 : Nat.Prime 607133031219019337 := by
  apply lucas_primality 607133031219019337 (3 : ZMod 607133031219019337)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (911, 1), (83305849508647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (911, 1), (83305849508647, 1)] : List FactorBlock).map factorBlockValue).prod) = 607133031219019337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_911
      · exact prime_seventyTwoBR_83305849508647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 607133031219019337) ^ 303566515609509668 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 607133031219019337) ^ 666446796069176 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 607133031219019337) ^ 7288 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_717405158976231287 : Nat.Prime 717405158976231287 := by
  apply lucas_primality 717405158976231287 (5 : ZMod 717405158976231287)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (9923, 1), (12697, 1), (258819923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (9923, 1), (12697, 1), (258819923, 1)] : List FactorBlock).map factorBlockValue).prod) = 717405158976231287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_11
      · exact prime_seventyTwoBR_9923
      · exact prime_seventyTwoBR_12697
      · exact prime_seventyTwoBR_258819923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 717405158976231287) ^ 358702579488115643 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 717405158976231287) ^ 65218650816021026 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 717405158976231287) ^ 72297204371282 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 717405158976231287) ^ 56501942110438 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 717405158976231287) ^ 2771831282 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_1651976179213107581 : Nat.Prime 1651976179213107581 := by
  apply lucas_primality 1651976179213107581 (2 : ZMod 1651976179213107581)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (41201, 1), (286396685797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (41201, 1), (286396685797, 1)] : List FactorBlock).map factorBlockValue).prod) = 1651976179213107581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_41201
      · exact prime_seventyTwoBR_286396685797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1651976179213107581) ^ 825988089606553790 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1651976179213107581) ^ 330395235842621516 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1651976179213107581) ^ 235996597030443940 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1651976179213107581) ^ 40095536011580 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1651976179213107581) ^ 5768140 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_1972209354371518949 : Nat.Prime 1972209354371518949 := by
  apply lucas_primality 1972209354371518949 (2 : ZMod 1972209354371518949)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (70436048370411391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (70436048370411391, 1)] : List FactorBlock).map factorBlockValue).prod) = 1972209354371518949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_70436048370411391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1972209354371518949) ^ 986104677185759474 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1972209354371518949) ^ 281744193481645564 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1972209354371518949) ^ 28 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_2453999752523335957 : Nat.Prime 2453999752523335957 := by
  apply lucas_primality 2453999752523335957 (2 : ZMod 2453999752523335957)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (131, 1), (82161502361167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (131, 1), (82161502361167, 1)] : List FactorBlock).map factorBlockValue).prod) = 2453999752523335957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_19
      · exact prime_seventyTwoBR_131
      · exact prime_seventyTwoBR_82161502361167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2453999752523335957) ^ 1226999876261667978 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2453999752523335957) ^ 817999917507778652 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2453999752523335957) ^ 129157881711754524 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2453999752523335957) ^ 18732822538346076 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2453999752523335957) ^ 29868 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_3303952358426215163 : Nat.Prime 3303952358426215163 := by
  apply lucas_primality 3303952358426215163 (2 : ZMod 3303952358426215163)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1651976179213107581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1651976179213107581, 1)] : List FactorBlock).map factorBlockValue).prod) = 3303952358426215163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_1651976179213107581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 3303952358426215163) ^ 1651976179213107581 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 3303952358426215163) ^ 2 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_5252550851214373297 : Nat.Prime 5252550851214373297 := by
  apply lucas_primality 5252550851214373297 (5 : ZMod 5252550851214373297)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (109428142733632777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (109428142733632777, 1)] : List FactorBlock).map factorBlockValue).prod) = 5252550851214373297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_109428142733632777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 5252550851214373297) ^ 2626275425607186648 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 5252550851214373297) ^ 1750850283738124432 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 5252550851214373297) ^ 48 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_5578377785623596091 : Nat.Prime 5578377785623596091 := by
  apply lucas_primality 5578377785623596091 (3 : ZMod 5578377785623596091)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (167, 1), (1113448659805109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (167, 1), (1113448659805109, 1)] : List FactorBlock).map factorBlockValue).prod) = 5578377785623596091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_167
      · exact prime_seventyTwoBR_1113448659805109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5578377785623596091) ^ 2789188892811798045 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 5578377785623596091) ^ 1859459261874532030 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 5578377785623596091) ^ 1115675557124719218 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 5578377785623596091) ^ 33403459794153270 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 5578377785623596091) ^ 5010 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_7105475845583015171 : Nat.Prime 7105475845583015171 := by
  apply lucas_primality 7105475845583015171 (2 : ZMod 7105475845583015171)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (71, 1), (10007712458567627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (71, 1), (10007712458567627, 1)] : List FactorBlock).map factorBlockValue).prod) = 7105475845583015171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_71
      · exact prime_seventyTwoBR_10007712458567627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7105475845583015171) ^ 3552737922791507585 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 7105475845583015171) ^ 1421095169116603034 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 7105475845583015171) ^ 100077124585676270 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 7105475845583015171) ^ 710 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_9815999010093343829 : Nat.Prime 9815999010093343829 := by
  apply lucas_primality 9815999010093343829 (2 : ZMod 9815999010093343829)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2453999752523335957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2453999752523335957, 1)] : List FactorBlock).map factorBlockValue).prod) = 9815999010093343829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_2453999752523335957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 9815999010093343829) ^ 4907999505046671914 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 9815999010093343829) ^ 4 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_15644260193571294431 : Nat.Prime 15644260193571294431 := by
  apply lucas_primality 15644260193571294431 (11 : ZMod 15644260193571294431)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (43, 1), (59, 1), (71, 1), (9859, 1), (880933951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (43, 1), (59, 1), (71, 1), (9859, 1), (880933951, 1)] : List FactorBlock).map factorBlockValue).prod) = 15644260193571294431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_43
      · exact prime_seventyTwoBR_59
      · exact prime_seventyTwoBR_71
      · exact prime_seventyTwoBR_9859
      · exact prime_seventyTwoBR_880933951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 15644260193571294431) ^ 7822130096785647215 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (11 : ZMod 15644260193571294431) ^ 3128852038714258886 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (11 : ZMod 15644260193571294431) ^ 363820004501658010 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (11 : ZMod 15644260193571294431) ^ 265156952433411770 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (11 : ZMod 15644260193571294431) ^ 220341692867201330 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (11 : ZMod 15644260193571294431) ^ 1586799897917770 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (11 : ZMod 15644260193571294431) ^ 17758720930 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_18390256610937363227 : Nat.Prime 18390256610937363227 := by
  apply lucas_primality 18390256610937363227 (2 : ZMod 18390256610937363227)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (4159583, 1), (116346787969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (4159583, 1), (116346787969, 1)] : List FactorBlock).map factorBlockValue).prod) = 18390256610937363227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_19
      · exact prime_seventyTwoBR_4159583
      · exact prime_seventyTwoBR_116346787969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 18390256610937363227) ^ 9195128305468681613 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 18390256610937363227) ^ 967908242680913854 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 18390256610937363227) ^ 4421177942822 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 18390256610937363227) ^ 158064154 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_26226569552104612423 : Nat.Prime 26226569552104612423 := by
  apply lucas_primality 26226569552104612423 (6 : ZMod 26226569552104612423)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (643, 1), (755330037212851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (643, 1), (755330037212851, 1)] : List FactorBlock).map factorBlockValue).prod) = 26226569552104612423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_643
      · exact prime_seventyTwoBR_755330037212851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 26226569552104612423) ^ 13113284776052306211 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 26226569552104612423) ^ 8742189850701537474 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 26226569552104612423) ^ 40787822009493954 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (6 : ZMod 26226569552104612423) ^ 34722 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_230670806352274708181 : Nat.Prime 230670806352274708181 := by
  apply lucas_primality 230670806352274708181 (2 : ZMod 230670806352274708181)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (6301, 1), (831553, 1), (2201218853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (6301, 1), (831553, 1), (2201218853, 1)] : List FactorBlock).map factorBlockValue).prod) = 230670806352274708181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_6301
      · exact prime_seventyTwoBR_831553
      · exact prime_seventyTwoBR_2201218853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 230670806352274708181) ^ 115335403176137354090 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 230670806352274708181) ^ 46134161270454941636 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 230670806352274708181) ^ 36608602817374180 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 230670806352274708181) ^ 277397599855060 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 230670806352274708181) ^ 104792309060 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_262443780759797988019 : Nat.Prime 262443780759797988019 := by
  apply lucas_primality 262443780759797988019 (2 : ZMod 262443780759797988019)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (186120703, 1), (235012169101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (186120703, 1), (235012169101, 1)] : List FactorBlock).map factorBlockValue).prod) = 262443780759797988019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_186120703
      · exact prime_seventyTwoBR_235012169101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 262443780759797988019) ^ 131221890379898994009 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 262443780759797988019) ^ 87481260253265996006 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 262443780759797988019) ^ 1410073014606 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 262443780759797988019) ^ 1116724218 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_889543747188376293397 : Nat.Prime 889543747188376293397 := by
  apply lucas_primality 889543747188376293397 (2 : ZMod 889543747188376293397)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (31, 1), (3181, 1), (16567, 1), (2669118827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (31, 1), (3181, 1), (16567, 1), (2669118827, 1)] : List FactorBlock).map factorBlockValue).prod) = 889543747188376293397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_17
      · exact prime_seventyTwoBR_31
      · exact prime_seventyTwoBR_3181
      · exact prime_seventyTwoBR_16567
      · exact prime_seventyTwoBR_2669118827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 889543747188376293397) ^ 444771873594188146698 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 889543747188376293397) ^ 296514582396125431132 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 889543747188376293397) ^ 52326102775786840788 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 889543747188376293397) ^ 28694959586721815916 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 889543747188376293397) ^ 279642800122092516 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 889543747188376293397) ^ 53693713236456588 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 889543747188376293397) ^ 333272441148 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_892540445699775374561 : Nat.Prime 892540445699775374561 := by
  apply lucas_primality 892540445699775374561 (3 : ZMod 892540445699775374561)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (5578377785623596091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (5578377785623596091, 1)] : List FactorBlock).map factorBlockValue).prod) = 892540445699775374561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_5578377785623596091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 892540445699775374561) ^ 446270222849887687280 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 892540445699775374561) ^ 178508089139955074912 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 892540445699775374561) ^ 160 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_942953299425405198277 : Nat.Prime 942953299425405198277 := by
  apply lucas_primality 942953299425405198277 (2 : ZMod 942953299425405198277)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (617, 1), (79724609, 1), (1597465091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (617, 1), (79724609, 1), (1597465091, 1)] : List FactorBlock).map factorBlockValue).prod) = 942953299425405198277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_617
      · exact prime_seventyTwoBR_79724609
      · exact prime_seventyTwoBR_1597465091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 942953299425405198277) ^ 471476649712702599138 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 942953299425405198277) ^ 314317766475135066092 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 942953299425405198277) ^ 1528287357253493028 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 942953299425405198277) ^ 11827631533764 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 942953299425405198277) ^ 590281005036 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_1585205519483868388159 : Nat.Prime 1585205519483868388159 := by
  apply lucas_primality 1585205519483868388159 (3 : ZMod 1585205519483868388159)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (23, 1), (541, 1), (1633299661310827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (23, 1), (541, 1), (1633299661310827, 1)] : List FactorBlock).map factorBlockValue).prod) = 1585205519483868388159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_13
      · exact prime_seventyTwoBR_23
      · exact prime_seventyTwoBR_541
      · exact prime_seventyTwoBR_1633299661310827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1585205519483868388159) ^ 792602759741934194079 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1585205519483868388159) ^ 528401839827956129386 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1585205519483868388159) ^ 121938886114143722166 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1585205519483868388159) ^ 68921979107994277746 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1585205519483868388159) ^ 2930139592391623638 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1585205519483868388159) ^ 970554 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_1994250993419108065129 : Nat.Prime 1994250993419108065129 := by
  apply lucas_primality 1994250993419108065129 (7 : ZMod 1994250993419108065129)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (281, 1), (118361, 1), (247099, 1), (594749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (281, 1), (118361, 1), (247099, 1), (594749, 1)] : List FactorBlock).map factorBlockValue).prod) = 1994250993419108065129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_17
      · exact prime_seventyTwoBR_281
      · exact prime_seventyTwoBR_118361
      · exact prime_seventyTwoBR_247099
      · exact prime_seventyTwoBR_594749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1994250993419108065129) ^ 997125496709554032564 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1994250993419108065129) ^ 664750331139702688376 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1994250993419108065129) ^ 117308881965829886184 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1994250993419108065129) ^ 7096978624267288488 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1994250993419108065129) ^ 16848885979495848 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1994250993419108065129) ^ 8070655864326072 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1994250993419108065129) ^ 3353096841556872 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_2923075326350927212433 : Nat.Prime 2923075326350927212433 := by
  apply lucas_primality 2923075326350927212433 (3 : ZMod 2923075326350927212433)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (84527909, 1), (196484010223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (84527909, 1), (196484010223, 1)] : List FactorBlock).map factorBlockValue).prod) = 2923075326350927212433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_11
      · exact prime_seventyTwoBR_84527909
      · exact prime_seventyTwoBR_196484010223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2923075326350927212433) ^ 1461537663175463606216 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 2923075326350927212433) ^ 265734120577357019312 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 2923075326350927212433) ^ 34581185799248 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 2923075326350927212433) ^ 14876911984 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_6417502447590859269067 : Nat.Prime 6417502447590859269067 := by
  apply lucas_primality 6417502447590859269067 (2 : ZMod 6417502447590859269067)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (333139, 1), (3210623017014349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (333139, 1), (3210623017014349, 1)] : List FactorBlock).map factorBlockValue).prod) = 6417502447590859269067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_333139
      · exact prime_seventyTwoBR_3210623017014349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6417502447590859269067) ^ 3208751223795429634533 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 6417502447590859269067) ^ 2139167482530286423022 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 6417502447590859269067) ^ 19263738102086094 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 6417502447590859269067) ^ 1998834 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_13454063766471313210661 : Nat.Prime 13454063766471313210661 := by
  apply lucas_primality 13454063766471313210661 (2 : ZMod 13454063766471313210661)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (43, 1), (15644260193571294431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (43, 1), (15644260193571294431, 1)] : List FactorBlock).map factorBlockValue).prod) = 13454063766471313210661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_43
      · exact prime_seventyTwoBR_15644260193571294431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13454063766471313210661) ^ 6727031883235656605330 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 13454063766471313210661) ^ 2690812753294262642132 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 13454063766471313210661) ^ 312885203871425888620 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 13454063766471313210661) ^ 860 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_24309173954927264587543 : Nat.Prime 24309173954927264587543 := by
  apply lucas_primality 24309173954927264587543 (3 : ZMod 24309173954927264587543)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (187690163, 1), (2398473531371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (187690163, 1), (2398473531371, 1)] : List FactorBlock).map factorBlockValue).prod) = 24309173954927264587543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_187690163
      · exact prime_seventyTwoBR_2398473531371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 24309173954927264587543) ^ 12154586977463632293771 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 24309173954927264587543) ^ 8103057984975754862514 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 24309173954927264587543) ^ 129517570694034 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 24309173954927264587543) ^ 10135268802 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_30501804402887818393849 : Nat.Prime 30501804402887818393849 := by
  apply lucas_primality 30501804402887818393849 (23 : ZMod 30501804402887818393849)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (13, 1), (647, 1), (34292669, 1), (629458829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (13, 1), (647, 1), (34292669, 1), (629458829, 1)] : List FactorBlock).map factorBlockValue).prod) = 30501804402887818393849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_13
      · exact prime_seventyTwoBR_647
      · exact prime_seventyTwoBR_34292669
      · exact prime_seventyTwoBR_629458829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 30501804402887818393849) ^ 15250902201443909196924 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (23 : ZMod 30501804402887818393849) ^ 10167268134295939464616 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (23 : ZMod 30501804402887818393849) ^ 4357400628983974056264 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (23 : ZMod 30501804402887818393849) ^ 2346292646375986030296 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (23 : ZMod 30501804402887818393849) ^ 47143438026101728584 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (23 : ZMod 30501804402887818393849) ^ 889455539400792 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (23 : ZMod 30501804402887818393849) ^ 48457187345112 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_31206087177027442158307 : Nat.Prime 31206087177027442158307 := by
  apply lucas_primality 31206087177027442158307 (3 : ZMod 31206087177027442158307)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (193, 1), (255049, 1), (105659154950243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (193, 1), (255049, 1), (105659154950243, 1)] : List FactorBlock).map factorBlockValue).prod) = 31206087177027442158307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_193
      · exact prime_seventyTwoBR_255049
      · exact prime_seventyTwoBR_105659154950243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 31206087177027442158307) ^ 15603043588513721079153 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 31206087177027442158307) ^ 10402029059009147386102 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 31206087177027442158307) ^ 161689570865427161442 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 31206087177027442158307) ^ 122353301432381394 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 31206087177027442158307) ^ 295346742 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_33394028632337555706259 : Nat.Prime 33394028632337555706259 := by
  apply lucas_primality 33394028632337555706259 (2 : ZMod 33394028632337555706259)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (7, 1), (9815999010093343829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (7, 1), (9815999010093343829, 1)] : List FactorBlock).map factorBlockValue).prod) = 33394028632337555706259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_9815999010093343829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 33394028632337555706259) ^ 16697014316168777853129 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 33394028632337555706259) ^ 11131342877445851902086 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 33394028632337555706259) ^ 4770575518905365100894 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 33394028632337555706259) ^ 3402 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_44356863149970354174931 : Nat.Prime 44356863149970354174931 := by
  apply lucas_primality 44356863149970354174931 (2 : ZMod 44356863149970354174931)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (23, 1), (103, 1), (3207013, 1), (194613870523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (23, 1), (103, 1), (3207013, 1), (194613870523, 1)] : List FactorBlock).map factorBlockValue).prod) = 44356863149970354174931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_23
      · exact prime_seventyTwoBR_103
      · exact prime_seventyTwoBR_3207013
      · exact prime_seventyTwoBR_194613870523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 44356863149970354174931) ^ 22178431574985177087465 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 44356863149970354174931) ^ 14785621049990118058310 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 44356863149970354174931) ^ 8871372629994070834986 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 44356863149970354174931) ^ 1928559267390015398910 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 44356863149970354174931) ^ 430649156795828681310 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 44356863149970354174931) ^ 13831207778069610 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 44356863149970354174931) ^ 227922413910 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_47354683110784303483997 : Nat.Prime 47354683110784303483997 := by
  apply lucas_primality 47354683110784303483997 (2 : ZMod 47354683110784303483997)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (6199, 1), (6679, 1), (21995128891363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (6199, 1), (6679, 1), (21995128891363, 1)] : List FactorBlock).map factorBlockValue).prod) = 47354683110784303483997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_13
      · exact prime_seventyTwoBR_6199
      · exact prime_seventyTwoBR_6679
      · exact prime_seventyTwoBR_21995128891363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 47354683110784303483997) ^ 23677341555392151741998 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 47354683110784303483997) ^ 3642667931598792575692 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 47354683110784303483997) ^ 7639084225001500804 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 47354683110784303483997) ^ 7090085807873080324 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 47354683110784303483997) ^ 2152962292 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_72915860960910461352557 : Nat.Prime 72915860960910461352557 := by
  apply lucas_primality 72915860960910461352557 (2 : ZMod 72915860960910461352557)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (1987, 1), (13275277, 1), (36371981119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (1987, 1), (13275277, 1), (36371981119, 1)] : List FactorBlock).map factorBlockValue).prod) = 72915860960910461352557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_19
      · exact prime_seventyTwoBR_1987
      · exact prime_seventyTwoBR_13275277
      · exact prime_seventyTwoBR_36371981119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 72915860960910461352557) ^ 36457930480455230676278 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 72915860960910461352557) ^ 3837676892679497965924 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 72915860960910461352557) ^ 36696457453905617188 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 72915860960910461352557) ^ 5492605612742428 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 72915860960910461352557) ^ 2004726130324 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_85973493506179321550957 : Nat.Prime 85973493506179321550957 := by
  apply lucas_primality 85973493506179321550957 (5 : ZMod 85973493506179321550957)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (19, 1), (29, 1), (61, 1), (167, 1), (499, 1), (10093, 1), (108614503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (19, 1), (29, 1), (61, 1), (167, 1), (499, 1), (10093, 1), (108614503, 1)] : List FactorBlock).map factorBlockValue).prod) = 85973493506179321550957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_19
      · exact prime_seventyTwoBR_29
      · exact prime_seventyTwoBR_61
      · exact prime_seventyTwoBR_167
      · exact prime_seventyTwoBR_499
      · exact prime_seventyTwoBR_10093
      · exact prime_seventyTwoBR_108614503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 85973493506179321550957) ^ 42986746753089660775478 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 85973493506179321550957) ^ 12281927643739903078708 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 85973493506179321550957) ^ 4524920710851543239524 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 85973493506179321550957) ^ 2964603224351011087964 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 85973493506179321550957) ^ 1409401532888185599196 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 85973493506179321550957) ^ 514811338360355218868 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 85973493506179321550957) ^ 172291570152663971044 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 85973493506179321550957) ^ 8518130734784436892 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 85973493506179321550957) ^ 791547087465652 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_96020376098014700377229 : Nat.Prime 96020376098014700377229 := by
  apply lucas_primality 96020376098014700377229 (2 : ZMod 96020376098014700377229)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (33461, 1), (717405158976231287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (33461, 1), (717405158976231287, 1)] : List FactorBlock).map factorBlockValue).prod) = 96020376098014700377229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_33461
      · exact prime_seventyTwoBR_717405158976231287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 96020376098014700377229) ^ 48010188049007350188614 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 96020376098014700377229) ^ 2869620635904925148 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 96020376098014700377229) ^ 133844 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_164314988843532577151617 : Nat.Prime 164314988843532577151617 := by
  apply lucas_primality 164314988843532577151617 (5 : ZMod 164314988843532577151617)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 5), (107, 2), (1861, 1), (273601, 1), (906211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 5), (107, 2), (1861, 1), (273601, 1), (906211, 1)] : List FactorBlock).map factorBlockValue).prod) = 164314988843532577151617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_107
      · exact prime_seventyTwoBR_1861
      · exact prime_seventyTwoBR_273601
      · exact prime_seventyTwoBR_906211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 164314988843532577151617) ^ 82157494421766288575808 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 164314988843532577151617) ^ 54771662947844192383872 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 164314988843532577151617) ^ 1535654101341425954688 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 164314988843532577151617) ^ 88293922000823523456 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 164314988843532577151617) ^ 600564284646374016 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 164314988843532577151617) ^ 181320894188585856 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_206765322585934096190867 : Nat.Prime 206765322585934096190867 := by
  apply lucas_primality 206765322585934096190867 (2 : ZMod 206765322585934096190867)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (5309, 1), (1329891569, 1), (1331147143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (5309, 1), (1329891569, 1), (1331147143, 1)] : List FactorBlock).map factorBlockValue).prod) = 206765322585934096190867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_11
      · exact prime_seventyTwoBR_5309
      · exact prime_seventyTwoBR_1329891569
      · exact prime_seventyTwoBR_1331147143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 206765322585934096190867) ^ 103382661292967048095433 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 206765322585934096190867) ^ 18796847507812190562806 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 206765322585934096190867) ^ 38946189976631022074 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 206765322585934096190867) ^ 155475324008114 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 206765322585934096190867) ^ 155328675476062 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_245285706294727098438547 : Nat.Prime 245285706294727098438547 := by
  apply lucas_primality 245285706294727098438547 (2 : ZMod 245285706294727098438547)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (40499, 1), (336477040989663803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (40499, 1), (336477040989663803, 1)] : List FactorBlock).map factorBlockValue).prod) = 245285706294727098438547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_40499
      · exact prime_seventyTwoBR_336477040989663803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 245285706294727098438547) ^ 122642853147363549219273 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 245285706294727098438547) ^ 81761902098242366146182 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 245285706294727098438547) ^ 6056586737813948454 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 245285706294727098438547) ^ 728982 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_273231909840096064289303 : Nat.Prime 273231909840096064289303 := by
  apply lucas_primality 273231909840096064289303 (5 : ZMod 273231909840096064289303)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (73, 1), (8219353, 1), (17514493277783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (73, 1), (8219353, 1), (17514493277783, 1)] : List FactorBlock).map factorBlockValue).prod) = 273231909840096064289303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_13
      · exact prime_seventyTwoBR_73
      · exact prime_seventyTwoBR_8219353
      · exact prime_seventyTwoBR_17514493277783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 273231909840096064289303) ^ 136615954920048032144651 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 273231909840096064289303) ^ 21017839218468928022254 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 273231909840096064289303) ^ 3742902874521863894374 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 273231909840096064289303) ^ 33242508241232134 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 273231909840096064289303) ^ 15600331994 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_790366065824859639750959 : Nat.Prime 790366065824859639750959 := by
  apply lucas_primality 790366065824859639750959 (7 : ZMod 790366065824859639750959)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (825655997, 1), (25191008205553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (825655997, 1), (25191008205553, 1)] : List FactorBlock).map factorBlockValue).prod) = 790366065824859639750959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_19
      · exact prime_seventyTwoBR_825655997
      · exact prime_seventyTwoBR_25191008205553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 790366065824859639750959) ^ 395183032912429819875479 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 790366065824859639750959) ^ 41598213990782086302682 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 790366065824859639750959) ^ 957258311811014 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (7 : ZMod 790366065824859639750959) ^ 31374927886 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_1079175633958812445305637 : Nat.Prime 1079175633958812445305637 := by
  apply lucas_primality 1079175633958812445305637 (5 : ZMod 1079175633958812445305637)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (73, 1), (101, 1), (17573, 1), (21283, 1), (32612785729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (73, 1), (101, 1), (17573, 1), (21283, 1), (32612785729, 1)] : List FactorBlock).map factorBlockValue).prod) = 1079175633958812445305637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_73
      · exact prime_seventyTwoBR_101
      · exact prime_seventyTwoBR_17573
      · exact prime_seventyTwoBR_21283
      · exact prime_seventyTwoBR_32612785729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1079175633958812445305637) ^ 539587816979406222652818 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1079175633958812445305637) ^ 359725211319604148435212 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1079175633958812445305637) ^ 14783227862449485552132 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1079175633958812445305637) ^ 10684907266918935102036 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1079175633958812445305637) ^ 61411007452274082132 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1079175633958812445305637) ^ 50705992292384177292 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1079175633958812445305637) ^ 33090568923684 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_1306472498739977101693163 : Nat.Prime 1306472498739977101693163 := by
  apply lucas_primality 1306472498739977101693163 (2 : ZMod 1306472498739977101693163)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47716351, 1), (13689987513294731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47716351, 1), (13689987513294731, 1)] : List FactorBlock).map factorBlockValue).prod) = 1306472498739977101693163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_47716351
      · exact prime_seventyTwoBR_13689987513294731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1306472498739977101693163) ^ 653236249369988550846581 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1306472498739977101693163) ^ 27379975026589462 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1306472498739977101693163) ^ 95432702 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_3149795213890960520289289 : Nat.Prime 3149795213890960520289289 := by
  apply lucas_primality 3149795213890960520289289 (13 : ZMod 3149795213890960520289289)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (37, 1), (89, 1), (751, 1), (3011, 1), (766303515253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (37, 1), (89, 1), (751, 1), (3011, 1), (766303515253, 1)] : List FactorBlock).map factorBlockValue).prod) = 3149795213890960520289289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_23
      · exact prime_seventyTwoBR_37
      · exact prime_seventyTwoBR_89
      · exact prime_seventyTwoBR_751
      · exact prime_seventyTwoBR_3011
      · exact prime_seventyTwoBR_766303515253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 3149795213890960520289289) ^ 1574897606945480260144644 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (13 : ZMod 3149795213890960520289289) ^ 1049931737963653506763096 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (13 : ZMod 3149795213890960520289289) ^ 136947617995259153056056 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (13 : ZMod 3149795213890960520289289) ^ 85129600375431365413224 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (13 : ZMod 3149795213890960520289289) ^ 35390957459448994609992 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (13 : ZMod 3149795213890960520289289) ^ 4194134772158402823288 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (13 : ZMod 3149795213890960520289289) ^ 1046096052438047333208 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (13 : ZMod 3149795213890960520289289) ^ 4110375525096 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_3307939830389119343287531 : Nat.Prime 3307939830389119343287531 := by
  apply lucas_primality 3307939830389119343287531 (10 : ZMod 3307939830389119343287531)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (257142995393, 1), (428806784507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (257142995393, 1), (428806784507, 1)] : List FactorBlock).map factorBlockValue).prod) = 3307939830389119343287531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_257142995393
      · exact prime_seventyTwoBR_428806784507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 3307939830389119343287531) ^ 1653969915194559671643765 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (10 : ZMod 3307939830389119343287531) ^ 1102646610129706447762510 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (10 : ZMod 3307939830389119343287531) ^ 661587966077823868657506 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (10 : ZMod 3307939830389119343287531) ^ 12864203535210 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (10 : ZMod 3307939830389119343287531) ^ 7714289861790 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_4578732486439847671497931 : Nat.Prime 4578732486439847671497931 := by
  apply lucas_primality 4578732486439847671497931 (10 : ZMod 4578732486439847671497931)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (19, 1), (892540445699775374561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (19, 1), (892540445699775374561, 1)] : List FactorBlock).map factorBlockValue).prod) = 4578732486439847671497931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_19
      · exact prime_seventyTwoBR_892540445699775374561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 4578732486439847671497931) ^ 2289366243219923835748965 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (10 : ZMod 4578732486439847671497931) ^ 1526244162146615890499310 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (10 : ZMod 4578732486439847671497931) ^ 915746497287969534299586 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (10 : ZMod 4578732486439847671497931) ^ 240985920338939351131470 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (10 : ZMod 4578732486439847671497931) ^ 5130 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_8094638232731381519666987 : Nat.Prime 8094638232731381519666987 := by
  apply lucas_primality 8094638232731381519666987 (2 : ZMod 8094638232731381519666987)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (241, 1), (1352707259, 1), (335540433331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (241, 1), (1352707259, 1), (335540433331, 1)] : List FactorBlock).map factorBlockValue).prod) = 8094638232731381519666987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_37
      · exact prime_seventyTwoBR_241
      · exact prime_seventyTwoBR_1352707259
      · exact prime_seventyTwoBR_335540433331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8094638232731381519666987) ^ 4047319116365690759833493 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 8094638232731381519666987) ^ 218774006290037338369378 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 8094638232731381519666987) ^ 33587710509258844479946 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 8094638232731381519666987) ^ 5984028088025054 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 8094638232731381519666987) ^ 24124181257006 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_11172491882845938845100149 : Nat.Prime 11172491882845938845100149 := by
  apply lucas_primality 11172491882845938845100149 (2 : ZMod 11172491882845938845100149)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (75274373, 1), (1613299776822703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (75274373, 1), (1613299776822703, 1)] : List FactorBlock).map factorBlockValue).prod) = 11172491882845938845100149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_23
      · exact prime_seventyTwoBR_75274373
      · exact prime_seventyTwoBR_1613299776822703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11172491882845938845100149) ^ 5586245941422969422550074 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 11172491882845938845100149) ^ 485760516645475601960876 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 11172491882845938845100149) ^ 148423579467688676 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 11172491882845938845100149) ^ 6925242316 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_191718954178836054191031611 : Nat.Prime 191718954178836054191031611 := by
  apply lucas_primality 191718954178836054191031611 (2 : ZMod 191718954178836054191031611)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19793, 1), (33623, 1), (103201937, 1), (279144527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19793, 1), (33623, 1), (103201937, 1), (279144527, 1)] : List FactorBlock).map factorBlockValue).prod) = 191718954178836054191031611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_19793
      · exact prime_seventyTwoBR_33623
      · exact prime_seventyTwoBR_103201937
      · exact prime_seventyTwoBR_279144527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 191718954178836054191031611) ^ 95859477089418027095515805 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 191718954178836054191031611) ^ 38343790835767210838206322 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 191718954178836054191031611) ^ 9686199877675746687770 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 191718954178836054191031611) ^ 5702018088178807786070 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 191718954178836054191031611) ^ 1857706936051365530 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 191718954178836054191031611) ^ 686808930983755430 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_200762301074064169954759517 : Nat.Prime 200762301074064169954759517 := by
  apply lucas_primality 200762301074064169954759517 (2 : ZMod 200762301074064169954759517)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (31, 1), (101, 1), (942953299425405198277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (31, 1), (101, 1), (942953299425405198277, 1)] : List FactorBlock).map factorBlockValue).prod) = 200762301074064169954759517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_17
      · exact prime_seventyTwoBR_31
      · exact prime_seventyTwoBR_101
      · exact prime_seventyTwoBR_942953299425405198277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 200762301074064169954759517) ^ 100381150537032084977379758 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 200762301074064169954759517) ^ 11809547122003774703221148 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 200762301074064169954759517) ^ 6476203260453682901766436 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 200762301074064169954759517) ^ 1987745555188754157967916 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 200762301074064169954759517) ^ 212908 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_1576355845470429778904037689 : Nat.Prime 1576355845470429778904037689 := by
  apply lucas_primality 1576355845470429778904037689 (3 : ZMod 1576355845470429778904037689)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (324549103, 1), (607133031219019337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (324549103, 1), (607133031219019337, 1)] : List FactorBlock).map factorBlockValue).prod) = 1576355845470429778904037689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_324549103
      · exact prime_seventyTwoBR_607133031219019337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1576355845470429778904037689) ^ 788177922735214889452018844 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1576355845470429778904037689) ^ 4857064249752154696 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1576355845470429778904037689) ^ 2596392824 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_6080229689671657718629859663 : Nat.Prime 6080229689671657718629859663 := by
  apply lucas_primality 6080229689671657718629859663 (5 : ZMod 6080229689671657718629859663)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (19751, 1), (76557353, 1), (154657376772029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (19751, 1), (76557353, 1), (154657376772029, 1)] : List FactorBlock).map factorBlockValue).prod) = 6080229689671657718629859663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_13
      · exact prime_seventyTwoBR_19751
      · exact prime_seventyTwoBR_76557353
      · exact prime_seventyTwoBR_154657376772029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6080229689671657718629859663) ^ 3040114844835828859314929831 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 6080229689671657718629859663) ^ 467709976128589055279219974 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 6080229689671657718629859663) ^ 307844144077345841660162 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 6080229689671657718629859663) ^ 79420584064232964254 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 6080229689671657718629859663) ^ 39314191256678 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_7738474150491200732801639567 : Nat.Prime 7738474150491200732801639567 := by
  apply lucas_primality 7738474150491200732801639567 (5 : ZMod 7738474150491200732801639567)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (17, 2), (273231909840096064289303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (17, 2), (273231909840096064289303, 1)] : List FactorBlock).map factorBlockValue).prod) = 7738474150491200732801639567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_17
      · exact prime_seventyTwoBR_273231909840096064289303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7738474150491200732801639567) ^ 3869237075245600366400819783 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 7738474150491200732801639567) ^ 1105496307213028676114519938 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 7738474150491200732801639567) ^ 455204361793600043105978798 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (5 : ZMod 7738474150491200732801639567) ^ 28322 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_12160459379343315437259719317 : Nat.Prime 12160459379343315437259719317 := by
  apply lucas_primality 12160459379343315437259719317 (2 : ZMod 12160459379343315437259719317)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (41, 1), (811, 1), (10463, 1), (153304251163993169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (41, 1), (811, 1), (10463, 1), (153304251163993169, 1)] : List FactorBlock).map factorBlockValue).prod) = 12160459379343315437259719317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_19
      · exact prime_seventyTwoBR_41
      · exact prime_seventyTwoBR_811
      · exact prime_seventyTwoBR_10463
      · exact prime_seventyTwoBR_153304251163993169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12160459379343315437259719317) ^ 6080229689671657718629859658 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 12160459379343315437259719317) ^ 4053486459781105145753239772 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 12160459379343315437259719317) ^ 640024177860174496697879964 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 12160459379343315437259719317) ^ 296596570227885742372188276 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 12160459379343315437259719317) ^ 14994401207574988208704956 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 12160459379343315437259719317) ^ 1162234481443497604631532 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 12160459379343315437259719317) ^ 79322388564 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_28374405218467736020272678431 : Nat.Prime 28374405218467736020272678431 := by
  apply lucas_primality 28374405218467736020272678431 (11 : ZMod 28374405218467736020272678431)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (4133, 1), (26177, 1), (26226569552104612423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (4133, 1), (26177, 1), (26226569552104612423, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467736020272678431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_4133
      · exact prime_seventyTwoBR_26177
      · exact prime_seventyTwoBR_26226569552104612423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 28374405218467736020272678431) ^ 14187202609233868010136339215 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (11 : ZMod 28374405218467736020272678431) ^ 5674881043693547204054535686 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (11 : ZMod 28374405218467736020272678431) ^ 6865329111654424393968710 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (11 : ZMod 28374405218467736020272678431) ^ 1083944119588483631442590 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (11 : ZMod 28374405218467736020272678431) ^ 1081895410 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_42561607827701604030409017607 : Nat.Prime 42561607827701604030409017607 := by
  apply lucas_primality 42561607827701604030409017607 (3 : ZMod 42561607827701604030409017607)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (19, 1), (41, 1), (811, 1), (10463, 1), (153304251163993169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (19, 1), (41, 1), (811, 1), (10463, 1), (153304251163993169, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701604030409017607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_7
      · exact prime_seventyTwoBR_19
      · exact prime_seventyTwoBR_41
      · exact prime_seventyTwoBR_811
      · exact prime_seventyTwoBR_10463
      · exact prime_seventyTwoBR_153304251163993169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 42561607827701604030409017607) ^ 21280803913850802015204508803 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 42561607827701604030409017607) ^ 14187202609233868010136339202 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 42561607827701604030409017607) ^ 6080229689671657718629859658 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 42561607827701604030409017607) ^ 2240084622510610738442579874 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 42561607827701604030409017607) ^ 1038087995797600098302658966 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 42561607827701604030409017607) ^ 52480404226512458730467346 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 42561607827701604030409017607) ^ 4067820685052241616210362 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (3 : ZMod 42561607827701604030409017607) ^ 277628359974 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_42561607827701604030409017619 : Nat.Prime 42561607827701604030409017619 := by
  apply lucas_primality 42561607827701604030409017619 (2 : ZMod 42561607827701604030409017619)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (751, 1), (1999, 1), (1926863401, 1), (41563403633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (751, 1), (1999, 1), (1926863401, 1), (41563403633, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701604030409017619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_59
      · exact prime_seventyTwoBR_751
      · exact prime_seventyTwoBR_1999
      · exact prime_seventyTwoBR_1926863401
      · exact prime_seventyTwoBR_41563403633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 42561607827701604030409017619) ^ 21280803913850802015204508809 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 42561607827701604030409017619) ^ 14187202609233868010136339206 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 42561607827701604030409017619) ^ 721383183520366170006932502 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 42561607827701604030409017619) ^ 56673246108790418149679118 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 42561607827701604030409017619) ^ 21291449638670137083746382 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 42561607827701604030409017619) ^ 22088544421785716418 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 42561607827701604030409017619) ^ 1024016420876298546 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem prime_seventyTwoBR_85123215655403208060818035291 : Nat.Prime 85123215655403208060818035291 := by
  apply lucas_primality 85123215655403208060818035291 (2 : ZMod 85123215655403208060818035291)
  · rw [← seventyTwoBRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (4133, 1), (26177, 1), (26226569552104612423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (4133, 1), (26177, 1), (26226569552104612423, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyTwoBR_2
      · exact prime_seventyTwoBR_3
      · exact prime_seventyTwoBR_5
      · exact prime_seventyTwoBR_4133
      · exact prime_seventyTwoBR_26177
      · exact prime_seventyTwoBR_26226569552104612423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 85123215655403208060818035291) ^ 42561607827701604030409017645 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 85123215655403208060818035291) ^ 28374405218467736020272678430 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 85123215655403208060818035291) ^ 17024643131080641612163607058 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 85123215655403208060818035291) ^ 20595987334963273181906130 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 85123215655403208060818035291) ^ 3251832358765450894327770 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide
    · change (2 : ZMod 85123215655403208060818035291) ^ 3245686230 ≠ 1
      rw [← seventyTwoBRFastPow_eq_pow]
      decide

private theorem phi_seventyTwoBR_85123215655403208060818035200 : Nat.totient 85123215655403208060818035200 = 22699098709795425696800440320 := by
  rw [← show ((([(2, 9), (3, 1), (5, 2), (53359, 1), (425097209, 1), (97728416413, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035200 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_3, prime_seventyTwoBR_5, prime_seventyTwoBR_53359, prime_seventyTwoBR_425097209, prime_seventyTwoBR_97728416413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035201 : Nat.totient 85123215655403208060818035201 = 83915485252828828566916314240 := by
  rw [← show ((([(71, 1), (18793, 1), (19309, 1), (3303952358426215163, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035201 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_71, prime_seventyTwoBR_18793, prime_seventyTwoBR_19309, prime_seventyTwoBR_3303952358426215163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035202 : Nat.totient 85123215655403208060818035202 = 40711097304712601404792154704 := by
  rw [← show ((([(2, 1), (23, 1), (8607563, 1), (36838247, 1), (5835942767267, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035202 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_23, prime_seventyTwoBR_8607563, prime_seventyTwoBR_36838247, prime_seventyTwoBR_5835942767267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035203 : Nat.totient 85123215655403208060818035203 = 52383517326392839653646955520 := by
  rw [← show ((([(3, 1), (13, 1), (5823777031781, 1), (374781957371617, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035203 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_3, prime_seventyTwoBR_13, prime_seventyTwoBR_5823777031781, prime_seventyTwoBR_374781957371617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035204 : Nat.totient 85123215655403208060818035204 = 37946965751054563927443223680 := by
  rw [← show ((([(2, 2), (11, 3), (67, 1), (227, 1), (28838330863, 1), (36453496813, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035204 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_11, prime_seventyTwoBR_67, prime_seventyTwoBR_227, prime_seventyTwoBR_28838330863, prime_seventyTwoBR_36453496813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035205 : Nat.totient 85123215655403208060818035205 = 58368010427507861132102164800 := by
  rw [← show ((([(5, 1), (7, 1), (26987, 1), (1841699, 1), (48933549083352151, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035205 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_5, prime_seventyTwoBR_7, prime_seventyTwoBR_26987, prime_seventyTwoBR_1841699, prime_seventyTwoBR_48933549083352151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035206 : Nat.totient 85123215655403208060818035206 = 28374405218467736020272678384 := by
  rw [← show ((([(2, 1), (3, 3), (1576355845470429778904037689, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035206 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_3, prime_seventyTwoBR_1576355845470429778904037689]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035207 : Nat.totient 85123215655403208060818035207 = 85104038879361086679167112000 := by
  rw [← show ((([(4451, 1), (1640953, 1), (214361111, 1), (54368616979, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035207 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_4451, prime_seventyTwoBR_1640953, prime_seventyTwoBR_214361111, prime_seventyTwoBR_54368616979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035208 : Nat.totient 85123215655403208060818035208 = 41758558623405347350589979328 := by
  rw [← show ((([(2, 3), (53, 1), (200762301074064169954759517, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035208 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_53, prime_seventyTwoBR_200762301074064169954759517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035209 : Nat.totient 85123215655403208060818035209 = 53410645117021846078086608640 := by
  rw [← show ((([(3, 1), (17, 1), (568960357991, 1), (2933565821357749, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035209 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_3, prime_seventyTwoBR_17, prime_seventyTwoBR_568960357991, prime_seventyTwoBR_2933565821357749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035210 : Nat.totient 85123215655403208060818035210 = 33129035215308242695143014400 := by
  rw [← show ((([(2, 1), (5, 1), (37, 1), (495983533, 1), (463851579150316801, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035210 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_5, prime_seventyTwoBR_37, prime_seventyTwoBR_495983533, prime_seventyTwoBR_463851579150316801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035211 : Nat.totient 85123215655403208060818035211 = 82406043726269091498563249664 := by
  rw [← show ((([(43, 1), (113, 1), (46349, 1), (535375567, 1), (705995944763, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035211 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_43, prime_seventyTwoBR_113, prime_seventyTwoBR_46349, prime_seventyTwoBR_535375567, prime_seventyTwoBR_705995944763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035212 : Nat.totient 85123215655403208060818035212 = 22449034678445582701748428800 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (19, 1), (41, 1), (811, 1), (10463, 1), (153304251163993169, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035212 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_3, prime_seventyTwoBR_7, prime_seventyTwoBR_19, prime_seventyTwoBR_41, prime_seventyTwoBR_811, prime_seventyTwoBR_10463, prime_seventyTwoBR_153304251163993169]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035213 : Nat.totient 85123215655403208060818035213 = 84294297132714143265643938864 := by
  rw [← show ((([(103, 1), (33997, 1), (24309173954927264587543, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035213 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_103, prime_seventyTwoBR_33997, prime_seventyTwoBR_24309173954927264587543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035214 : Nat.totient 85123215655403208060818035214 = 42561607827701604030409017606 := by
  rw [← show ((([(2, 1), (42561607827701604030409017607, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035214 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_42561607827701604030409017607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035215 : Nat.totient 85123215655403208060818035215 = 41271595866930796135261839360 := by
  rw [← show ((([(3, 2), (5, 1), (11, 1), (155009, 1), (2886826487, 1), (384295435879, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035215 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_3, prime_seventyTwoBR_5, prime_seventyTwoBR_11, prime_seventyTwoBR_155009, prime_seventyTwoBR_2886826487, prime_seventyTwoBR_384295435879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035216 : Nat.totient 85123215655403208060818035216 = 39287446546706112409060525056 := by
  rw [← show ((([(2, 4), (13, 1), (205213, 1), (1994250993419108065129, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035216 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_13, prime_seventyTwoBR_205213, prime_seventyTwoBR_1994250993419108065129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035217 : Nat.totient 85123215655403208060818035217 = 85057584800947504962436684800 := by
  rw [← show ((([(1297, 1), (42866374921, 1), (1531056745347641, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035217 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_1297, prime_seventyTwoBR_42866374921, prime_seventyTwoBR_1531056745347641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035218 : Nat.totient 85123215655403208060818035218 = 27310128140543892865214434560 := by
  rw [← show ((([(2, 1), (3, 1), (31, 1), (317, 1), (439, 1), (1321039283, 1), (2489405028797, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035218 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_3, prime_seventyTwoBR_31, prime_seventyTwoBR_317, prime_seventyTwoBR_439, prime_seventyTwoBR_1321039283, prime_seventyTwoBR_2489405028797]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035219 : Nat.totient 85123215655403208060818035219 = 72962756276059892623558315896 := by
  rw [← show ((([(7, 1), (12160459379343315437259719317, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035219 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_7, prime_seventyTwoBR_12160459379343315437259719317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035220 : Nat.totient 85123215655403208060818035220 = 32634991715554584307022382080 := by
  rw [← show ((([(2, 2), (5, 1), (29, 1), (137, 1), (150767, 1), (7105475845583015171, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035220 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_5, prime_seventyTwoBR_29, prime_seventyTwoBR_137, prime_seventyTwoBR_150767, prime_seventyTwoBR_7105475845583015171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035221 : Nat.totient 85123215655403208060818035221 = 56739652971962592345202348560 := by
  rw [← show ((([(3, 1), (6197, 1), (4578732486439847671497931, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035221 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_3, prime_seventyTwoBR_6197, prime_seventyTwoBR_4578732486439847671497931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035222 : Nat.totient 85123215655403208060818035222 = 42498511877185368951411194880 := by
  rw [← show ((([(2, 1), (773, 1), (5333, 1), (652019, 1), (15834585403763041, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035222 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_773, prime_seventyTwoBR_5333, prime_seventyTwoBR_652019, prime_seventyTwoBR_15834585403763041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035223 : Nat.totient 85123215655403208060818035223 = 85119907715572818941474721960 := by
  rw [← show ((([(25733, 1), (3307939830389119343287531, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035223 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_25733, prime_seventyTwoBR_3307939830389119343287531]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035224 : Nat.totient 85123215655403208060818035224 = 28279863561285718109585035776 := by
  rw [← show ((([(2, 3), (3, 2), (349, 1), (2137, 1), (1585205519483868388159, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035224 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_3, prime_seventyTwoBR_349, prime_seventyTwoBR_2137, prime_seventyTwoBR_1585205519483868388159]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035225 : Nat.totient 85123215655403208060818035225 = 63751855129153040930655189120 := by
  rw [← show ((([(5, 2), (23, 1), (47, 1), (3149795213890960520289289, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035225 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_5, prime_seventyTwoBR_23, prime_seventyTwoBR_47, prime_seventyTwoBR_3149795213890960520289289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035226 : Nat.totient 85123215655403208060818035226 = 31214013380132574384409860480 := by
  rw [← show ((([(2, 1), (7, 2), (11, 1), (17, 2), (273231909840096064289303, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035226 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_7, prime_seventyTwoBR_11, prime_seventyTwoBR_17, prime_seventyTwoBR_273231909840096064289303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035227 : Nat.totient 85123215655403208060818035227 = 56665715702270261087494637952 := by
  rw [← show ((([(3, 1), (683, 1), (7909259, 1), (5252550851214373297, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035227 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_3, prime_seventyTwoBR_683, prime_seventyTwoBR_7909259, prime_seventyTwoBR_5252550851214373297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035228 : Nat.totient 85123215655403208060818035228 = 42561601981550951328540032192 := by
  rw [← show ((([(2, 2), (7280279, 1), (2923075326350927212433, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035228 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_7280279, prime_seventyTwoBR_2923075326350927212433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035229 : Nat.totient 85123215655403208060818035229 = 78269532279951315999115689984 := by
  rw [← show ((([(13, 2), (257, 1), (37145327, 1), (69516613, 1), (758988863, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035229 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_13, prime_seventyTwoBR_257, prime_seventyTwoBR_37145327, prime_seventyTwoBR_69516613, prime_seventyTwoBR_758988863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035230 : Nat.totient 85123215655403208060818035230 = 22697870052193501343448506016 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (13723, 1), (206765322585934096190867, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035230 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_3, prime_seventyTwoBR_5, prime_seventyTwoBR_13723, prime_seventyTwoBR_206765322585934096190867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035231 : Nat.totient 85123215655403208060818035231 = 80441941556490759684721065600 := by
  rw [← show ((([(19, 1), (401, 1), (11172491882845938845100149, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035231 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_19, prime_seventyTwoBR_401, prime_seventyTwoBR_11172491882845938845100149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035232 : Nat.totient 85123215655403208060818035232 = 42561108530306771591333120832 := by
  rw [← show ((([(2, 5), (85243, 1), (31206087177027442158307, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035232 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_85243, prime_seventyTwoBR_31206087177027442158307]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035233 : Nat.totient 85123215655403208060818035233 = 48624091498578160230706206720 := by
  rw [← show ((([(3, 3), (7, 1), (2741, 1), (164314988843532577151617, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035233 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_3, prime_seventyTwoBR_7, prime_seventyTwoBR_2741, prime_seventyTwoBR_164314988843532577151617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035234 : Nat.totient 85123215655403208060818035234 = 42526674089900787820466697600 := by
  rw [← show ((([(2, 1), (1559, 1), (5573, 1), (44986441, 1), (108893318030291, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035234 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_1559, prime_seventyTwoBR_5573, prime_seventyTwoBR_44986441, prime_seventyTwoBR_108893318030291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035235 : Nat.totient 85123215655403208060818035235 = 67471596924896735870846976000 := by
  rw [← show ((([(5, 1), (173, 1), (313, 1), (4111, 1), (111893, 1), (5449541, 1), (125423021, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035235 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_5, prime_seventyTwoBR_173, prime_seventyTwoBR_313, prime_seventyTwoBR_4111, prime_seventyTwoBR_111893, prime_seventyTwoBR_5449541, prime_seventyTwoBR_125423021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035236 : Nat.totient 85123215655403208060818035236 = 27842406154368099444057600000 := by
  rw [← show ((([(2, 2), (3, 1), (59, 1), (751, 1), (1999, 1), (1926863401, 1), (41563403633, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035236 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_3, prime_seventyTwoBR_59, prime_seventyTwoBR_751, prime_seventyTwoBR_1999, prime_seventyTwoBR_1926863401, prime_seventyTwoBR_41563403633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035237 : Nat.totient 85123215655403208060818035237 = 77384741504912007328016395660 := by
  rw [← show ((([(11, 1), (7738474150491200732801639567, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035237 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_11, prime_seventyTwoBR_7738474150491200732801639567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035238 : Nat.totient 85123215655403208060818035238 = 42561607827701604030409017618 := by
  rw [← show ((([(2, 1), (42561607827701604030409017619, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035238 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_42561607827701604030409017619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035239 : Nat.totient 85123215655403208060818035239 = 56748319865522882586348248376 := by
  rw [← show ((([(3, 1), (115679, 1), (245285706294727098438547, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035239 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_3, prime_seventyTwoBR_115679, prime_seventyTwoBR_245285706294727098438547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035240 : Nat.totient 85123215655403208060818035240 = 29182174337201279818856560128 := by
  rw [← show ((([(2, 3), (5, 1), (7, 1), (9967, 1), (30501804402887818393849, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035240 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_5, prime_seventyTwoBR_7, prime_seventyTwoBR_9967, prime_seventyTwoBR_30501804402887818393849]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035241 : Nat.totient 85123215655403208060818035241 = 85123193342236076414505854400 := by
  rw [← show ((([(10622747, 1), (10864429, 1), (21161051, 1), (34855157, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035241 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_10622747, prime_seventyTwoBR_10864429, prime_seventyTwoBR_21161051, prime_seventyTwoBR_34855157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035242 : Nat.totient 85123215655403208060818035242 = 26191758660370171177664234880 := by
  rw [← show ((([(2, 1), (3, 2), (13, 1), (9252373021, 1), (39316878497239253, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035242 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_3, prime_seventyTwoBR_13, prime_seventyTwoBR_9252373021, prime_seventyTwoBR_39316878497239253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035243 : Nat.totient 85123215655403208060818035243 = 79288663525388507605662535680 := by
  rw [← show ((([(17, 1), (97, 1), (58031, 1), (889543747188376293397, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035243 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_17, prime_seventyTwoBR_97, prime_seventyTwoBR_58031, prime_seventyTwoBR_889543747188376293397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035244 : Nat.totient 85123215655403208060818035244 = 42515759262847442197209552896 := by
  rw [← show ((([(2, 2), (929, 1), (1245617, 1), (18390256610937363227, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035244 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_929, prime_seventyTwoBR_1245617, prime_seventyTwoBR_18390256610937363227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035245 : Nat.totient 85123215655403208060818035245 = 45398781197319318931989275904 := by
  rw [← show ((([(3, 1), (5, 1), (169937, 1), (33394028632337555706259, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035245 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_3, prime_seventyTwoBR_5, prime_seventyTwoBR_169937, prime_seventyTwoBR_33394028632337555706259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035246 : Nat.totient 85123215655403208060818035246 = 42447809603550668717611008000 := by
  rw [← show ((([(2, 1), (421, 1), (3361, 1), (624797, 1), (94427569, 1), (509835031, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035246 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_421, prime_seventyTwoBR_3361, prime_seventyTwoBR_624797, prime_seventyTwoBR_94427569, prime_seventyTwoBR_509835031]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035247 : Nat.totient 85123215655403208060818035247 = 70990789876603768105275403008 := by
  rw [← show ((([(7, 1), (37, 1), (5213521837, 1), (63040124235040409, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035247 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_7, prime_seventyTwoBR_37, prime_seventyTwoBR_5213521837, prime_seventyTwoBR_63040124235040409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035248 : Nat.totient 85123215655403208060818035248 = 24335404118280845663604664320 := by
  rw [← show ((([(2, 4), (3, 1), (11, 1), (23, 1), (73, 1), (96020376098014700377229, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035248 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_3, prime_seventyTwoBR_11, prime_seventyTwoBR_23, prime_seventyTwoBR_73, prime_seventyTwoBR_96020376098014700377229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035249 : Nat.totient 85123215655403208060818035249 = 79536660689503703410612238400 := by
  rw [← show ((([(29, 2), (31, 1), (1655531, 1), (1972209354371518949, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035249 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_29, prime_seventyTwoBR_31, prime_seventyTwoBR_1655531, prime_seventyTwoBR_1972209354371518949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035250 : Nat.totient 85123215655403208060818035250 = 32189701756249499908722048000 := by
  rw [← show ((([(2, 1), (5, 3), (19, 1), (739, 1), (1361, 1), (162623, 1), (109564504670267, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035250 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_5, prime_seventyTwoBR_19, prime_seventyTwoBR_739, prime_seventyTwoBR_1361, prime_seventyTwoBR_162623, prime_seventyTwoBR_109564504670267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035251 : Nat.totient 85123215655403208060818035251 = 55818502004387216148792359040 := by
  rw [← show ((([(3, 2), (61, 1), (862332943, 1), (179804559126573593, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035251 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_3, prime_seventyTwoBR_61, prime_seventyTwoBR_862332943, prime_seventyTwoBR_179804559126573593]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035252 : Nat.totient 85123215655403208060818035252 = 42521380606779011133498473472 := by
  rw [← show ((([(2, 2), (1063, 1), (226099, 1), (3854434097, 1), (22971825017, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035252 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_1063, prime_seventyTwoBR_226099, prime_seventyTwoBR_3854434097, prime_seventyTwoBR_22971825017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035253 : Nat.totient 85123215655403208060818035253 = 83016152603247072398192640000 := by
  rw [← show ((([(41, 1), (3511, 1), (14797, 1), (51521, 1), (7774579, 1), (99769661, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035253 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_41, prime_seventyTwoBR_3511, prime_seventyTwoBR_14797, prime_seventyTwoBR_51521, prime_seventyTwoBR_7774579, prime_seventyTwoBR_99769661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035254 : Nat.totient 85123215655403208060818035254 = 23732815500089944857763056000 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (43, 1), (1061, 1), (213919, 1), (207666064086254551, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035254 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_3, prime_seventyTwoBR_7, prime_seventyTwoBR_43, prime_seventyTwoBR_1061, prime_seventyTwoBR_213919, prime_seventyTwoBR_207666064086254551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035255 : Nat.totient 85123215655403208060818035255 = 62791358275290369032754647040 := by
  rw [← show ((([(5, 1), (13, 1), (1087, 1), (5741, 1), (666937, 1), (314653641426613, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035255 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_5, prime_seventyTwoBR_13, prime_seventyTwoBR_1087, prime_seventyTwoBR_5741, prime_seventyTwoBR_666937, prime_seventyTwoBR_314653641426613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035256 : Nat.totient 85123215655403208060818035256 = 42083387514580348590452553216 := by
  rw [← show ((([(2, 3), (89, 1), (93431848567, 1), (1279596625790489, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035256 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_89, prime_seventyTwoBR_93431848567, prime_seventyTwoBR_1279596625790489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035257 : Nat.totient 85123215655403208060818035257 = 56747389186752885061691398400 := by
  rw [← show ((([(3, 1), (39929, 1), (7865448131, 1), (90347234100281, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035257 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_3, prime_seventyTwoBR_39929, prime_seventyTwoBR_7865448131, prime_seventyTwoBR_90347234100281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035258 : Nat.totient 85123215655403208060818035258 = 42561607565257823270448855420 := by
  rw [← show ((([(2, 1), (162174191, 1), (262443780759797988019, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035258 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_162174191, prime_seventyTwoBR_262443780759797988019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035259 : Nat.totient 85123215655403208060818035259 = 77376837844253758731618788200 := by
  rw [← show ((([(11, 1), (9791, 1), (790366065824859639750959, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035259 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_11, prime_seventyTwoBR_9791, prime_seventyTwoBR_790366065824859639750959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035260 : Nat.totient 85123215655403208060818035260 = 21364197414713386620455190528 := by
  rw [← show ((([(2, 2), (3, 5), (5, 1), (17, 1), (352883, 1), (241897979, 1), (12069793889, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035260 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_3, prime_seventyTwoBR_5, prime_seventyTwoBR_17, prime_seventyTwoBR_352883, prime_seventyTwoBR_241897979, prime_seventyTwoBR_12069793889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035261 : Nat.totient 85123215655403208060818035261 = 71585662546103811575536594944 := by
  rw [← show ((([(7, 1), (53, 1), (163909, 1), (59249473, 1), (23625816104963, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035261 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_7, prime_seventyTwoBR_53, prime_seventyTwoBR_163909, prime_seventyTwoBR_59249473, prime_seventyTwoBR_23625816104963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035262 : Nat.totient 85123215655403208060818035262 = 42561606122692255191606685728 := by
  rw [← show ((([(2, 1), (27222109, 1), (300773807, 1), (5198239012037, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035262 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_27222109, prime_seventyTwoBR_300773807, prime_seventyTwoBR_5198239012037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035263 : Nat.totient 85123215655403208060818035263 = 56748810436922064469662582488 := by
  rw [← show ((([(3, 1), (4235270203739, 1), (6699550171183439, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035263 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_3, prime_seventyTwoBR_4235270203739, prime_seventyTwoBR_6699550171183439]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035264 : Nat.totient 85123215655403208060818035264 = 42560287431255424071934318080 := by
  rw [← show ((([(2, 6), (44839, 1), (114661, 1), (258699985223221219, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035264 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_44839, prime_seventyTwoBR_114661, prime_seventyTwoBR_258699985223221219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035265 : Nat.totient 85123215655403208060818035265 = 66849584815527148339435713216 := by
  rw [← show ((([(5, 1), (83, 1), (157, 1), (1306472498739977101693163, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035265 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_5, prime_seventyTwoBR_83, prime_seventyTwoBR_157, prime_seventyTwoBR_1306472498739977101693163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035266 : Nat.totient 85123215655403208060818035266 = 28321957149611105792223466560 := by
  rw [← show ((([(2, 1), (3, 1), (541, 1), (468634028243, 1), (55958451195197, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035266 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_3, prime_seventyTwoBR_541, prime_seventyTwoBR_468634028243, prime_seventyTwoBR_55958451195197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035267 : Nat.totient 85123215655403208060818035267 = 85123215655350020471746739160 := by
  rw [← show ((([(1600481967397, 1), (53185988589328711, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035267 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_1600481967397, prime_seventyTwoBR_53185988589328711]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035268 : Nat.totient 85123215655403208060818035268 = 33673412858460801718990464000 := by
  rw [← show ((([(2, 2), (7, 1), (13, 1), (19751, 1), (76557353, 1), (154657376772029, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035268 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_7, prime_seventyTwoBR_13, prime_seventyTwoBR_19751, prime_seventyTwoBR_76557353, prime_seventyTwoBR_154657376772029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035269 : Nat.totient 85123215655403208060818035269 = 53754156027270879392795103648 := by
  rw [← show ((([(3, 2), (19, 1), (6827, 1), (72915860960910461352557, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035269 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_3, prime_seventyTwoBR_19, prime_seventyTwoBR_6827, prime_seventyTwoBR_72915860960910461352557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035270 : Nat.totient 85123215655403208060818035270 = 30950457662224555758344160000 := by
  rw [← show ((([(2, 1), (5, 1), (11, 1), (9001, 1), (85973493506179321550957, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035270 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_5, prime_seventyTwoBR_11, prime_seventyTwoBR_9001, prime_seventyTwoBR_85973493506179321550957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035271 : Nat.totient 85123215655403208060818035271 = 80206948671507502936719566400 := by
  rw [← show ((([(23, 1), (67, 1), (100580761, 1), (549199920203943571, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035271 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_23, prime_seventyTwoBR_67, prime_seventyTwoBR_100580761, prime_seventyTwoBR_549199920203943571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035272 : Nat.totient 85123215655403208060818035272 = 27032981244695480207914924800 := by
  rw [← show ((([(2, 3), (3, 1), (47, 1), (71, 1), (79, 1), (13454063766471313210661, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035272 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_3, prime_seventyTwoBR_47, prime_seventyTwoBR_71, prime_seventyTwoBR_79, prime_seventyTwoBR_13454063766471313210661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035273 : Nat.totient 85123215655403208060818035273 = 85123174847886712752424338624 := by
  rw [← show ((([(2261887, 1), (26820593, 1), (1403164992731303, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035273 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2261887, prime_seventyTwoBR_26820593, prime_seventyTwoBR_1403164992731303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035274 : Nat.totient 85123215655403208060818035274 = 42166343820172218204355256880 := by
  rw [← show ((([(2, 1), (109, 1), (8803, 1), (44356863149970354174931, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035274 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_109, prime_seventyTwoBR_8803, prime_seventyTwoBR_44356863149970354174931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035275 : Nat.totient 85123215655403208060818035275 = 38909267326069830300872217600 := by
  rw [← show ((([(3, 1), (5, 2), (7, 2), (10159, 1), (104527, 1), (21812790670809041, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035275 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_3, prime_seventyTwoBR_5, prime_seventyTwoBR_7, prime_seventyTwoBR_10159, prime_seventyTwoBR_104527, prime_seventyTwoBR_21812790670809041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035276 : Nat.totient 85123215655403208060818035276 = 42561594992696708848683847392 := by
  rw [← show ((([(2, 2), (3316057, 1), (6417502447590859269067, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035276 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_3316057, prime_seventyTwoBR_6417502447590859269067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035277 : Nat.totient 85123215655403208060818035277 = 80115967675468484336657727424 := by
  rw [← show ((([(17, 1), (390586677059, 1), (12819812537981759, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035277 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_17, prime_seventyTwoBR_390586677059, prime_seventyTwoBR_12819812537981759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035278 : Nat.totient 85123215655403208060818035278 = 27057946300039450947622141440 := by
  rw [← show ((([(2, 1), (3, 2), (29, 1), (107, 1), (331, 1), (133592203, 1), (34465504125049, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035278 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_3, prime_seventyTwoBR_29, prime_seventyTwoBR_107, prime_seventyTwoBR_331, prime_seventyTwoBR_133592203, prime_seventyTwoBR_34465504125049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035279 : Nat.totient 85123215655403208060818035279 = 85123215424732401708174302440 := by
  rw [← show ((([(369024659, 1), (230670806352274708181, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035279 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_369024659, prime_seventyTwoBR_230670806352274708181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035280 : Nat.totient 85123215655403208060818035280 = 32615312221587275404443648000 := by
  rw [← show ((([(2, 4), (5, 1), (31, 1), (131, 1), (389, 1), (2027569, 1), (332200132244641, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035280 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_5, prime_seventyTwoBR_31, prime_seventyTwoBR_131, prime_seventyTwoBR_389, prime_seventyTwoBR_2027569, prime_seventyTwoBR_332200132244641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035281 : Nat.totient 85123215655403208060818035281 = 47444346448278354182818356480 := by
  rw [← show ((([(3, 1), (11, 1), (13, 1), (269, 1), (26516779, 1), (27817473315656539, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035281 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_3, prime_seventyTwoBR_11, prime_seventyTwoBR_13, prime_seventyTwoBR_269, prime_seventyTwoBR_26516779, prime_seventyTwoBR_27817473315656539]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035282 : Nat.totient 85123215655403208060818035282 = 36481378138029946311779157972 := by
  rw [← show ((([(2, 1), (7, 1), (6080229689671657718629859663, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035282 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_7, prime_seventyTwoBR_6080229689671657718629859663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035283 : Nat.totient 85123215655403208060818035283 = 84649704395402406673294156800 := by
  rw [← show ((([(181, 1), (26321, 1), (78624367, 1), (227253143493049, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035283 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_181, prime_seventyTwoBR_26321, prime_seventyTwoBR_78624367, prime_seventyTwoBR_227253143493049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035284 : Nat.totient 85123215655403208060818035284 = 27607529401752391803508551840 := by
  rw [← show ((([(2, 2), (3, 1), (37, 1), (191718954178836054191031611, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035284 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_3, prime_seventyTwoBR_37, prime_seventyTwoBR_191718954178836054191031611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035285 : Nat.totient 85123215655403208060818035285 = 68098498301789862635182496256 := by
  rw [← show ((([(5, 1), (1196519, 1), (3934369, 1), (3616457187859687, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035285 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_5, prime_seventyTwoBR_1196519, prime_seventyTwoBR_3934369, prime_seventyTwoBR_3616457187859687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035286 : Nat.totient 85123215655403208060818035286 = 42560528652067645217963672568 := by
  rw [← show ((([(2, 1), (39439, 1), (1079175633958812445305637, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035286 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_39439, prime_seventyTwoBR_1079175633958812445305637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035287 : Nat.totient 85123215655403208060818035287 = 56748810436260978123805105152 := by
  rw [← show ((([(3, 3), (84135581429, 1), (37471800127765889, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035287 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_3, prime_seventyTwoBR_84135581429, prime_seventyTwoBR_37471800127765889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035288 : Nat.totient 85123215655403208060818035288 = 39846635428888196258507587584 := by
  rw [← show ((([(2, 3), (19, 1), (197, 1), (293, 1), (307, 1), (13003, 1), (2430460956692609, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035288 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_19, prime_seventyTwoBR_197, prime_seventyTwoBR_293, prime_seventyTwoBR_307, prime_seventyTwoBR_13003, prime_seventyTwoBR_2430460956692609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035289 : Nat.totient 85123215655403208060818035289 = 71861877383591505318150240000 := by
  rw [← show ((([(7, 1), (101, 1), (223, 1), (2371, 1), (2971, 1), (76646007751338589, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035289 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_7, prime_seventyTwoBR_101, prime_seventyTwoBR_223, prime_seventyTwoBR_2371, prime_seventyTwoBR_2971, prime_seventyTwoBR_76646007751338589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035290 : Nat.totient 85123215655403208060818035290 = 22693164966001750905769439232 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (4133, 1), (26177, 1), (26226569552104612423, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035290 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_3, prime_seventyTwoBR_5, prime_seventyTwoBR_4133, prime_seventyTwoBR_26177, prime_seventyTwoBR_26226569552104612423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035291 : Nat.totient 85123215655403208060818035291 = 85123215655403208060818035290 := by
  rw [← show ((([(85123215655403208060818035291, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035291 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_85123215655403208060818035291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035292 : Nat.totient 85123215655403208060818035292 = 38530477987801376033614853360 := by
  rw [← show ((([(2, 2), (11, 1), (239, 1), (8094638232731381519666987, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035292 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_11, prime_seventyTwoBR_239, prime_seventyTwoBR_8094638232731381519666987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035293 : Nat.totient 85123215655403208060818035293 = 56748810436935472040545356860 := by
  rw [← show ((([(3, 1), (28374405218467736020272678431, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035293 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_3, prime_seventyTwoBR_28374405218467736020272678431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035294 : Nat.totient 85123215655403208060818035294 = 34401182921624037308120432640 := by
  rw [← show ((([(2, 1), (13, 1), (17, 1), (23, 1), (41, 1), (383, 1), (2617, 1), (19069, 1), (1187089, 1), (9001199, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035294 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_13, prime_seventyTwoBR_17, prime_seventyTwoBR_23, prime_seventyTwoBR_41, prime_seventyTwoBR_383, prime_seventyTwoBR_2617, prime_seventyTwoBR_19069, prime_seventyTwoBR_1187089, prime_seventyTwoBR_9001199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035295 : Nat.totient 85123215655403208060818035295 = 66939140586630534411538065024 := by
  rw [← show ((([(5, 1), (59, 1), (12829, 1), (104842123, 1), (214534624085303, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035295 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_5, prime_seventyTwoBR_59, prime_seventyTwoBR_12829, prime_seventyTwoBR_104842123, prime_seventyTwoBR_214534624085303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035296 : Nat.totient 85123215655403208060818035296 = 24320918757963296184733919232 := by
  rw [← show ((([(2, 5), (3, 2), (7, 1), (33624227237, 1), (1255755767761513, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035296 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_3, prime_seventyTwoBR_7, prime_seventyTwoBR_33624227237, prime_seventyTwoBR_1255755767761513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035297 : Nat.totient 85123215655403208060818035297 = 83142725889302306479326799872 := by
  rw [← show ((([(43, 1), (94687, 1), (41348669, 1), (505623993688193, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035297 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_43, prime_seventyTwoBR_94687, prime_seventyTwoBR_41348669, prime_seventyTwoBR_505623993688193]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035298 : Nat.totient 85123215655403208060818035298 = 42561607827700328552679314164 := by
  rw [← show ((([(2, 1), (34291061048723, 1), (1241186668654763, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035298 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_34291061048723, prime_seventyTwoBR_1241186668654763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035299 : Nat.totient 85123215655403208060818035299 = 56444888080730458380783872160 := by
  rw [← show ((([(3, 1), (199, 1), (3011, 1), (47354683110784303483997, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035299 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_3, prime_seventyTwoBR_199, prime_seventyTwoBR_3011, prime_seventyTwoBR_47354683110784303483997]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035300 : Nat.totient 85123215655403208060818035300 = 34049286262132817817013676320 := by
  rw [← show ((([(2, 2), (5, 2), (1198181055347, 1), (710437001783099, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035300 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_2, prime_seventyTwoBR_5, prime_seventyTwoBR_1198181055347, prime_seventyTwoBR_710437001783099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyTwoBR_85123215655403208060818035301 : Nat.totient 85123215655403208060818035301 = 85122801873800542372679873440 := by
  rw [← show ((([(205721, 1), (50423032727, 1), (8206168525403, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403208060818035301 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyTwoBR_205721, prime_seventyTwoBR_50423032727, prime_seventyTwoBR_8206168525403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64SeventyTwoBR : certifiedKill 1 85123215655403208060818035199 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_seventyTwoBR_85123215655403208060818035200, phi_seventyTwoBR_85123215655403208060818035201, phi_seventyTwoBR_85123215655403208060818035202,
    phi_seventyTwoBR_85123215655403208060818035203, phi_seventyTwoBR_85123215655403208060818035204, phi_seventyTwoBR_85123215655403208060818035205,
    phi_seventyTwoBR_85123215655403208060818035206, phi_seventyTwoBR_85123215655403208060818035207, phi_seventyTwoBR_85123215655403208060818035208,
    phi_seventyTwoBR_85123215655403208060818035209, phi_seventyTwoBR_85123215655403208060818035210, phi_seventyTwoBR_85123215655403208060818035211,
    phi_seventyTwoBR_85123215655403208060818035212, phi_seventyTwoBR_85123215655403208060818035213, phi_seventyTwoBR_85123215655403208060818035214,
    phi_seventyTwoBR_85123215655403208060818035215, phi_seventyTwoBR_85123215655403208060818035216, phi_seventyTwoBR_85123215655403208060818035217,
    phi_seventyTwoBR_85123215655403208060818035218, phi_seventyTwoBR_85123215655403208060818035219, phi_seventyTwoBR_85123215655403208060818035220,
    phi_seventyTwoBR_85123215655403208060818035221, phi_seventyTwoBR_85123215655403208060818035222, phi_seventyTwoBR_85123215655403208060818035223,
    phi_seventyTwoBR_85123215655403208060818035224, phi_seventyTwoBR_85123215655403208060818035225, phi_seventyTwoBR_85123215655403208060818035226,
    phi_seventyTwoBR_85123215655403208060818035227, phi_seventyTwoBR_85123215655403208060818035228, phi_seventyTwoBR_85123215655403208060818035229,
    phi_seventyTwoBR_85123215655403208060818035230, phi_seventyTwoBR_85123215655403208060818035231, phi_seventyTwoBR_85123215655403208060818035232,
    phi_seventyTwoBR_85123215655403208060818035233, phi_seventyTwoBR_85123215655403208060818035234, phi_seventyTwoBR_85123215655403208060818035235,
    phi_seventyTwoBR_85123215655403208060818035236, phi_seventyTwoBR_85123215655403208060818035237, phi_seventyTwoBR_85123215655403208060818035238,
    phi_seventyTwoBR_85123215655403208060818035239, phi_seventyTwoBR_85123215655403208060818035240, phi_seventyTwoBR_85123215655403208060818035241,
    phi_seventyTwoBR_85123215655403208060818035242, phi_seventyTwoBR_85123215655403208060818035243, phi_seventyTwoBR_85123215655403208060818035244,
    phi_seventyTwoBR_85123215655403208060818035245, phi_seventyTwoBR_85123215655403208060818035246, phi_seventyTwoBR_85123215655403208060818035247,
    phi_seventyTwoBR_85123215655403208060818035248, phi_seventyTwoBR_85123215655403208060818035249, phi_seventyTwoBR_85123215655403208060818035250,
    phi_seventyTwoBR_85123215655403208060818035251, phi_seventyTwoBR_85123215655403208060818035252, phi_seventyTwoBR_85123215655403208060818035253,
    phi_seventyTwoBR_85123215655403208060818035254, phi_seventyTwoBR_85123215655403208060818035255, phi_seventyTwoBR_85123215655403208060818035256,
    phi_seventyTwoBR_85123215655403208060818035257, phi_seventyTwoBR_85123215655403208060818035258, phi_seventyTwoBR_85123215655403208060818035259,
    phi_seventyTwoBR_85123215655403208060818035260, phi_seventyTwoBR_85123215655403208060818035261, phi_seventyTwoBR_85123215655403208060818035262,
    phi_seventyTwoBR_85123215655403208060818035263, phi_seventyTwoBR_85123215655403208060818035264, phi_seventyTwoBR_85123215655403208060818035265,
    phi_seventyTwoBR_85123215655403208060818035266, phi_seventyTwoBR_85123215655403208060818035267, phi_seventyTwoBR_85123215655403208060818035268,
    phi_seventyTwoBR_85123215655403208060818035269, phi_seventyTwoBR_85123215655403208060818035270, phi_seventyTwoBR_85123215655403208060818035271,
    phi_seventyTwoBR_85123215655403208060818035272, phi_seventyTwoBR_85123215655403208060818035273, phi_seventyTwoBR_85123215655403208060818035274,
    phi_seventyTwoBR_85123215655403208060818035275, phi_seventyTwoBR_85123215655403208060818035276, phi_seventyTwoBR_85123215655403208060818035277,
    phi_seventyTwoBR_85123215655403208060818035278, phi_seventyTwoBR_85123215655403208060818035279, phi_seventyTwoBR_85123215655403208060818035280,
    phi_seventyTwoBR_85123215655403208060818035281, phi_seventyTwoBR_85123215655403208060818035282, phi_seventyTwoBR_85123215655403208060818035283,
    phi_seventyTwoBR_85123215655403208060818035284, phi_seventyTwoBR_85123215655403208060818035285, phi_seventyTwoBR_85123215655403208060818035286,
    phi_seventyTwoBR_85123215655403208060818035287, phi_seventyTwoBR_85123215655403208060818035288, phi_seventyTwoBR_85123215655403208060818035289,
    phi_seventyTwoBR_85123215655403208060818035290, phi_seventyTwoBR_85123215655403208060818035291, phi_seventyTwoBR_85123215655403208060818035292,
    phi_seventyTwoBR_85123215655403208060818035293, phi_seventyTwoBR_85123215655403208060818035294, phi_seventyTwoBR_85123215655403208060818035295,
    phi_seventyTwoBR_85123215655403208060818035296, phi_seventyTwoBR_85123215655403208060818035297, phi_seventyTwoBR_85123215655403208060818035298,
    phi_seventyTwoBR_85123215655403208060818035299, phi_seventyTwoBR_85123215655403208060818035300, phi_seventyTwoBR_85123215655403208060818035301]

end TotientTailPeriodKiller
end Erdos249257
