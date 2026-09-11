import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredOneCUFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredOneCUFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredOneCUFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredOneCUFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredOneCUFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredOneCUFastPow a n * oneHundredOneCUFastPow a n * a else oneHundredOneCUFastPow a n * oneHundredOneCUFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredOneCU_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredOneCU_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredOneCU_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredOneCU_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredOneCU_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredOneCU_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredOneCU_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredOneCU_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredOneCU_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredOneCU_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredOneCU_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredOneCU_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredOneCU_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredOneCU_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredOneCU_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredOneCU_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredOneCU_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredOneCU_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredOneCU_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredOneCU_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredOneCU_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredOneCU_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredOneCU_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredOneCU_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredOneCU_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredOneCU_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredOneCU_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredOneCU_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredOneCU_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredOneCU_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredOneCU_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredOneCU_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredOneCU_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredOneCU_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredOneCU_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredOneCU_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredOneCU_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredOneCU_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredOneCU_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredOneCU_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredOneCU_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredOneCU_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredOneCU_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredOneCU_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredOneCU_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredOneCU_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredOneCU_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredOneCU_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredOneCU_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredOneCU_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredOneCU_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredOneCU_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredOneCU_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredOneCU_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredOneCU_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredOneCU_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredOneCU_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredOneCU_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredOneCU_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredOneCU_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredOneCU_331 : Nat.Prime 331 := by norm_num

private theorem prime_oneHundredOneCU_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredOneCU_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredOneCU_367 : Nat.Prime 367 := by norm_num

private theorem prime_oneHundredOneCU_373 : Nat.Prime 373 := by norm_num

private theorem prime_oneHundredOneCU_379 : Nat.Prime 379 := by norm_num

private theorem prime_oneHundredOneCU_401 : Nat.Prime 401 := by norm_num

private theorem prime_oneHundredOneCU_409 : Nat.Prime 409 := by norm_num

private theorem prime_oneHundredOneCU_419 : Nat.Prime 419 := by norm_num

private theorem prime_oneHundredOneCU_421 : Nat.Prime 421 := by norm_num

private theorem prime_oneHundredOneCU_431 : Nat.Prime 431 := by norm_num

private theorem prime_oneHundredOneCU_433 : Nat.Prime 433 := by norm_num

private theorem prime_oneHundredOneCU_439 : Nat.Prime 439 := by norm_num

private theorem prime_oneHundredOneCU_449 : Nat.Prime 449 := by norm_num

private theorem prime_oneHundredOneCU_457 : Nat.Prime 457 := by norm_num

private theorem prime_oneHundredOneCU_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredOneCU_463 : Nat.Prime 463 := by norm_num

private theorem prime_oneHundredOneCU_503 : Nat.Prime 503 := by norm_num

private theorem prime_oneHundredOneCU_509 : Nat.Prime 509 := by norm_num

private theorem prime_oneHundredOneCU_521 : Nat.Prime 521 := by norm_num

private theorem prime_oneHundredOneCU_563 : Nat.Prime 563 := by norm_num

private theorem prime_oneHundredOneCU_587 : Nat.Prime 587 := by norm_num

private theorem prime_oneHundredOneCU_607 : Nat.Prime 607 := by norm_num

private theorem prime_oneHundredOneCU_619 : Nat.Prime 619 := by norm_num

private theorem prime_oneHundredOneCU_647 : Nat.Prime 647 := by norm_num

private theorem prime_oneHundredOneCU_653 : Nat.Prime 653 := by norm_num

private theorem prime_oneHundredOneCU_659 : Nat.Prime 659 := by norm_num

private theorem prime_oneHundredOneCU_673 : Nat.Prime 673 := by norm_num

private theorem prime_oneHundredOneCU_677 : Nat.Prime 677 := by norm_num

private theorem prime_oneHundredOneCU_701 : Nat.Prime 701 := by norm_num

private theorem prime_oneHundredOneCU_709 : Nat.Prime 709 := by norm_num

private theorem prime_oneHundredOneCU_733 : Nat.Prime 733 := by norm_num

private theorem prime_oneHundredOneCU_743 : Nat.Prime 743 := by norm_num

private theorem prime_oneHundredOneCU_751 : Nat.Prime 751 := by norm_num

private theorem prime_oneHundredOneCU_757 : Nat.Prime 757 := by norm_num

private theorem prime_oneHundredOneCU_769 : Nat.Prime 769 := by norm_num

private theorem prime_oneHundredOneCU_797 : Nat.Prime 797 := by norm_num

private theorem prime_oneHundredOneCU_827 : Nat.Prime 827 := by norm_num

private theorem prime_oneHundredOneCU_859 : Nat.Prime 859 := by norm_num

private theorem prime_oneHundredOneCU_911 : Nat.Prime 911 := by norm_num

private theorem prime_oneHundredOneCU_919 : Nat.Prime 919 := by norm_num

private theorem prime_oneHundredOneCU_947 : Nat.Prime 947 := by norm_num

private theorem prime_oneHundredOneCU_971 : Nat.Prime 971 := by norm_num

private theorem prime_oneHundredOneCU_977 : Nat.Prime 977 := by norm_num

private theorem prime_oneHundredOneCU_1021 : Nat.Prime 1021 := by norm_num

private theorem prime_oneHundredOneCU_1061 : Nat.Prime 1061 := by norm_num

private theorem prime_oneHundredOneCU_1087 : Nat.Prime 1087 := by norm_num

private theorem prime_oneHundredOneCU_1093 : Nat.Prime 1093 := by norm_num

private theorem prime_oneHundredOneCU_1103 : Nat.Prime 1103 := by norm_num

private theorem prime_oneHundredOneCU_1123 : Nat.Prime 1123 := by norm_num

private theorem prime_oneHundredOneCU_1163 : Nat.Prime 1163 := by norm_num

private theorem prime_oneHundredOneCU_1187 : Nat.Prime 1187 := by norm_num

private theorem prime_oneHundredOneCU_1201 : Nat.Prime 1201 := by norm_num

private theorem prime_oneHundredOneCU_1217 : Nat.Prime 1217 := by norm_num

private theorem prime_oneHundredOneCU_1259 : Nat.Prime 1259 := by norm_num

private theorem prime_oneHundredOneCU_1283 : Nat.Prime 1283 := by norm_num

private theorem prime_oneHundredOneCU_1291 : Nat.Prime 1291 := by norm_num

private theorem prime_oneHundredOneCU_1303 : Nat.Prime 1303 := by norm_num

private theorem prime_oneHundredOneCU_1409 : Nat.Prime 1409 := by norm_num

private theorem prime_oneHundredOneCU_1423 : Nat.Prime 1423 := by norm_num

private theorem prime_oneHundredOneCU_1453 : Nat.Prime 1453 := by norm_num

private theorem prime_oneHundredOneCU_1481 : Nat.Prime 1481 := by norm_num

private theorem prime_oneHundredOneCU_1499 : Nat.Prime 1499 := by norm_num

private theorem prime_oneHundredOneCU_1531 : Nat.Prime 1531 := by norm_num

private theorem prime_oneHundredOneCU_1559 : Nat.Prime 1559 := by norm_num

private theorem prime_oneHundredOneCU_1567 : Nat.Prime 1567 := by norm_num

private theorem prime_oneHundredOneCU_1583 : Nat.Prime 1583 := by norm_num

private theorem prime_oneHundredOneCU_1601 : Nat.Prime 1601 := by norm_num

private theorem prime_oneHundredOneCU_1657 : Nat.Prime 1657 := by norm_num

private theorem prime_oneHundredOneCU_1697 : Nat.Prime 1697 := by norm_num

private theorem prime_oneHundredOneCU_1699 : Nat.Prime 1699 := by norm_num

private theorem prime_oneHundredOneCU_1759 : Nat.Prime 1759 := by norm_num

private theorem prime_oneHundredOneCU_1801 : Nat.Prime 1801 := by norm_num

private theorem prime_oneHundredOneCU_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_oneHundredOneCU_1861 : Nat.Prime 1861 := by norm_num

private theorem prime_oneHundredOneCU_1879 : Nat.Prime 1879 := by norm_num

private theorem prime_oneHundredOneCU_1987 : Nat.Prime 1987 := by norm_num

private theorem prime_oneHundredOneCU_2011 : Nat.Prime 2011 := by norm_num

private theorem prime_oneHundredOneCU_2063 : Nat.Prime 2063 := by norm_num

private theorem prime_oneHundredOneCU_2141 : Nat.Prime 2141 := by norm_num

private theorem prime_oneHundredOneCU_2161 : Nat.Prime 2161 := by norm_num

private theorem prime_oneHundredOneCU_2309 : Nat.Prime 2309 := by norm_num

private theorem prime_oneHundredOneCU_2441 : Nat.Prime 2441 := by norm_num

private theorem prime_oneHundredOneCU_2473 : Nat.Prime 2473 := by norm_num

private theorem prime_oneHundredOneCU_2557 : Nat.Prime 2557 := by norm_num

private theorem prime_oneHundredOneCU_2579 : Nat.Prime 2579 := by norm_num

private theorem prime_oneHundredOneCU_2593 : Nat.Prime 2593 := by norm_num

private theorem prime_oneHundredOneCU_2657 : Nat.Prime 2657 := by norm_num

private theorem prime_oneHundredOneCU_2663 : Nat.Prime 2663 := by norm_num

private theorem prime_oneHundredOneCU_2699 : Nat.Prime 2699 := by norm_num

private theorem prime_oneHundredOneCU_2731 : Nat.Prime 2731 := by norm_num

private theorem prime_oneHundredOneCU_2897 : Nat.Prime 2897 := by norm_num

private theorem prime_oneHundredOneCU_2917 : Nat.Prime 2917 := by norm_num

private theorem prime_oneHundredOneCU_2971 : Nat.Prime 2971 := by norm_num

private theorem prime_oneHundredOneCU_2999 : Nat.Prime 2999 := by norm_num

private theorem prime_oneHundredOneCU_3041 : Nat.Prime 3041 := by norm_num

private theorem prime_oneHundredOneCU_3209 : Nat.Prime 3209 := by norm_num

private theorem prime_oneHundredOneCU_3217 : Nat.Prime 3217 := by norm_num

private theorem prime_oneHundredOneCU_3299 : Nat.Prime 3299 := by norm_num

private theorem prime_oneHundredOneCU_3347 : Nat.Prime 3347 := by norm_num

private theorem prime_oneHundredOneCU_3361 : Nat.Prime 3361 := by norm_num

private theorem prime_oneHundredOneCU_4019 : Nat.Prime 4019 := by norm_num

private theorem prime_oneHundredOneCU_4057 : Nat.Prime 4057 := by norm_num

private theorem prime_oneHundredOneCU_4091 : Nat.Prime 4091 := by norm_num

private theorem prime_oneHundredOneCU_4259 : Nat.Prime 4259 := by norm_num

private theorem prime_oneHundredOneCU_4517 : Nat.Prime 4517 := by norm_num

private theorem prime_oneHundredOneCU_4523 : Nat.Prime 4523 := by norm_num

private theorem prime_oneHundredOneCU_4649 : Nat.Prime 4649 := by norm_num

private theorem prime_oneHundredOneCU_4931 : Nat.Prime 4931 := by norm_num

private theorem prime_oneHundredOneCU_4973 : Nat.Prime 4973 := by norm_num

private theorem prime_oneHundredOneCU_5119 : Nat.Prime 5119 := by norm_num

private theorem prime_oneHundredOneCU_5189 : Nat.Prime 5189 := by norm_num

private theorem prime_oneHundredOneCU_5573 : Nat.Prime 5573 := by norm_num

private theorem prime_oneHundredOneCU_5743 : Nat.Prime 5743 := by norm_num

private theorem prime_oneHundredOneCU_5827 : Nat.Prime 5827 := by norm_num

private theorem prime_oneHundredOneCU_5851 : Nat.Prime 5851 := by norm_num

private theorem prime_oneHundredOneCU_6037 : Nat.Prime 6037 := by norm_num

private theorem prime_oneHundredOneCU_6151 : Nat.Prime 6151 := by norm_num

private theorem prime_oneHundredOneCU_6359 : Nat.Prime 6359 := by norm_num

private theorem prime_oneHundredOneCU_6659 : Nat.Prime 6659 := by norm_num

private theorem prime_oneHundredOneCU_6791 : Nat.Prime 6791 := by norm_num

private theorem prime_oneHundredOneCU_6827 : Nat.Prime 6827 := by norm_num

private theorem prime_oneHundredOneCU_6997 : Nat.Prime 6997 := by norm_num

private theorem prime_oneHundredOneCU_7349 : Nat.Prime 7349 := by norm_num

private theorem prime_oneHundredOneCU_7477 : Nat.Prime 7477 := by norm_num

private theorem prime_oneHundredOneCU_7591 : Nat.Prime 7591 := by norm_num

private theorem prime_oneHundredOneCU_8539 : Nat.Prime 8539 := by norm_num

private theorem prime_oneHundredOneCU_8669 : Nat.Prime 8669 := by norm_num

private theorem prime_oneHundredOneCU_9151 : Nat.Prime 9151 := by norm_num

private theorem prime_oneHundredOneCU_9241 : Nat.Prime 9241 := by norm_num

private theorem prime_oneHundredOneCU_9461 : Nat.Prime 9461 := by norm_num

private theorem prime_oneHundredOneCU_9623 : Nat.Prime 9623 := by norm_num

private theorem prime_oneHundredOneCU_9629 : Nat.Prime 9629 := by norm_num

private theorem prime_oneHundredOneCU_9767 : Nat.Prime 9767 := by norm_num

private theorem prime_oneHundredOneCU_9883 : Nat.Prime 9883 := by norm_num

private theorem prime_oneHundredOneCU_10141 : Nat.Prime 10141 := by norm_num

private theorem prime_oneHundredOneCU_10169 : Nat.Prime 10169 := by norm_num

private theorem prime_oneHundredOneCU_10177 : Nat.Prime 10177 := by norm_num

private theorem prime_oneHundredOneCU_10597 : Nat.Prime 10597 := by norm_num

private theorem prime_oneHundredOneCU_10691 : Nat.Prime 10691 := by norm_num

private theorem prime_oneHundredOneCU_10781 : Nat.Prime 10781 := by norm_num

private theorem prime_oneHundredOneCU_11941 : Nat.Prime 11941 := by norm_num

private theorem prime_oneHundredOneCU_12073 : Nat.Prime 12073 := by norm_num

private theorem prime_oneHundredOneCU_12097 : Nat.Prime 12097 := by norm_num

private theorem prime_oneHundredOneCU_12113 : Nat.Prime 12113 := by norm_num

private theorem prime_oneHundredOneCU_12379 : Nat.Prime 12379 := by norm_num

private theorem prime_oneHundredOneCU_12799 : Nat.Prime 12799 := by norm_num

private theorem prime_oneHundredOneCU_12919 : Nat.Prime 12919 := by norm_num

private theorem prime_oneHundredOneCU_13331 : Nat.Prime 13331 := by norm_num

private theorem prime_oneHundredOneCU_13649 : Nat.Prime 13649 := by norm_num

private theorem prime_oneHundredOneCU_13681 : Nat.Prime 13681 := by norm_num

private theorem prime_oneHundredOneCU_13921 : Nat.Prime 13921 := by norm_num

private theorem prime_oneHundredOneCU_14561 : Nat.Prime 14561 := by norm_num

private theorem prime_oneHundredOneCU_15227 : Nat.Prime 15227 := by norm_num

private theorem prime_oneHundredOneCU_16421 : Nat.Prime 16421 := by norm_num

private theorem prime_oneHundredOneCU_16901 : Nat.Prime 16901 := by norm_num

private theorem prime_oneHundredOneCU_17191 : Nat.Prime 17191 := by norm_num

private theorem prime_oneHundredOneCU_18089 : Nat.Prime 18089 := by norm_num

private theorem prime_oneHundredOneCU_18917 : Nat.Prime 18917 := by norm_num

private theorem prime_oneHundredOneCU_19861 : Nat.Prime 19861 := by norm_num

private theorem prime_oneHundredOneCU_20149 : Nat.Prime 20149 := by norm_num

private theorem prime_oneHundredOneCU_20287 : Nat.Prime 20287 := by norm_num

private theorem prime_oneHundredOneCU_20399 : Nat.Prime 20399 := by norm_num

private theorem prime_oneHundredOneCU_20663 : Nat.Prime 20663 := by norm_num

private theorem prime_oneHundredOneCU_21647 : Nat.Prime 21647 := by norm_num

private theorem prime_oneHundredOneCU_22133 : Nat.Prime 22133 := by norm_num

private theorem prime_oneHundredOneCU_22811 : Nat.Prime 22811 := by norm_num

private theorem prime_oneHundredOneCU_23321 : Nat.Prime 23321 := by norm_num

private theorem prime_oneHundredOneCU_24683 : Nat.Prime 24683 := by norm_num

private theorem prime_oneHundredOneCU_25367 : Nat.Prime 25367 := by norm_num

private theorem prime_oneHundredOneCU_25693 : Nat.Prime 25693 := by norm_num

private theorem prime_oneHundredOneCU_25717 : Nat.Prime 25717 := by norm_num

private theorem prime_oneHundredOneCU_25919 : Nat.Prime 25919 := by norm_num

private theorem prime_oneHundredOneCU_25999 : Nat.Prime 25999 := by norm_num

private theorem prime_oneHundredOneCU_26041 : Nat.Prime 26041 := by norm_num

private theorem prime_oneHundredOneCU_26237 : Nat.Prime 26237 := by norm_num

private theorem prime_oneHundredOneCU_27673 : Nat.Prime 27673 := by norm_num

private theorem prime_oneHundredOneCU_27773 : Nat.Prime 27773 := by norm_num

private theorem prime_oneHundredOneCU_28909 : Nat.Prime 28909 := by norm_num

private theorem prime_oneHundredOneCU_30011 : Nat.Prime 30011 := by norm_num

private theorem prime_oneHundredOneCU_30937 : Nat.Prime 30937 := by norm_num

private theorem prime_oneHundredOneCU_31481 : Nat.Prime 31481 := by norm_num

private theorem prime_oneHundredOneCU_31771 : Nat.Prime 31771 := by norm_num

private theorem prime_oneHundredOneCU_32189 : Nat.Prime 32189 := by norm_num

private theorem prime_oneHundredOneCU_32561 : Nat.Prime 32561 := by norm_num

private theorem prime_oneHundredOneCU_33479 : Nat.Prime 33479 := by norm_num

private theorem prime_oneHundredOneCU_34549 : Nat.Prime 34549 := by norm_num

private theorem prime_oneHundredOneCU_35447 : Nat.Prime 35447 := by norm_num

private theorem prime_oneHundredOneCU_37097 : Nat.Prime 37097 := by norm_num

private theorem prime_oneHundredOneCU_37643 : Nat.Prime 37643 := by norm_num

private theorem prime_oneHundredOneCU_40841 : Nat.Prime 40841 := by norm_num

private theorem prime_oneHundredOneCU_41357 : Nat.Prime 41357 := by norm_num

private theorem prime_oneHundredOneCU_41659 : Nat.Prime 41659 := by norm_num

private theorem prime_oneHundredOneCU_43789 : Nat.Prime 43789 := by norm_num

private theorem prime_oneHundredOneCU_44273 : Nat.Prime 44273 := by norm_num

private theorem prime_oneHundredOneCU_44909 : Nat.Prime 44909 := by norm_num

private theorem prime_oneHundredOneCU_44987 : Nat.Prime 44987 := by norm_num

private theorem prime_oneHundredOneCU_45523 : Nat.Prime 45523 := by norm_num

private theorem prime_oneHundredOneCU_46381 : Nat.Prime 46381 := by norm_num

private theorem prime_oneHundredOneCU_48437 : Nat.Prime 48437 := by norm_num

private theorem prime_oneHundredOneCU_49633 : Nat.Prime 49633 := by norm_num

private theorem prime_oneHundredOneCU_49993 : Nat.Prime 49993 := by norm_num

private theorem prime_oneHundredOneCU_50147 : Nat.Prime 50147 := by norm_num

private theorem prime_oneHundredOneCU_51827 : Nat.Prime 51827 := by norm_num

private theorem prime_oneHundredOneCU_52963 : Nat.Prime 52963 := by norm_num

private theorem prime_oneHundredOneCU_57727 : Nat.Prime 57727 := by norm_num

private theorem prime_oneHundredOneCU_61909 : Nat.Prime 61909 := by norm_num

private theorem prime_oneHundredOneCU_63079 : Nat.Prime 63079 := by norm_num

private theorem prime_oneHundredOneCU_63697 : Nat.Prime 63697 := by norm_num

private theorem prime_oneHundredOneCU_64279 : Nat.Prime 64279 := by norm_num

private theorem prime_oneHundredOneCU_65119 : Nat.Prime 65119 := by norm_num

private theorem prime_oneHundredOneCU_67057 : Nat.Prime 67057 := by norm_num

private theorem prime_oneHundredOneCU_71399 : Nat.Prime 71399 := by norm_num

private theorem prime_oneHundredOneCU_72091 : Nat.Prime 72091 := by norm_num

private theorem prime_oneHundredOneCU_77543 : Nat.Prime 77543 := by norm_num

private theorem prime_oneHundredOneCU_80407 : Nat.Prime 80407 := by norm_num

private theorem prime_oneHundredOneCU_83717 : Nat.Prime 83717 := by norm_num

private theorem prime_oneHundredOneCU_85021 : Nat.Prime 85021 := by norm_num

private theorem prime_oneHundredOneCU_88129 : Nat.Prime 88129 := by norm_num

private theorem prime_oneHundredOneCU_88897 : Nat.Prime 88897 := by norm_num

private theorem prime_oneHundredOneCU_89317 : Nat.Prime 89317 := by norm_num

private theorem prime_oneHundredOneCU_90023 : Nat.Prime 90023 := by norm_num

private theorem prime_oneHundredOneCU_90703 : Nat.Prime 90703 := by norm_num

private theorem prime_oneHundredOneCU_93281 : Nat.Prime 93281 := by norm_num

private theorem prime_oneHundredOneCU_95287 : Nat.Prime 95287 := by norm_num

private theorem prime_oneHundredOneCU_96779 : Nat.Prime 96779 := by norm_num

private theorem prime_oneHundredOneCU_97583 : Nat.Prime 97583 := by norm_num

private theorem prime_oneHundredOneCU_98369 : Nat.Prime 98369 := by norm_num

private theorem prime_oneHundredOneCU_100549 : Nat.Prime 100549 := by norm_num

private theorem prime_oneHundredOneCU_101203 : Nat.Prime 101203 := by norm_num

private theorem prime_oneHundredOneCU_104803 : Nat.Prime 104803 := by norm_num

private theorem prime_oneHundredOneCU_108947 : Nat.Prime 108947 := by norm_num

private theorem prime_oneHundredOneCU_120847 : Nat.Prime 120847 := by norm_num

private theorem prime_oneHundredOneCU_129127 : Nat.Prime 129127 := by norm_num

private theorem prime_oneHundredOneCU_129287 : Nat.Prime 129287 := by norm_num

private theorem prime_oneHundredOneCU_130201 : Nat.Prime 130201 := by norm_num

private theorem prime_oneHundredOneCU_141499 : Nat.Prime 141499 := by norm_num

private theorem prime_oneHundredOneCU_145757 : Nat.Prime 145757 := by norm_num

private theorem prime_oneHundredOneCU_146347 : Nat.Prime 146347 := by norm_num

private theorem prime_oneHundredOneCU_147139 : Nat.Prime 147139 := by norm_num

private theorem prime_oneHundredOneCU_160789 : Nat.Prime 160789 := by norm_num

private theorem prime_oneHundredOneCU_161009 : Nat.Prime 161009 := by norm_num

private theorem prime_oneHundredOneCU_168499 : Nat.Prime 168499 := by norm_num

private theorem prime_oneHundredOneCU_170299 : Nat.Prime 170299 := by norm_num

private theorem prime_oneHundredOneCU_172243 : Nat.Prime 172243 := by norm_num

private theorem prime_oneHundredOneCU_174121 : Nat.Prime 174121 := by norm_num

private theorem prime_oneHundredOneCU_177647 : Nat.Prime 177647 := by norm_num

private theorem prime_oneHundredOneCU_185599 : Nat.Prime 185599 := by norm_num

private theorem prime_oneHundredOneCU_190837 : Nat.Prime 190837 := by norm_num

private theorem prime_oneHundredOneCU_197089 : Nat.Prime 197089 := by norm_num

private theorem prime_oneHundredOneCU_213791 : Nat.Prime 213791 := by norm_num

private theorem prime_oneHundredOneCU_218509 : Nat.Prime 218509 := by norm_num

private theorem prime_oneHundredOneCU_226487 : Nat.Prime 226487 := by norm_num

private theorem prime_oneHundredOneCU_229127 : Nat.Prime 229127 := by norm_num

private theorem prime_oneHundredOneCU_246809 : Nat.Prime 246809 := by norm_num

private theorem prime_oneHundredOneCU_287813 : Nat.Prime 287813 := by norm_num

private theorem prime_oneHundredOneCU_302191 : Nat.Prime 302191 := by norm_num

private theorem prime_oneHundredOneCU_329533 : Nat.Prime 329533 := by norm_num

private theorem prime_oneHundredOneCU_340619 : Nat.Prime 340619 := by norm_num

private theorem prime_oneHundredOneCU_341063 : Nat.Prime 341063 := by norm_num

private theorem prime_oneHundredOneCU_358711 : Nat.Prime 358711 := by norm_num

private theorem prime_oneHundredOneCU_360271 : Nat.Prime 360271 := by norm_num

private theorem prime_oneHundredOneCU_373231 : Nat.Prime 373231 := by norm_num

private theorem prime_oneHundredOneCU_404533 : Nat.Prime 404533 := by norm_num

private theorem prime_oneHundredOneCU_412717 : Nat.Prime 412717 := by norm_num

private theorem prime_oneHundredOneCU_424849 : Nat.Prime 424849 := by norm_num

private theorem prime_oneHundredOneCU_427541 : Nat.Prime 427541 := by norm_num

private theorem prime_oneHundredOneCU_438049 : Nat.Prime 438049 := by norm_num

private theorem prime_oneHundredOneCU_458531 : Nat.Prime 458531 := by norm_num

private theorem prime_oneHundredOneCU_460841 : Nat.Prime 460841 := by norm_num

private theorem prime_oneHundredOneCU_469099 : Nat.Prime 469099 := by norm_num

private theorem prime_oneHundredOneCU_470489 : Nat.Prime 470489 := by norm_num

private theorem prime_oneHundredOneCU_480533 : Nat.Prime 480533 := by norm_num

private theorem prime_oneHundredOneCU_557521 : Nat.Prime 557521 := by norm_num

private theorem prime_oneHundredOneCU_559649 : Nat.Prime 559649 := by norm_num

private theorem prime_oneHundredOneCU_572137 : Nat.Prime 572137 := by norm_num

private theorem prime_oneHundredOneCU_580231 : Nat.Prime 580231 := by norm_num

private theorem prime_oneHundredOneCU_620303 : Nat.Prime 620303 := by norm_num

private theorem prime_oneHundredOneCU_623879 : Nat.Prime 623879 := by norm_num

private theorem prime_oneHundredOneCU_633467 : Nat.Prime 633467 := by norm_num

private theorem prime_oneHundredOneCU_639697 : Nat.Prime 639697 := by norm_num

private theorem prime_oneHundredOneCU_668159 : Nat.Prime 668159 := by norm_num

private theorem prime_oneHundredOneCU_704393 : Nat.Prime 704393 := by norm_num

private theorem prime_oneHundredOneCU_715303 : Nat.Prime 715303 := by norm_num

private theorem prime_oneHundredOneCU_728851 : Nat.Prime 728851 := by norm_num

private theorem prime_oneHundredOneCU_729413 : Nat.Prime 729413 := by norm_num

private theorem prime_oneHundredOneCU_744791 : Nat.Prime 744791 := by norm_num

private theorem prime_oneHundredOneCU_749149 : Nat.Prime 749149 := by norm_num

private theorem prime_oneHundredOneCU_769579 : Nat.Prime 769579 := by norm_num

private theorem prime_oneHundredOneCU_776557 : Nat.Prime 776557 := by norm_num

private theorem prime_oneHundredOneCU_781229 : Nat.Prime 781229 := by norm_num

private theorem prime_oneHundredOneCU_840223 : Nat.Prime 840223 := by norm_num

private theorem prime_oneHundredOneCU_850691 : Nat.Prime 850691 := by norm_num

private theorem prime_oneHundredOneCU_854353 : Nat.Prime 854353 := by norm_num

private theorem prime_oneHundredOneCU_914339 : Nat.Prime 914339 := by norm_num

private theorem prime_oneHundredOneCU_926633 : Nat.Prime 926633 := by norm_num

private theorem prime_oneHundredOneCU_932549 : Nat.Prime 932549 := by norm_num

private theorem prime_oneHundredOneCU_947383 : Nat.Prime 947383 := by norm_num

private theorem prime_oneHundredOneCU_1033807 : Nat.Prime 1033807 := by norm_num

private theorem prime_oneHundredOneCU_1035451 : Nat.Prime 1035451 := by norm_num

private theorem prime_oneHundredOneCU_1074877 : Nat.Prime 1074877 := by norm_num

private theorem prime_oneHundredOneCU_1108957 : Nat.Prime 1108957 := by norm_num

private theorem prime_oneHundredOneCU_1147103 : Nat.Prime 1147103 := by norm_num

private theorem prime_oneHundredOneCU_1335319 : Nat.Prime 1335319 := by norm_num

private theorem prime_oneHundredOneCU_1387849 : Nat.Prime 1387849 := by norm_num

private theorem prime_oneHundredOneCU_1498789 : Nat.Prime 1498789 := by norm_num

private theorem prime_oneHundredOneCU_1507069 : Nat.Prime 1507069 := by norm_num

private theorem prime_oneHundredOneCU_1541431 : Nat.Prime 1541431 := by norm_num

private theorem prime_oneHundredOneCU_1589239 : Nat.Prime 1589239 := by norm_num

private theorem prime_oneHundredOneCU_1601219 : Nat.Prime 1601219 := by norm_num

private theorem prime_oneHundredOneCU_1652509 : Nat.Prime 1652509 := by norm_num

private theorem prime_oneHundredOneCU_1774067 : Nat.Prime 1774067 := by norm_num

private theorem prime_oneHundredOneCU_1980191 : Nat.Prime 1980191 := by norm_num

private theorem prime_oneHundredOneCU_2015791 : Nat.Prime 2015791 := by norm_num

private theorem prime_oneHundredOneCU_2192947 : Nat.Prime 2192947 := by norm_num

private theorem prime_oneHundredOneCU_2228687 : Nat.Prime 2228687 := by norm_num

private theorem prime_oneHundredOneCU_2289593 : Nat.Prime 2289593 := by norm_num

private theorem prime_oneHundredOneCU_2361721 : Nat.Prime 2361721 := by norm_num

private theorem prime_oneHundredOneCU_2364917 : Nat.Prime 2364917 := by norm_num

private theorem prime_oneHundredOneCU_2542229 : Nat.Prime 2542229 := by norm_num

private theorem prime_oneHundredOneCU_2653481 : Nat.Prime 2653481 := by norm_num

private theorem prime_oneHundredOneCU_2737793 : Nat.Prime 2737793 := by norm_num

private theorem prime_oneHundredOneCU_2795459 : Nat.Prime 2795459 := by norm_num

private theorem prime_oneHundredOneCU_2969303 : Nat.Prime 2969303 := by norm_num

private theorem prime_oneHundredOneCU_3065663 : Nat.Prime 3065663 := by norm_num

private theorem prime_oneHundredOneCU_3074879 : Nat.Prime 3074879 := by norm_num

private theorem prime_oneHundredOneCU_3142313 : Nat.Prime 3142313 := by norm_num

private theorem prime_oneHundredOneCU_3178013 : Nat.Prime 3178013 := by norm_num

private theorem prime_oneHundredOneCU_3265403 : Nat.Prime 3265403 := by norm_num

private theorem prime_oneHundredOneCU_3361387 : Nat.Prime 3361387 := by norm_num

private theorem prime_oneHundredOneCU_3512987 : Nat.Prime 3512987 := by norm_num

private theorem prime_oneHundredOneCU_3584459 : Nat.Prime 3584459 := by norm_num

private theorem prime_oneHundredOneCU_3758093 : Nat.Prime 3758093 := by norm_num

private theorem prime_oneHundredOneCU_3948281 : Nat.Prime 3948281 := by norm_num

private theorem prime_oneHundredOneCU_4016503 : Nat.Prime 4016503 := by norm_num

private theorem prime_oneHundredOneCU_4096823 : Nat.Prime 4096823 := by norm_num

private theorem prime_oneHundredOneCU_4219979 : Nat.Prime 4219979 := by norm_num

private theorem prime_oneHundredOneCU_4266391 : Nat.Prime 4266391 := by norm_num

private theorem prime_oneHundredOneCU_4418749 : Nat.Prime 4418749 := by norm_num

private theorem prime_oneHundredOneCU_4558661 : Nat.Prime 4558661 := by norm_num

private theorem prime_oneHundredOneCU_4599737 : Nat.Prime 4599737 := by norm_num

private theorem prime_oneHundredOneCU_5052559 : Nat.Prime 5052559 := by norm_num

private theorem prime_oneHundredOneCU_5165801 : Nat.Prime 5165801 := by norm_num

private theorem prime_oneHundredOneCU_5441437 : Nat.Prime 5441437 := by norm_num

private theorem prime_oneHundredOneCU_6138871 : Nat.Prime 6138871 := by norm_num

private theorem prime_oneHundredOneCU_6163169 : Nat.Prime 6163169 := by norm_num

private theorem prime_oneHundredOneCU_6390029 : Nat.Prime 6390029 := by norm_num

private theorem prime_oneHundredOneCU_6393091 : Nat.Prime 6393091 := by norm_num

private theorem prime_oneHundredOneCU_6588859 : Nat.Prime 6588859 := by norm_num

private theorem prime_oneHundredOneCU_6669683 : Nat.Prime 6669683 := by norm_num

private theorem prime_oneHundredOneCU_6701467 : Nat.Prime 6701467 := by norm_num

private theorem prime_oneHundredOneCU_6856781 : Nat.Prime 6856781 := by norm_num

private theorem prime_oneHundredOneCU_6862319 : Nat.Prime 6862319 := by norm_num

private theorem prime_oneHundredOneCU_7442153 : Nat.Prime 7442153 := by norm_num

private theorem prime_oneHundredOneCU_7719889 : Nat.Prime 7719889 := by norm_num

private theorem prime_oneHundredOneCU_7751531 : Nat.Prime 7751531 := by norm_num

private theorem prime_oneHundredOneCU_8198191 : Nat.Prime 8198191 := by norm_num

private theorem prime_oneHundredOneCU_8291741 : Nat.Prime 8291741 := by norm_num

private theorem prime_oneHundredOneCU_8556059 : Nat.Prime 8556059 := by norm_num

private theorem prime_oneHundredOneCU_9163981 : Nat.Prime 9163981 := by norm_num

private theorem prime_oneHundredOneCU_9546253 : Nat.Prime 9546253 := by norm_num

private theorem prime_oneHundredOneCU_9725489 : Nat.Prime 9725489 := by norm_num

private theorem prime_oneHundredOneCU_10576519 : Nat.Prime 10576519 := by norm_num

private theorem prime_oneHundredOneCU_10632887 : Nat.Prime 10632887 := by norm_num

private theorem prime_oneHundredOneCU_10695599 : Nat.Prime 10695599 := by norm_num

private theorem prime_oneHundredOneCU_12187067 : Nat.Prime 12187067 := by norm_num

private theorem prime_oneHundredOneCU_12476221 : Nat.Prime 12476221 := by norm_num

private theorem prime_oneHundredOneCU_12518329 : Nat.Prime 12518329 := by norm_num

private theorem prime_oneHundredOneCU_12931669 : Nat.Prime 12931669 := by norm_num

private theorem prime_oneHundredOneCU_13446299 : Nat.Prime 13446299 := by norm_num

private theorem prime_oneHundredOneCU_13802353 : Nat.Prime 13802353 := by norm_num

private theorem prime_oneHundredOneCU_14720089 : Nat.Prime 14720089 := by norm_num

private theorem prime_oneHundredOneCU_15444071 : Nat.Prime 15444071 := by norm_num

private theorem prime_oneHundredOneCU_15930997 : Nat.Prime 15930997 := by norm_num

private theorem prime_oneHundredOneCU_15972841 : Nat.Prime 15972841 := by norm_num

private theorem prime_oneHundredOneCU_16831459 : Nat.Prime 16831459 := by norm_num

private theorem prime_oneHundredOneCU_17608711 : Nat.Prime 17608711 := by norm_num

private theorem prime_oneHundredOneCU_19709617 : Nat.Prime 19709617 := by norm_num

private theorem prime_oneHundredOneCU_20793169 : Nat.Prime 20793169 := by norm_num

private theorem prime_oneHundredOneCU_26365541 : Nat.Prime 26365541 := by norm_num

private theorem prime_oneHundredOneCU_27003367 : Nat.Prime 27003367 := by norm_num

private theorem prime_oneHundredOneCU_30879557 : Nat.Prime 30879557 := by
  apply lucas_primality 30879557 (2 : ZMod 30879557)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7719889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7719889, 1)] : List FactorBlock).map factorBlockValue).prod) = 30879557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_7719889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 30879557) ^ 15439778 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 30879557) ^ 4 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_32203397 : Nat.Prime 32203397 := by
  apply lucas_primality 32203397 (2 : ZMod 32203397)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (109, 1), (233, 1), (317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (109, 1), (233, 1), (317, 1)] : List FactorBlock).map factorBlockValue).prod) = 32203397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_109
      · exact prime_oneHundredOneCU_233
      · exact prime_oneHundredOneCU_317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32203397) ^ 16101698 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 32203397) ^ 295444 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 32203397) ^ 138212 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 32203397) ^ 101588 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_34105789 : Nat.Prime 34105789 := by
  apply lucas_primality 34105789 (2 : ZMod 34105789)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (947383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (947383, 1)] : List FactorBlock).map factorBlockValue).prod) = 34105789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_947383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 34105789) ^ 17052894 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 34105789) ^ 11368596 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 34105789) ^ 36 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_34107329 : Nat.Prime 34107329 := by
  apply lucas_primality 34107329 (3 : ZMod 34107329)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (409, 1), (1303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (409, 1), (1303, 1)] : List FactorBlock).map factorBlockValue).prod) = 34107329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_409
      · exact prime_oneHundredOneCU_1303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 34107329) ^ 17053664 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 34107329) ^ 83392 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 34107329) ^ 26176 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_35485211 : Nat.Prime 35485211 := by
  apply lucas_primality 35485211 (2 : ZMod 35485211)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (67, 1), (52963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (67, 1), (52963, 1)] : List FactorBlock).map factorBlockValue).prod) = 35485211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_67
      · exact prime_oneHundredOneCU_52963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 35485211) ^ 17742605 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 35485211) ^ 7097042 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 35485211) ^ 529630 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 35485211) ^ 670 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_37239551 : Nat.Prime 37239551 := by
  apply lucas_primality 37239551 (13 : ZMod 37239551)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (744791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (744791, 1)] : List FactorBlock).map factorBlockValue).prod) = 37239551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_744791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 37239551) ^ 18619775 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (13 : ZMod 37239551) ^ 7447910 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (13 : ZMod 37239551) ^ 50 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_42937339 : Nat.Prime 42937339 := by
  apply lucas_primality 42937339 (2 : ZMod 42937339)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (89, 1), (80407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (89, 1), (80407, 1)] : List FactorBlock).map factorBlockValue).prod) = 42937339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_89
      · exact prime_oneHundredOneCU_80407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 42937339) ^ 21468669 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 42937339) ^ 14312446 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 42937339) ^ 482442 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 42937339) ^ 534 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_46174741 : Nat.Prime 46174741 := by
  apply lucas_primality 46174741 (10 : ZMod 46174741)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (769579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (769579, 1)] : List FactorBlock).map factorBlockValue).prod) = 46174741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_769579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 46174741) ^ 23087370 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (10 : ZMod 46174741) ^ 15391580 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (10 : ZMod 46174741) ^ 9234948 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (10 : ZMod 46174741) ^ 60 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_50639749 : Nat.Prime 50639749 := by
  apply lucas_primality 50639749 (10 : ZMod 50639749)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (4219979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (4219979, 1)] : List FactorBlock).map factorBlockValue).prod) = 50639749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_4219979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 50639749) ^ 25319874 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (10 : ZMod 50639749) ^ 16879916 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (10 : ZMod 50639749) ^ 12 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_53249519 : Nat.Prime 53249519 := by
  apply lucas_primality 53249519 (7 : ZMod 53249519)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (733, 1), (5189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (733, 1), (5189, 1)] : List FactorBlock).map factorBlockValue).prod) = 53249519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_733
      · exact prime_oneHundredOneCU_5189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 53249519) ^ 26624759 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 53249519) ^ 7607074 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 53249519) ^ 72646 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 53249519) ^ 10262 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_55992161 : Nat.Prime 55992161 := by
  apply lucas_primality 55992161 (3 : ZMod 55992161)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (7, 1), (49993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (7, 1), (49993, 1)] : List FactorBlock).map factorBlockValue).prod) = 55992161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_49993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 55992161) ^ 27996080 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 55992161) ^ 11198432 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 55992161) ^ 7998880 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 55992161) ^ 1120 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_57776189 : Nat.Prime 57776189 := by
  apply lucas_primality 57776189 (2 : ZMod 57776189)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (31, 1), (137, 1), (179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (31, 1), (137, 1), (179, 1)] : List FactorBlock).map factorBlockValue).prod) = 57776189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_19
      · exact prime_oneHundredOneCU_31
      · exact prime_oneHundredOneCU_137
      · exact prime_oneHundredOneCU_179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 57776189) ^ 28888094 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 57776189) ^ 3040852 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 57776189) ^ 1863748 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 57776189) ^ 421724 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 57776189) ^ 322772 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_58363813 : Nat.Prime 58363813 := by
  apply lucas_primality 58363813 (6 : ZMod 58363813)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 2), (53, 1), (181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 2), (53, 1), (181, 1)] : List FactorBlock).map factorBlockValue).prod) = 58363813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_13
      · exact prime_oneHundredOneCU_53
      · exact prime_oneHundredOneCU_181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 58363813) ^ 29181906 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 58363813) ^ 19454604 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 58363813) ^ 4489524 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 58363813) ^ 1101204 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 58363813) ^ 322452 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_61893959 : Nat.Prime 61893959 := by
  apply lucas_primality 61893959 (14 : ZMod 61893959)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (127, 1), (4973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (127, 1), (4973, 1)] : List FactorBlock).map factorBlockValue).prod) = 61893959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_127
      · exact prime_oneHundredOneCU_4973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 61893959) ^ 30946979 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (14 : ZMod 61893959) ^ 8841994 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (14 : ZMod 61893959) ^ 487354 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (14 : ZMod 61893959) ^ 12446 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_63797323 : Nat.Prime 63797323 := by
  apply lucas_primality 63797323 (2 : ZMod 63797323)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (10632887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (10632887, 1)] : List FactorBlock).map factorBlockValue).prod) = 63797323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_10632887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 63797323) ^ 31898661 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 63797323) ^ 21265774 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 63797323) ^ 6 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_66333929 : Nat.Prime 66333929 := by
  apply lucas_primality 66333929 (3 : ZMod 66333929)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (8291741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (8291741, 1)] : List FactorBlock).map factorBlockValue).prod) = 66333929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_8291741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 66333929) ^ 33166964 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 66333929) ^ 8 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_69298967 : Nat.Prime 69298967 := by
  apply lucas_primality 69298967 (5 : ZMod 69298967)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (193, 1), (859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (193, 1), (859, 1)] : List FactorBlock).map factorBlockValue).prod) = 69298967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_11
      · exact prime_oneHundredOneCU_19
      · exact prime_oneHundredOneCU_193
      · exact prime_oneHundredOneCU_859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 69298967) ^ 34649483 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 69298967) ^ 6299906 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 69298967) ^ 3647314 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 69298967) ^ 359062 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 69298967) ^ 80674 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_73575913 : Nat.Prime 73575913 := by
  apply lucas_primality 73575913 (7 : ZMod 73575913)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (3065663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (3065663, 1)] : List FactorBlock).map factorBlockValue).prod) = 73575913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_3065663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 73575913) ^ 36787956 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 73575913) ^ 24525304 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 73575913) ^ 24 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_77837173 : Nat.Prime 77837173 := by
  apply lucas_primality 77837173 (2 : ZMod 77837173)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (926633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (926633, 1)] : List FactorBlock).map factorBlockValue).prod) = 77837173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_926633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 77837173) ^ 38918586 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 77837173) ^ 25945724 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 77837173) ^ 11119596 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 77837173) ^ 84 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_81936461 : Nat.Prime 81936461 := by
  apply lucas_primality 81936461 (2 : ZMod 81936461)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (4096823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (4096823, 1)] : List FactorBlock).map factorBlockValue).prod) = 81936461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_4096823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 81936461) ^ 40968230 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 81936461) ^ 16387292 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 81936461) ^ 20 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_84663223 : Nat.Prime 84663223 := by
  apply lucas_primality 84663223 (3 : ZMod 84663223)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (2015791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (2015791, 1)] : List FactorBlock).map factorBlockValue).prod) = 84663223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_2015791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 84663223) ^ 42331611 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 84663223) ^ 28221074 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 84663223) ^ 12094746 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 84663223) ^ 42 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_84828571 : Nat.Prime 84828571 := by
  apply lucas_primality 84828571 (7 : ZMod 84828571)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (89, 1), (31771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (89, 1), (31771, 1)] : List FactorBlock).map factorBlockValue).prod) = 84828571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_89
      · exact prime_oneHundredOneCU_31771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 84828571) ^ 42414285 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 84828571) ^ 28276190 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 84828571) ^ 16965714 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 84828571) ^ 953130 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 84828571) ^ 2670 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_85564793 : Nat.Prime 85564793 := by
  apply lucas_primality 85564793 (3 : ZMod 85564793)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (10695599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (10695599, 1)] : List FactorBlock).map factorBlockValue).prod) = 85564793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_10695599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 85564793) ^ 42782396 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 85564793) ^ 8 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_87865241 : Nat.Prime 87865241 := by
  apply lucas_primality 87865241 (6 : ZMod 87865241)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (1409, 1), (1559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (1409, 1), (1559, 1)] : List FactorBlock).map factorBlockValue).prod) = 87865241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_1409
      · exact prime_oneHundredOneCU_1559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 87865241) ^ 43932620 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 87865241) ^ 17573048 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 87865241) ^ 62360 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 87865241) ^ 56360 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_90141559 : Nat.Prime 90141559 := by
  apply lucas_primality 90141559 (3 : ZMod 90141559)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 2), (88897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 2), (88897, 1)] : List FactorBlock).map factorBlockValue).prod) = 90141559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_13
      · exact prime_oneHundredOneCU_88897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 90141559) ^ 45070779 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 90141559) ^ 30047186 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 90141559) ^ 6933966 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 90141559) ^ 1014 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_91758097 : Nat.Prime 91758097 := by
  apply lucas_primality 91758097 (10 : ZMod 91758097)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (101, 1), (701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (101, 1), (701, 1)] : List FactorBlock).map factorBlockValue).prod) = 91758097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_101
      · exact prime_oneHundredOneCU_701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 91758097) ^ 45879048 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (10 : ZMod 91758097) ^ 30586032 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (10 : ZMod 91758097) ^ 908496 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (10 : ZMod 91758097) ^ 130896 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_94269391 : Nat.Prime 94269391 := by
  apply lucas_primality 94269391 (12 : ZMod 94269391)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (3142313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (3142313, 1)] : List FactorBlock).map factorBlockValue).prod) = 94269391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_3142313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (12 : ZMod 94269391) ^ 47134695 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (12 : ZMod 94269391) ^ 31423130 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (12 : ZMod 94269391) ^ 18853878 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (12 : ZMod 94269391) ^ 30 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_96243773 : Nat.Prime 96243773 := by
  apply lucas_primality 96243773 (2 : ZMod 96243773)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (283, 1), (85021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (283, 1), (85021, 1)] : List FactorBlock).map factorBlockValue).prod) = 96243773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_283
      · exact prime_oneHundredOneCU_85021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 96243773) ^ 48121886 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 96243773) ^ 340084 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 96243773) ^ 1132 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_96809287 : Nat.Prime 96809287 := by
  apply lucas_primality 96809287 (3 : ZMod 96809287)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (79, 1), (163, 1), (179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (79, 1), (163, 1), (179, 1)] : List FactorBlock).map factorBlockValue).prod) = 96809287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_79
      · exact prime_oneHundredOneCU_163
      · exact prime_oneHundredOneCU_179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 96809287) ^ 48404643 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 96809287) ^ 32269762 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 96809287) ^ 13829898 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 96809287) ^ 1225434 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 96809287) ^ 593922 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 96809287) ^ 540834 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_115552379 : Nat.Prime 115552379 := by
  apply lucas_primality 115552379 (2 : ZMod 115552379)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (57776189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (57776189, 1)] : List FactorBlock).map factorBlockValue).prod) = 115552379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_57776189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 115552379) ^ 57776189 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 115552379) ^ 2 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_118892869 : Nat.Prime 118892869 := by
  apply lucas_primality 118892869 (2 : ZMod 118892869)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (919, 1), (10781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (919, 1), (10781, 1)] : List FactorBlock).map factorBlockValue).prod) = 118892869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_919
      · exact prime_oneHundredOneCU_10781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 118892869) ^ 59446434 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 118892869) ^ 39630956 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 118892869) ^ 129372 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 118892869) ^ 11028 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_123787919 : Nat.Prime 123787919 := by
  apply lucas_primality 123787919 (13 : ZMod 123787919)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61893959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61893959, 1)] : List FactorBlock).map factorBlockValue).prod) = 123787919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_61893959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (13 : ZMod 123787919) ^ 61893959 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (13 : ZMod 123787919) ^ 2 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_124209779 : Nat.Prime 124209779 := by
  apply lucas_primality 124209779 (2 : ZMod 124209779)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (619, 1), (1303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (619, 1), (1303, 1)] : List FactorBlock).map factorBlockValue).prod) = 124209779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_11
      · exact prime_oneHundredOneCU_619
      · exact prime_oneHundredOneCU_1303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 124209779) ^ 62104889 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 124209779) ^ 17744254 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 124209779) ^ 11291798 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 124209779) ^ 200662 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 124209779) ^ 95326 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_127310383 : Nat.Prime 127310383 := by
  apply lucas_primality 127310383 (3 : ZMod 127310383)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (23, 1), (18089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (23, 1), (18089, 1)] : List FactorBlock).map factorBlockValue).prod) = 127310383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_17
      · exact prime_oneHundredOneCU_23
      · exact prime_oneHundredOneCU_18089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 127310383) ^ 63655191 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 127310383) ^ 42436794 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 127310383) ^ 7488846 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 127310383) ^ 5535234 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 127310383) ^ 7038 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_144051547 : Nat.Prime 144051547 := by
  apply lucas_primality 144051547 (3 : ZMod 144051547)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1759, 1), (13649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1759, 1), (13649, 1)] : List FactorBlock).map factorBlockValue).prod) = 144051547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_1759
      · exact prime_oneHundredOneCU_13649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 144051547) ^ 72025773 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 144051547) ^ 48017182 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 144051547) ^ 81894 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 144051547) ^ 10554 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_156276031 : Nat.Prime 156276031 := by
  apply lucas_primality 156276031 (7 : ZMod 156276031)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (23, 1), (226487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (23, 1), (226487, 1)] : List FactorBlock).map factorBlockValue).prod) = 156276031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_23
      · exact prime_oneHundredOneCU_226487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 156276031) ^ 78138015 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 156276031) ^ 52092010 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 156276031) ^ 31255206 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 156276031) ^ 6794610 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 156276031) ^ 690 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_164951659 : Nat.Prime 164951659 := by
  apply lucas_primality 164951659 (10 : ZMod 164951659)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (9163981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (9163981, 1)] : List FactorBlock).map factorBlockValue).prod) = 164951659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_9163981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 164951659) ^ 82475829 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (10 : ZMod 164951659) ^ 54983886 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (10 : ZMod 164951659) ^ 18 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_171129587 : Nat.Prime 171129587 := by
  apply lucas_primality 171129587 (2 : ZMod 171129587)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (85564793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (85564793, 1)] : List FactorBlock).map factorBlockValue).prod) = 171129587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_85564793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 171129587) ^ 85564793 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 171129587) ^ 2 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_185485739 : Nat.Prime 185485739 := by
  apply lucas_primality 185485739 (2 : ZMod 185485739)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (193, 1), (480533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (193, 1), (480533, 1)] : List FactorBlock).map factorBlockValue).prod) = 185485739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_193
      · exact prime_oneHundredOneCU_480533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 185485739) ^ 92742869 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 185485739) ^ 961066 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 185485739) ^ 386 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_192979337 : Nat.Prime 192979337 := by
  apply lucas_primality 192979337 (3 : ZMod 192979337)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (2192947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (2192947, 1)] : List FactorBlock).map factorBlockValue).prod) = 192979337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_11
      · exact prime_oneHundredOneCU_2192947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 192979337) ^ 96489668 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 192979337) ^ 17543576 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 192979337) ^ 88 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_202938553 : Nat.Prime 202938553 := by
  apply lucas_primality 202938553 (5 : ZMod 202938553)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (1087, 1), (2593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (1087, 1), (2593, 1)] : List FactorBlock).map factorBlockValue).prod) = 202938553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_1087
      · exact prime_oneHundredOneCU_2593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 202938553) ^ 101469276 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 202938553) ^ 67646184 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 202938553) ^ 186696 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 202938553) ^ 78264 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_222872401 : Nat.Prime 222872401 := by
  apply lucas_primality 222872401 (7 : ZMod 222872401)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 2), (61909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 2), (61909, 1)] : List FactorBlock).map factorBlockValue).prod) = 222872401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_61909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 222872401) ^ 111436200 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 222872401) ^ 74290800 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 222872401) ^ 44574480 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 222872401) ^ 3600 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_225326671 : Nat.Prime 225326671 := by
  apply lucas_primality 225326671 (6 : ZMod 225326671)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (37, 1), (11941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (37, 1), (11941, 1)] : List FactorBlock).map factorBlockValue).prod) = 225326671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_17
      · exact prime_oneHundredOneCU_37
      · exact prime_oneHundredOneCU_11941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 225326671) ^ 112663335 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 225326671) ^ 75108890 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 225326671) ^ 45065334 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 225326671) ^ 13254510 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 225326671) ^ 6089910 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 225326671) ^ 18870 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_251591311 : Nat.Prime 251591311 := by
  apply lucas_primality 251591311 (39 : ZMod 251591311)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (2795459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (2795459, 1)] : List FactorBlock).map factorBlockValue).prod) = 251591311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_2795459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (39 : ZMod 251591311) ^ 125795655 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (39 : ZMod 251591311) ^ 83863770 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (39 : ZMod 251591311) ^ 50318262 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (39 : ZMod 251591311) ^ 90 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_270033671 : Nat.Prime 270033671 := by
  apply lucas_primality 270033671 (13 : ZMod 270033671)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (27003367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (27003367, 1)] : List FactorBlock).map factorBlockValue).prod) = 270033671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_27003367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 270033671) ^ 135016835 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (13 : ZMod 270033671) ^ 54006734 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (13 : ZMod 270033671) ^ 10 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_296040469 : Nat.Prime 296040469 := by
  apply lucas_primality 296040469 (2 : ZMod 296040469)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (850691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (850691, 1)] : List FactorBlock).map factorBlockValue).prod) = 296040469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_29
      · exact prime_oneHundredOneCU_850691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 296040469) ^ 148020234 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 296040469) ^ 98680156 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 296040469) ^ 10208292 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 296040469) ^ 348 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_309046583 : Nat.Prime 309046583 := by
  apply lucas_primality 309046583 (5 : ZMod 309046583)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 2), (914339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 2), (914339, 1)] : List FactorBlock).map factorBlockValue).prod) = 309046583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_13
      · exact prime_oneHundredOneCU_914339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 309046583) ^ 154523291 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 309046583) ^ 23772814 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 309046583) ^ 338 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_340066117 : Nat.Prime 340066117 := by
  apply lucas_primality 340066117 (6 : ZMod 340066117)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (107, 1), (6791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (107, 1), (6791, 1)] : List FactorBlock).map factorBlockValue).prod) = 340066117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_13
      · exact prime_oneHundredOneCU_107
      · exact prime_oneHundredOneCU_6791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 340066117) ^ 170033058 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 340066117) ^ 113355372 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 340066117) ^ 26158932 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 340066117) ^ 3178188 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 340066117) ^ 50076 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_408782999 : Nat.Prime 408782999 := by
  apply lucas_primality 408782999 (7 : ZMod 408782999)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (1217, 1), (12919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (1217, 1), (12919, 1)] : List FactorBlock).map factorBlockValue).prod) = 408782999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_13
      · exact prime_oneHundredOneCU_1217
      · exact prime_oneHundredOneCU_12919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 408782999) ^ 204391499 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 408782999) ^ 31444846 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 408782999) ^ 335894 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 408782999) ^ 31642 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_421686977 : Nat.Prime 421686977 := by
  apply lucas_primality 421686977 (3 : ZMod 421686977)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (6588859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (6588859, 1)] : List FactorBlock).map factorBlockValue).prod) = 421686977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_6588859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 421686977) ^ 210843488 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 421686977) ^ 64 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_422595493 : Nat.Prime 422595493 := by
  apply lucas_primality 422595493 (5 : ZMod 422595493)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (19, 1), (168499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (19, 1), (168499, 1)] : List FactorBlock).map factorBlockValue).prod) = 422595493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_11
      · exact prime_oneHundredOneCU_19
      · exact prime_oneHundredOneCU_168499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 422595493) ^ 211297746 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 422595493) ^ 140865164 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 422595493) ^ 38417772 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 422595493) ^ 22241868 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 422595493) ^ 2508 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_427802951 : Nat.Prime 427802951 := by
  apply lucas_primality 427802951 (14 : ZMod 427802951)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (8556059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (8556059, 1)] : List FactorBlock).map factorBlockValue).prod) = 427802951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_8556059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (14 : ZMod 427802951) ^ 213901475 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (14 : ZMod 427802951) ^ 85560590 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (14 : ZMod 427802951) ^ 50 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_447937289 : Nat.Prime 447937289 := by
  apply lucas_primality 447937289 (3 : ZMod 447937289)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (55992161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (55992161, 1)] : List FactorBlock).map factorBlockValue).prod) = 447937289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_55992161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 447937289) ^ 223968644 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 447937289) ^ 8 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_461413487 : Nat.Prime 461413487 := by
  apply lucas_primality 461413487 (5 : ZMod 461413487)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (7442153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (7442153, 1)] : List FactorBlock).map factorBlockValue).prod) = 461413487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_31
      · exact prime_oneHundredOneCU_7442153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 461413487) ^ 230706743 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 461413487) ^ 14884306 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 461413487) ^ 62 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_512590963 : Nat.Prime 512590963 := by
  apply lucas_primality 512590963 (2 : ZMod 512590963)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (73, 1), (90023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (73, 1), (90023, 1)] : List FactorBlock).map factorBlockValue).prod) = 512590963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_13
      · exact prime_oneHundredOneCU_73
      · exact prime_oneHundredOneCU_90023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 512590963) ^ 256295481 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 512590963) ^ 170863654 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 512590963) ^ 39430074 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 512590963) ^ 7021794 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 512590963) ^ 5694 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_520800883 : Nat.Prime 520800883 := by
  apply lucas_primality 520800883 (3 : ZMod 520800883)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (17, 1), (729413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (17, 1), (729413, 1)] : List FactorBlock).map factorBlockValue).prod) = 520800883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_17
      · exact prime_oneHundredOneCU_729413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 520800883) ^ 260400441 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 520800883) ^ 173600294 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 520800883) ^ 74400126 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 520800883) ^ 30635346 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 520800883) ^ 714 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_546855641 : Nat.Prime 546855641 := by
  apply lucas_primality 546855641 (3 : ZMod 546855641)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (1801, 1), (7591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (1801, 1), (7591, 1)] : List FactorBlock).map factorBlockValue).prod) = 546855641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_1801
      · exact prime_oneHundredOneCU_7591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 546855641) ^ 273427820 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 546855641) ^ 109371128 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 546855641) ^ 303640 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 546855641) ^ 72040 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_623795071 : Nat.Prime 623795071 := by
  apply lucas_primality 623795071 (6 : ZMod 623795071)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (20793169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (20793169, 1)] : List FactorBlock).map factorBlockValue).prod) = 623795071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_20793169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 623795071) ^ 311897535 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 623795071) ^ 207931690 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 623795071) ^ 124759014 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 623795071) ^ 30 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_746606249 : Nat.Prime 746606249 := by
  apply lucas_primality 746606249 (3 : ZMod 746606249)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (43, 1), (79, 1), (83, 1), (331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (43, 1), (79, 1), (83, 1), (331, 1)] : List FactorBlock).map factorBlockValue).prod) = 746606249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_43
      · exact prime_oneHundredOneCU_79
      · exact prime_oneHundredOneCU_83
      · exact prime_oneHundredOneCU_331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 746606249) ^ 373303124 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 746606249) ^ 17362936 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 746606249) ^ 9450712 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 746606249) ^ 8995256 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 746606249) ^ 2255608 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_765444629 : Nat.Prime 765444629 := by
  apply lucas_primality 765444629 (3 : ZMod 765444629)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (14720089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (14720089, 1)] : List FactorBlock).map factorBlockValue).prod) = 765444629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_13
      · exact prime_oneHundredOneCU_14720089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 765444629) ^ 382722314 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 765444629) ^ 58880356 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 765444629) ^ 52 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_798315283 : Nat.Prime 798315283 := by
  apply lucas_primality 798315283 (2 : ZMod 798315283)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (367, 1), (120847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (367, 1), (120847, 1)] : List FactorBlock).map factorBlockValue).prod) = 798315283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_367
      · exact prime_oneHundredOneCU_120847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 798315283) ^ 399157641 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 798315283) ^ 266105094 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 798315283) ^ 2175246 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 798315283) ^ 6606 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_815200231 : Nat.Prime 815200231 := by
  apply lucas_primality 815200231 (15 : ZMod 815200231)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 2), (160789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 2), (160789, 1)] : List FactorBlock).map factorBlockValue).prod) = 815200231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_13
      · exact prime_oneHundredOneCU_160789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 815200231) ^ 407600115 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (15 : ZMod 815200231) ^ 271733410 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (15 : ZMod 815200231) ^ 163040046 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (15 : ZMod 815200231) ^ 62707710 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (15 : ZMod 815200231) ^ 5070 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_895874579 : Nat.Prime 895874579 := by
  apply lucas_primality 895874579 (2 : ZMod 895874579)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (447937289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (447937289, 1)] : List FactorBlock).map factorBlockValue).prod) = 895874579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_447937289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 895874579) ^ 447937289 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 895874579) ^ 2 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_1078194503 : Nat.Prime 1078194503 := by
  apply lucas_primality 1078194503 (10 : ZMod 1078194503)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (17, 1), (269, 1), (1531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (17, 1), (269, 1), (1531, 1)] : List FactorBlock).map factorBlockValue).prod) = 1078194503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_11
      · exact prime_oneHundredOneCU_17
      · exact prime_oneHundredOneCU_269
      · exact prime_oneHundredOneCU_1531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1078194503) ^ 539097251 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (10 : ZMod 1078194503) ^ 154027786 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (10 : ZMod 1078194503) ^ 98017682 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (10 : ZMod 1078194503) ^ 63423206 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (10 : ZMod 1078194503) ^ 4008158 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (10 : ZMod 1078194503) ^ 704242 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_1085214341 : Nat.Prime 1085214341 := by
  apply lucas_primality 1085214341 (3 : ZMod 1085214341)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (7751531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (7751531, 1)] : List FactorBlock).map factorBlockValue).prod) = 1085214341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_7751531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1085214341) ^ 542607170 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1085214341) ^ 217042868 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1085214341) ^ 155030620 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1085214341) ^ 140 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_1096353761 : Nat.Prime 1096353761 := by
  apply lucas_primality 1096353761 (6 : ZMod 1096353761)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (53, 1), (129287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (53, 1), (129287, 1)] : List FactorBlock).map factorBlockValue).prod) = 1096353761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_53
      · exact prime_oneHundredOneCU_129287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1096353761) ^ 548176880 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 1096353761) ^ 219270752 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 1096353761) ^ 20685920 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 1096353761) ^ 8480 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_1136060269 : Nat.Prime 1136060269 := by
  apply lucas_primality 1136060269 (2 : ZMod 1136060269)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (29, 1), (401, 1), (1163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (29, 1), (401, 1), (1163, 1)] : List FactorBlock).map factorBlockValue).prod) = 1136060269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_29
      · exact prime_oneHundredOneCU_401
      · exact prime_oneHundredOneCU_1163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1136060269) ^ 568030134 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1136060269) ^ 378686756 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1136060269) ^ 162294324 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1136060269) ^ 39174492 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1136060269) ^ 2833068 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1136060269) ^ 976836 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_1395430007 : Nat.Prime 1395430007 := by
  apply lucas_primality 1395430007 (5 : ZMod 1395430007)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (241, 1), (170299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (241, 1), (170299, 1)] : List FactorBlock).map factorBlockValue).prod) = 1395430007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_17
      · exact prime_oneHundredOneCU_241
      · exact prime_oneHundredOneCU_170299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1395430007) ^ 697715003 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1395430007) ^ 82084118 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1395430007) ^ 5790166 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1395430007) ^ 8194 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_1396270049 : Nat.Prime 1396270049 := by
  apply lucas_primality 1396270049 (3 : ZMod 1396270049)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (271, 1), (161009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (271, 1), (161009, 1)] : List FactorBlock).map factorBlockValue).prod) = 1396270049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_271
      · exact prime_oneHundredOneCU_161009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1396270049) ^ 698135024 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1396270049) ^ 5152288 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1396270049) ^ 8672 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_1456004603 : Nat.Prime 1456004603 := by
  apply lucas_primality 1456004603 (2 : ZMod 1456004603)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (79, 1), (307, 1), (2309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (79, 1), (307, 1), (2309, 1)] : List FactorBlock).map factorBlockValue).prod) = 1456004603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_13
      · exact prime_oneHundredOneCU_79
      · exact prime_oneHundredOneCU_307
      · exact prime_oneHundredOneCU_2309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1456004603) ^ 728002301 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1456004603) ^ 112000354 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1456004603) ^ 18430438 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1456004603) ^ 4742686 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1456004603) ^ 630578 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_1523434819 : Nat.Prime 1523434819 := by
  apply lucas_primality 1523434819 (2 : ZMod 1523434819)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (6862319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (6862319, 1)] : List FactorBlock).map factorBlockValue).prod) = 1523434819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_37
      · exact prime_oneHundredOneCU_6862319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1523434819) ^ 761717409 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1523434819) ^ 507811606 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1523434819) ^ 41173914 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1523434819) ^ 222 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_1537170241 : Nat.Prime 1537170241 := by
  apply lucas_primality 1537170241 (14 : ZMod 1537170241)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (1601219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (1601219, 1)] : List FactorBlock).map factorBlockValue).prod) = 1537170241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_1601219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 1537170241) ^ 768585120 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (14 : ZMod 1537170241) ^ 512390080 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (14 : ZMod 1537170241) ^ 307434048 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (14 : ZMod 1537170241) ^ 960 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_1644218969 : Nat.Prime 1644218969 := by
  apply lucas_primality 1644218969 (3 : ZMod 1644218969)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (1061, 1), (27673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (1061, 1), (27673, 1)] : List FactorBlock).map factorBlockValue).prod) = 1644218969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_1061
      · exact prime_oneHundredOneCU_27673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1644218969) ^ 822109484 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1644218969) ^ 234888424 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1644218969) ^ 1549688 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1644218969) ^ 59416 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_1828315421 : Nat.Prime 1828315421 := by
  apply lucas_primality 1828315421 (2 : ZMod 1828315421)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (107, 1), (854353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (107, 1), (854353, 1)] : List FactorBlock).map factorBlockValue).prod) = 1828315421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_107
      · exact prime_oneHundredOneCU_854353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1828315421) ^ 914157710 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1828315421) ^ 365663084 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1828315421) ^ 17087060 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1828315421) ^ 2140 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_1863836719 : Nat.Prime 1863836719 := by
  apply lucas_primality 1863836719 (15 : ZMod 1863836719)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 2), (1074877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 2), (1074877, 1)] : List FactorBlock).map factorBlockValue).prod) = 1863836719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_17
      · exact prime_oneHundredOneCU_1074877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 1863836719) ^ 931918359 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (15 : ZMod 1863836719) ^ 621278906 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (15 : ZMod 1863836719) ^ 109637454 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (15 : ZMod 1863836719) ^ 1734 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_1908690587 : Nat.Prime 1908690587 := by
  apply lucas_primality 1908690587 (5 : ZMod 1908690587)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (47, 1), (71, 1), (25999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (47, 1), (71, 1), (25999, 1)] : List FactorBlock).map factorBlockValue).prod) = 1908690587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_11
      · exact prime_oneHundredOneCU_47
      · exact prime_oneHundredOneCU_71
      · exact prime_oneHundredOneCU_25999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1908690587) ^ 954345293 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1908690587) ^ 173517326 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1908690587) ^ 40610438 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1908690587) ^ 26882966 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1908690587) ^ 73414 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_2023320961 : Nat.Prime 2023320961 := by
  apply lucas_primality 2023320961 (11 : ZMod 2023320961)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (5, 1), (17, 1), (20663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (5, 1), (17, 1), (20663, 1)] : List FactorBlock).map factorBlockValue).prod) = 2023320961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_17
      · exact prime_oneHundredOneCU_20663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2023320961) ^ 1011660480 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (11 : ZMod 2023320961) ^ 674440320 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (11 : ZMod 2023320961) ^ 404664192 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (11 : ZMod 2023320961) ^ 119018880 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (11 : ZMod 2023320961) ^ 97920 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_2145740353 : Nat.Prime 2145740353 := by
  apply lucas_primality 2145740353 (5 : ZMod 2145740353)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (7, 1), (157, 1), (10169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (7, 1), (157, 1), (10169, 1)] : List FactorBlock).map factorBlockValue).prod) = 2145740353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_157
      · exact prime_oneHundredOneCU_10169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2145740353) ^ 1072870176 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2145740353) ^ 715246784 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2145740353) ^ 306534336 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2145740353) ^ 13667136 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2145740353) ^ 211008 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_2243137423 : Nat.Prime 2243137423 := by
  apply lucas_primality 2243137423 (5 : ZMod 2243137423)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (2441, 1), (6659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (2441, 1), (6659, 1)] : List FactorBlock).map factorBlockValue).prod) = 2243137423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_23
      · exact prime_oneHundredOneCU_2441
      · exact prime_oneHundredOneCU_6659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2243137423) ^ 1121568711 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2243137423) ^ 747712474 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2243137423) ^ 97527714 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2243137423) ^ 918942 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2243137423) ^ 336858 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_2705635211 : Nat.Prime 2705635211 := by
  apply lucas_primality 2705635211 (2 : ZMod 2705635211)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (751, 1), (360271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (751, 1), (360271, 1)] : List FactorBlock).map factorBlockValue).prod) = 2705635211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_751
      · exact prime_oneHundredOneCU_360271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2705635211) ^ 1352817605 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2705635211) ^ 541127042 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2705635211) ^ 3602710 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2705635211) ^ 7510 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_3322058167 : Nat.Prime 3322058167 := by
  apply lucas_primality 3322058167 (3 : ZMod 3322058167)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (26365541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (26365541, 1)] : List FactorBlock).map factorBlockValue).prod) = 3322058167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_26365541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3322058167) ^ 1661029083 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3322058167) ^ 1107352722 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3322058167) ^ 474579738 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3322058167) ^ 126 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_3485134333 : Nat.Prime 3485134333 := by
  apply lucas_primality 3485134333 (2 : ZMod 3485134333)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (96809287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (96809287, 1)] : List FactorBlock).map factorBlockValue).prod) = 3485134333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_96809287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3485134333) ^ 1742567166 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3485134333) ^ 1161711444 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3485134333) ^ 36 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_3619491523 : Nat.Prime 3619491523 := by
  apply lucas_primality 3619491523 (2 : ZMod 3619491523)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (35485211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (35485211, 1)] : List FactorBlock).map factorBlockValue).prod) = 3619491523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_17
      · exact prime_oneHundredOneCU_35485211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3619491523) ^ 1809745761 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3619491523) ^ 1206497174 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3619491523) ^ 212911266 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3619491523) ^ 102 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_3975218873 : Nat.Prime 3975218873 := by
  apply lucas_primality 3975218873 (3 : ZMod 3975218873)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (127, 1), (197, 1), (19861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (127, 1), (197, 1), (19861, 1)] : List FactorBlock).map factorBlockValue).prod) = 3975218873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_127
      · exact prime_oneHundredOneCU_197
      · exact prime_oneHundredOneCU_19861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3975218873) ^ 1987609436 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3975218873) ^ 31300936 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3975218873) ^ 20178776 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3975218873) ^ 200152 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_4891201387 : Nat.Prime 4891201387 := by
  apply lucas_primality 4891201387 (2 : ZMod 4891201387)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (815200231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (815200231, 1)] : List FactorBlock).map factorBlockValue).prod) = 4891201387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_815200231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4891201387) ^ 2445600693 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4891201387) ^ 1630400462 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4891201387) ^ 6 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_5355260921 : Nat.Prime 5355260921 := by
  apply lucas_primality 5355260921 (3 : ZMod 5355260921)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (41, 1), (3265403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (41, 1), (3265403, 1)] : List FactorBlock).map factorBlockValue).prod) = 5355260921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_41
      · exact prime_oneHundredOneCU_3265403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5355260921) ^ 2677630460 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 5355260921) ^ 1071052184 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 5355260921) ^ 130616120 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 5355260921) ^ 1640 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_6732583601 : Nat.Prime 6732583601 := by
  apply lucas_primality 6732583601 (3 : ZMod 6732583601)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (16831459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (16831459, 1)] : List FactorBlock).map factorBlockValue).prod) = 6732583601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_16831459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 6732583601) ^ 3366291800 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 6732583601) ^ 1346516720 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 6732583601) ^ 400 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_7087045213 : Nat.Prime 7087045213 := by
  apply lucas_primality 7087045213 (2 : ZMod 7087045213)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (13, 1), (47, 1), (211, 1), (509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (13, 1), (47, 1), (211, 1), (509, 1)] : List FactorBlock).map factorBlockValue).prod) = 7087045213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_13
      · exact prime_oneHundredOneCU_47
      · exact prime_oneHundredOneCU_211
      · exact prime_oneHundredOneCU_509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7087045213) ^ 3543522606 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7087045213) ^ 2362348404 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7087045213) ^ 545157324 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7087045213) ^ 150788196 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7087045213) ^ 33587892 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7087045213) ^ 13923468 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_8792039083 : Nat.Prime 8792039083 := by
  apply lucas_primality 8792039083 (2 : ZMod 8792039083)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (32189, 1), (45523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (32189, 1), (45523, 1)] : List FactorBlock).map factorBlockValue).prod) = 8792039083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_32189
      · exact prime_oneHundredOneCU_45523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8792039083) ^ 4396019541 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 8792039083) ^ 2930679694 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 8792039083) ^ 273138 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 8792039083) ^ 193134 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_8996972903 : Nat.Prime 8996972903 := by
  apply lucas_primality 8996972903 (5 : ZMod 8996972903)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (151, 1), (211, 1), (271, 1), (521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (151, 1), (211, 1), (271, 1), (521, 1)] : List FactorBlock).map factorBlockValue).prod) = 8996972903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_151
      · exact prime_oneHundredOneCU_211
      · exact prime_oneHundredOneCU_271
      · exact prime_oneHundredOneCU_521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 8996972903) ^ 4498486451 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 8996972903) ^ 59582602 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 8996972903) ^ 42639682 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 8996972903) ^ 33199162 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 8996972903) ^ 17268662 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_9892441421 : Nat.Prime 9892441421 := by
  apply lucas_primality 9892441421 (2 : ZMod 9892441421)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (131, 1), (1259, 1), (2999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (131, 1), (1259, 1), (2999, 1)] : List FactorBlock).map factorBlockValue).prod) = 9892441421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_131
      · exact prime_oneHundredOneCU_1259
      · exact prime_oneHundredOneCU_2999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9892441421) ^ 4946220710 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 9892441421) ^ 1978488284 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 9892441421) ^ 75514820 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 9892441421) ^ 7857380 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 9892441421) ^ 3298580 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_10236954319 : Nat.Prime 10236954319 := by
  apply lucas_primality 10236954319 (3 : ZMod 10236954319)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (103, 1), (653, 1), (25367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (103, 1), (653, 1), (25367, 1)] : List FactorBlock).map factorBlockValue).prod) = 10236954319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_103
      · exact prime_oneHundredOneCU_653
      · exact prime_oneHundredOneCU_25367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10236954319) ^ 5118477159 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 10236954319) ^ 3412318106 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 10236954319) ^ 99387906 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 10236954319) ^ 15676806 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 10236954319) ^ 403554 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_11045807161 : Nat.Prime 11045807161 := by
  apply lucas_primality 11045807161 (17 : ZMod 11045807161)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (31, 1), (2969303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (31, 1), (2969303, 1)] : List FactorBlock).map factorBlockValue).prod) = 11045807161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_31
      · exact prime_oneHundredOneCU_2969303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 11045807161) ^ 5522903580 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (17 : ZMod 11045807161) ^ 3681935720 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (17 : ZMod 11045807161) ^ 2209161432 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (17 : ZMod 11045807161) ^ 356316360 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (17 : ZMod 11045807161) ^ 3720 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_11622852517 : Nat.Prime 11622852517 := by
  apply lucas_primality 11622852517 (2 : ZMod 11622852517)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (139, 1), (633467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (139, 1), (633467, 1)] : List FactorBlock).map factorBlockValue).prod) = 11622852517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_11
      · exact prime_oneHundredOneCU_139
      · exact prime_oneHundredOneCU_633467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11622852517) ^ 5811426258 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 11622852517) ^ 3874284172 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 11622852517) ^ 1056622956 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 11622852517) ^ 83617644 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 11622852517) ^ 18348 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_13167424979 : Nat.Prime 13167424979 := by
  apply lucas_primality 13167424979 (2 : ZMod 13167424979)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (44987, 1), (146347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (44987, 1), (146347, 1)] : List FactorBlock).map factorBlockValue).prod) = 13167424979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_44987
      · exact prime_oneHundredOneCU_146347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 13167424979) ^ 6583712489 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 13167424979) ^ 292694 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 13167424979) ^ 89974 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_13288232669 : Nat.Prime 13288232669 := by
  apply lucas_primality 13288232669 (2 : ZMod 13288232669)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3322058167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3322058167, 1)] : List FactorBlock).map factorBlockValue).prod) = 13288232669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3322058167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 13288232669) ^ 6644116334 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 13288232669) ^ 4 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_19462430731 : Nat.Prime 19462430731 := by
  apply lucas_primality 19462430731 (2 : ZMod 19462430731)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (193, 1), (3361387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (193, 1), (3361387, 1)] : List FactorBlock).map factorBlockValue).prod) = 19462430731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_193
      · exact prime_oneHundredOneCU_3361387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 19462430731) ^ 9731215365 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 19462430731) ^ 6487476910 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 19462430731) ^ 3892486146 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 19462430731) ^ 100841610 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 19462430731) ^ 5790 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_21090239767 : Nat.Prime 21090239767 := by
  apply lucas_primality 21090239767 (3 : ZMod 21090239767)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (67, 1), (1201, 1), (14561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (67, 1), (1201, 1), (14561, 1)] : List FactorBlock).map factorBlockValue).prod) = 21090239767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_67
      · exact prime_oneHundredOneCU_1201
      · exact prime_oneHundredOneCU_14561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 21090239767) ^ 10545119883 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 21090239767) ^ 7030079922 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 21090239767) ^ 314779698 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 21090239767) ^ 17560566 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 21090239767) ^ 1448406 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_21643224241 : Nat.Prime 21643224241 := by
  apply lucas_primality 21643224241 (23 : ZMod 21643224241)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (11, 1), (8198191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (11, 1), (8198191, 1)] : List FactorBlock).map factorBlockValue).prod) = 21643224241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_11
      · exact prime_oneHundredOneCU_8198191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 21643224241) ^ 10821612120 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (23 : ZMod 21643224241) ^ 7214408080 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (23 : ZMod 21643224241) ^ 4328644848 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (23 : ZMod 21643224241) ^ 1967565840 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (23 : ZMod 21643224241) ^ 2640 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_22085454877 : Nat.Prime 22085454877 := by
  apply lucas_primality 22085454877 (2 : ZMod 22085454877)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (103, 1), (197, 1), (90703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (103, 1), (197, 1), (90703, 1)] : List FactorBlock).map factorBlockValue).prod) = 22085454877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_103
      · exact prime_oneHundredOneCU_197
      · exact prime_oneHundredOneCU_90703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22085454877) ^ 11042727438 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 22085454877) ^ 7361818292 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 22085454877) ^ 214421892 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 22085454877) ^ 112108908 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 22085454877) ^ 243492 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_22139894719 : Nat.Prime 22139894719 := by
  apply lucas_primality 22139894719 (3 : ZMod 22139894719)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (89, 1), (439, 1), (31481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (89, 1), (439, 1), (31481, 1)] : List FactorBlock).map factorBlockValue).prod) = 22139894719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_89
      · exact prime_oneHundredOneCU_439
      · exact prime_oneHundredOneCU_31481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 22139894719) ^ 11069947359 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 22139894719) ^ 7379964906 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 22139894719) ^ 248762862 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 22139894719) ^ 50432562 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 22139894719) ^ 703278 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_22402025627 : Nat.Prime 22402025627 := by
  apply lucas_primality 22402025627 (2 : ZMod 22402025627)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13331, 1), (840223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13331, 1), (840223, 1)] : List FactorBlock).map factorBlockValue).prod) = 22402025627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_13331
      · exact prime_oneHundredOneCU_840223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 22402025627) ^ 11201012813 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 22402025627) ^ 1680446 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 22402025627) ^ 26662 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_29828882687 : Nat.Prime 29828882687 := by
  apply lucas_primality 29828882687 (5 : ZMod 29828882687)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (19, 1), (46174741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (19, 1), (46174741, 1)] : List FactorBlock).map factorBlockValue).prod) = 29828882687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_17
      · exact prime_oneHundredOneCU_19
      · exact prime_oneHundredOneCU_46174741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 29828882687) ^ 14914441343 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 29828882687) ^ 1754640158 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 29828882687) ^ 1569941194 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 29828882687) ^ 646 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_35137665709 : Nat.Prime 35137665709 := by
  apply lucas_primality 35137665709 (2 : ZMod 35137665709)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (127310383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (127310383, 1)] : List FactorBlock).map factorBlockValue).prod) = 35137665709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_23
      · exact prime_oneHundredOneCU_127310383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 35137665709) ^ 17568832854 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 35137665709) ^ 11712555236 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 35137665709) ^ 1527724596 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 35137665709) ^ 276 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_36092472307 : Nat.Prime 36092472307 := by
  apply lucas_primality 36092472307 (2 : ZMod 36092472307)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (546855641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (546855641, 1)] : List FactorBlock).map factorBlockValue).prod) = 36092472307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_11
      · exact prime_oneHundredOneCU_546855641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 36092472307) ^ 18046236153 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 36092472307) ^ 12030824102 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 36092472307) ^ 3281133846 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 36092472307) ^ 66 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_38071752181 : Nat.Prime 38071752181 := by
  apply lucas_primality 38071752181 (2 : ZMod 38071752181)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (11, 2), (749149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (11, 2), (749149, 1)] : List FactorBlock).map factorBlockValue).prod) = 38071752181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_11
      · exact prime_oneHundredOneCU_749149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 38071752181) ^ 19035876090 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 38071752181) ^ 12690584060 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 38071752181) ^ 7614350436 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 38071752181) ^ 5438821740 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 38071752181) ^ 3461068380 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 38071752181) ^ 50820 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_39532119061 : Nat.Prime 39532119061 := by
  apply lucas_primality 39532119061 (2 : ZMod 39532119061)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 2), (13446299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 2), (13446299, 1)] : List FactorBlock).map factorBlockValue).prod) = 39532119061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_13446299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 39532119061) ^ 19766059530 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 39532119061) ^ 13177373020 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 39532119061) ^ 7906423812 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 39532119061) ^ 5647445580 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 39532119061) ^ 2940 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_41004407819 : Nat.Prime 41004407819 := by
  apply lucas_primality 41004407819 (2 : ZMod 41004407819)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (1863836719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (1863836719, 1)] : List FactorBlock).map factorBlockValue).prod) = 41004407819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_11
      · exact prime_oneHundredOneCU_1863836719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 41004407819) ^ 20502203909 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 41004407819) ^ 3727673438 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 41004407819) ^ 22 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_42842087369 : Nat.Prime 42842087369 := by
  apply lucas_primality 42842087369 (3 : ZMod 42842087369)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5355260921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5355260921, 1)] : List FactorBlock).map factorBlockValue).prod) = 42842087369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5355260921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 42842087369) ^ 21421043684 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 42842087369) ^ 8 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_45905724071 : Nat.Prime 45905724071 := by
  apply lucas_primality 45905724071 (7 : ZMod 45905724071)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (270033671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (270033671, 1)] : List FactorBlock).map factorBlockValue).prod) = 45905724071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_17
      · exact prime_oneHundredOneCU_270033671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 45905724071) ^ 22952862035 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 45905724071) ^ 9181144814 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 45905724071) ^ 2700336710 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 45905724071) ^ 170 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_47932131341 : Nat.Prime 47932131341 := by
  apply lucas_primality 47932131341 (2 : ZMod 47932131341)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (607, 1), (3948281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (607, 1), (3948281, 1)] : List FactorBlock).map factorBlockValue).prod) = 47932131341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_607
      · exact prime_oneHundredOneCU_3948281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 47932131341) ^ 23966065670 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 47932131341) ^ 9586426268 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 47932131341) ^ 78965620 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 47932131341) ^ 12140 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_48070046327 : Nat.Prime 48070046327 := by
  apply lucas_primality 48070046327 (5 : ZMod 48070046327)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (71, 1), (5052559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (71, 1), (5052559, 1)] : List FactorBlock).map factorBlockValue).prod) = 48070046327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_67
      · exact prime_oneHundredOneCU_71
      · exact prime_oneHundredOneCU_5052559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 48070046327) ^ 24035023163 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 48070046327) ^ 717463378 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 48070046327) ^ 677042906 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 48070046327) ^ 9514 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_55942292969 : Nat.Prime 55942292969 := by
  apply lucas_primality 55942292969 (3 : ZMod 55942292969)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (37, 1), (7349, 1), (25717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (37, 1), (7349, 1), (25717, 1)] : List FactorBlock).map factorBlockValue).prod) = 55942292969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_37
      · exact prime_oneHundredOneCU_7349
      · exact prime_oneHundredOneCU_25717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 55942292969) ^ 27971146484 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 55942292969) ^ 1511953864 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 55942292969) ^ 7612232 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 55942292969) ^ 2175304 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_70426246213 : Nat.Prime 70426246213 := by
  apply lucas_primality 70426246213 (6 : ZMod 70426246213)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (5573, 1), (50147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (5573, 1), (50147, 1)] : List FactorBlock).map factorBlockValue).prod) = 70426246213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_5573
      · exact prime_oneHundredOneCU_50147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 70426246213) ^ 35213123106 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 70426246213) ^ 23475415404 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 70426246213) ^ 10060892316 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 70426246213) ^ 12637044 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 70426246213) ^ 1404396 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_77606085077 : Nat.Prime 77606085077 := by
  apply lucas_primality 77606085077 (2 : ZMod 77606085077)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 2), (17, 1), (23, 1), (89, 1), (3299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 2), (17, 1), (23, 1), (89, 1), (3299, 1)] : List FactorBlock).map factorBlockValue).prod) = 77606085077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_13
      · exact prime_oneHundredOneCU_17
      · exact prime_oneHundredOneCU_23
      · exact prime_oneHundredOneCU_89
      · exact prime_oneHundredOneCU_3299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 77606085077) ^ 38803042538 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 77606085077) ^ 5969698852 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 77606085077) ^ 4565063828 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 77606085077) ^ 3374177612 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 77606085077) ^ 871978484 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 77606085077) ^ 23524124 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_84558153293 : Nat.Prime 84558153293 := by
  apply lucas_primality 84558153293 (2 : ZMod 84558153293)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (30011, 1), (704393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (30011, 1), (704393, 1)] : List FactorBlock).map factorBlockValue).prod) = 84558153293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_30011
      · exact prime_oneHundredOneCU_704393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 84558153293) ^ 42279076646 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 84558153293) ^ 2817572 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 84558153293) ^ 120044 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_91811448143 : Nat.Prime 91811448143 := by
  apply lucas_primality 91811448143 (5 : ZMod 91811448143)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (45905724071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (45905724071, 1)] : List FactorBlock).map factorBlockValue).prod) = 91811448143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_45905724071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 91811448143) ^ 45905724071 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 91811448143) ^ 2 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_93741461347 : Nat.Prime 93741461347 := by
  apply lucas_primality 93741461347 (2 : ZMod 93741461347)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (41, 1), (97, 1), (302191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (41, 1), (97, 1), (302191, 1)] : List FactorBlock).map factorBlockValue).prod) = 93741461347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_13
      · exact prime_oneHundredOneCU_41
      · exact prime_oneHundredOneCU_97
      · exact prime_oneHundredOneCU_302191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 93741461347) ^ 46870730673 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 93741461347) ^ 31247153782 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 93741461347) ^ 7210881642 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 93741461347) ^ 2286377106 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 93741461347) ^ 966406818 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 93741461347) ^ 310206 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_93882864989 : Nat.Prime 93882864989 := by
  apply lucas_primality 93882864989 (2 : ZMod 93882864989)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (29, 1), (73575913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (29, 1), (73575913, 1)] : List FactorBlock).map factorBlockValue).prod) = 93882864989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_11
      · exact prime_oneHundredOneCU_29
      · exact prime_oneHundredOneCU_73575913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 93882864989) ^ 46941432494 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 93882864989) ^ 8534805908 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 93882864989) ^ 3237340172 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 93882864989) ^ 1276 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_107280988123 : Nat.Prime 107280988123 := by
  apply lucas_primality 107280988123 (3 : ZMod 107280988123)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (29, 1), (137, 1), (211, 1), (277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (29, 1), (137, 1), (211, 1), (277, 1)] : List FactorBlock).map factorBlockValue).prod) = 107280988123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_11
      · exact prime_oneHundredOneCU_29
      · exact prime_oneHundredOneCU_137
      · exact prime_oneHundredOneCU_211
      · exact prime_oneHundredOneCU_277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 107280988123) ^ 53640494061 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 107280988123) ^ 35760329374 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 107280988123) ^ 15325855446 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 107280988123) ^ 9752817102 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 107280988123) ^ 3699344418 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 107280988123) ^ 783072906 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 107280988123) ^ 508440702 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 107280988123) ^ 387295986 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_113774915941 : Nat.Prime 113774915941 := by
  apply lucas_primality 113774915941 (6 : ZMod 113774915941)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 2), (4019, 1), (9629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 2), (4019, 1), (9629, 1)] : List FactorBlock).map factorBlockValue).prod) = 113774915941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_4019
      · exact prime_oneHundredOneCU_9629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 113774915941) ^ 56887457970 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 113774915941) ^ 37924971980 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 113774915941) ^ 22754983188 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 113774915941) ^ 16253559420 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 113774915941) ^ 28309260 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 113774915941) ^ 11815860 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_144369889229 : Nat.Prime 144369889229 := by
  apply lucas_primality 144369889229 (2 : ZMod 144369889229)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (36092472307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (36092472307, 1)] : List FactorBlock).map factorBlockValue).prod) = 144369889229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_36092472307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 144369889229) ^ 72184944614 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 144369889229) ^ 4 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_163121016269 : Nat.Prime 163121016269 := by
  apply lucas_primality 163121016269 (2 : ZMod 163121016269)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 3), (118892869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 3), (118892869, 1)] : List FactorBlock).map factorBlockValue).prod) = 163121016269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_118892869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 163121016269) ^ 81560508134 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 163121016269) ^ 23303002324 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 163121016269) ^ 1372 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_180916124023 : Nat.Prime 180916124023 := by
  apply lucas_primality 180916124023 (3 : ZMod 180916124023)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (53, 1), (367, 1), (172243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (53, 1), (367, 1), (172243, 1)] : List FactorBlock).map factorBlockValue).prod) = 180916124023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_53
      · exact prime_oneHundredOneCU_367
      · exact prime_oneHundredOneCU_172243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 180916124023) ^ 90458062011 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 180916124023) ^ 60305374674 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 180916124023) ^ 3413511774 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 180916124023) ^ 492959466 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 180916124023) ^ 1050354 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_192748552811 : Nat.Prime 192748552811 := by
  apply lucas_primality 192748552811 (10 : ZMod 192748552811)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (1879, 1), (932549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (1879, 1), (932549, 1)] : List FactorBlock).map factorBlockValue).prod) = 192748552811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_11
      · exact prime_oneHundredOneCU_1879
      · exact prime_oneHundredOneCU_932549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 192748552811) ^ 96374276405 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (10 : ZMod 192748552811) ^ 38549710562 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (10 : ZMod 192748552811) ^ 17522595710 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (10 : ZMod 192748552811) ^ 102580390 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (10 : ZMod 192748552811) ^ 206690 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_203495898157 : Nat.Prime 203495898157 := by
  apply lucas_primality 203495898157 (2 : ZMod 203495898157)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (193, 1), (87865241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (193, 1), (87865241, 1)] : List FactorBlock).map factorBlockValue).prod) = 203495898157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_193
      · exact prime_oneHundredOneCU_87865241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 203495898157) ^ 101747949078 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 203495898157) ^ 67831966052 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 203495898157) ^ 1054382892 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 203495898157) ^ 2316 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_224055886679 : Nat.Prime 224055886679 := by
  apply lucas_primality 224055886679 (7 : ZMod 224055886679)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (379, 1), (3041, 1), (7477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (379, 1), (3041, 1), (7477, 1)] : List FactorBlock).map factorBlockValue).prod) = 224055886679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_13
      · exact prime_oneHundredOneCU_379
      · exact prime_oneHundredOneCU_3041
      · exact prime_oneHundredOneCU_7477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 224055886679) ^ 112027943339 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 224055886679) ^ 17235068206 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 224055886679) ^ 591176482 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 224055886679) ^ 73678358 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 224055886679) ^ 29966014 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_316349930761 : Nat.Prime 316349930761 := by
  apply lucas_primality 316349930761 (13 : ZMod 316349930761)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (191, 1), (13802353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (191, 1), (13802353, 1)] : List FactorBlock).map factorBlockValue).prod) = 316349930761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_191
      · exact prime_oneHundredOneCU_13802353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 316349930761) ^ 158174965380 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (13 : ZMod 316349930761) ^ 105449976920 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (13 : ZMod 316349930761) ^ 63269986152 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (13 : ZMod 316349930761) ^ 1656282360 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (13 : ZMod 316349930761) ^ 22920 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_362835530639 : Nat.Prime 362835530639 := by
  apply lucas_primality 362835530639 (7 : ZMod 362835530639)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (29, 1), (173, 1), (5165801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (29, 1), (173, 1), (5165801, 1)] : List FactorBlock).map factorBlockValue).prod) = 362835530639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_29
      · exact prime_oneHundredOneCU_173
      · exact prime_oneHundredOneCU_5165801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 362835530639) ^ 181417765319 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 362835530639) ^ 51833647234 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 362835530639) ^ 12511570022 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 362835530639) ^ 2097315206 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 362835530639) ^ 70238 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_371683585739 : Nat.Prime 371683585739 := by
  apply lucas_primality 371683585739 (2 : ZMod 371683585739)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (137, 1), (167, 1), (367, 1), (22133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (137, 1), (167, 1), (367, 1), (22133, 1)] : List FactorBlock).map factorBlockValue).prod) = 371683585739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_137
      · exact prime_oneHundredOneCU_167
      · exact prime_oneHundredOneCU_367
      · exact prime_oneHundredOneCU_22133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 371683585739) ^ 185841792869 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 371683585739) ^ 2713018874 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 371683585739) ^ 2225650214 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 371683585739) ^ 1012761814 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 371683585739) ^ 16793186 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_375299503421 : Nat.Prime 375299503421 := by
  apply lucas_primality 375299503421 (3 : ZMod 375299503421)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1499, 1), (12518329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1499, 1), (12518329, 1)] : List FactorBlock).map factorBlockValue).prod) = 375299503421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_1499
      · exact prime_oneHundredOneCU_12518329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 375299503421) ^ 187649751710 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 375299503421) ^ 75059900684 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 375299503421) ^ 250366580 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 375299503421) ^ 29980 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_384357052403 : Nat.Prime 384357052403 := by
  apply lucas_primality 384357052403 (2 : ZMod 384357052403)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1123, 1), (171129587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1123, 1), (171129587, 1)] : List FactorBlock).map factorBlockValue).prod) = 384357052403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_1123
      · exact prime_oneHundredOneCU_171129587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 384357052403) ^ 192178526201 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 384357052403) ^ 342259174 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 384357052403) ^ 2246 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_389046343393 : Nat.Prime 389046343393 := by
  apply lucas_primality 389046343393 (10 : ZMod 389046343393)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (7, 1), (192979337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (7, 1), (192979337, 1)] : List FactorBlock).map factorBlockValue).prod) = 389046343393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_192979337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 389046343393) ^ 194523171696 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (10 : ZMod 389046343393) ^ 129682114464 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (10 : ZMod 389046343393) ^ 55578049056 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (10 : ZMod 389046343393) ^ 2016 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_427001582143 : Nat.Prime 427001582143 := by
  apply lucas_primality 427001582143 (5 : ZMod 427001582143)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (1395430007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (1395430007, 1)] : List FactorBlock).map factorBlockValue).prod) = 427001582143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_17
      · exact prime_oneHundredOneCU_1395430007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 427001582143) ^ 213500791071 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 427001582143) ^ 142333860714 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 427001582143) ^ 25117740126 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 427001582143) ^ 306 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_436468037917 : Nat.Prime 436468037917 := by
  apply lucas_primality 436468037917 (2 : ZMod 436468037917)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (88129, 1), (412717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (88129, 1), (412717, 1)] : List FactorBlock).map factorBlockValue).prod) = 436468037917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_88129
      · exact prime_oneHundredOneCU_412717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 436468037917) ^ 218234018958 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 436468037917) ^ 145489345972 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 436468037917) ^ 4952604 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 436468037917) ^ 1057548 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_502745885183 : Nat.Prime 502745885183 := by
  apply lucas_primality 502745885183 (5 : ZMod 502745885183)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (73, 1), (58363813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (73, 1), (58363813, 1)] : List FactorBlock).map factorBlockValue).prod) = 502745885183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_59
      · exact prime_oneHundredOneCU_73
      · exact prime_oneHundredOneCU_58363813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 502745885183) ^ 251372942591 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 502745885183) ^ 8521116698 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 502745885183) ^ 6886929934 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 502745885183) ^ 8614 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_619854465563 : Nat.Prime 619854465563 := by
  apply lucas_primality 619854465563 (2 : ZMod 619854465563)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (12097, 1), (1507069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (12097, 1), (1507069, 1)] : List FactorBlock).map factorBlockValue).prod) = 619854465563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_17
      · exact prime_oneHundredOneCU_12097
      · exact prime_oneHundredOneCU_1507069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 619854465563) ^ 309927232781 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 619854465563) ^ 36462027386 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 619854465563) ^ 51240346 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 619854465563) ^ 411298 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_678289370107 : Nat.Prime 678289370107 := by
  apply lucas_primality 678289370107 (5 : ZMod 678289370107)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (48437, 1), (63079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (48437, 1), (63079, 1)] : List FactorBlock).map factorBlockValue).prod) = 678289370107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_37
      · exact prime_oneHundredOneCU_48437
      · exact prime_oneHundredOneCU_63079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 678289370107) ^ 339144685053 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 678289370107) ^ 226096456702 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 678289370107) ^ 18332145138 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 678289370107) ^ 14003538 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 678289370107) ^ 10753014 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_789797312651 : Nat.Prime 789797312651 := by
  apply lucas_primality 789797312651 (7 : ZMod 789797312651)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (17, 1), (9241, 1), (100549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (17, 1), (9241, 1), (100549, 1)] : List FactorBlock).map factorBlockValue).prod) = 789797312651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_17
      · exact prime_oneHundredOneCU_9241
      · exact prime_oneHundredOneCU_100549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 789797312651) ^ 394898656325 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 789797312651) ^ 157959462530 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 789797312651) ^ 46458665450 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 789797312651) ^ 85466650 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 789797312651) ^ 7854850 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_826512328771 : Nat.Prime 826512328771 := by
  apply lucas_primality 826512328771 (2 : ZMod 826512328771)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (29, 1), (347, 1), (2737793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (29, 1), (347, 1), (2737793, 1)] : List FactorBlock).map factorBlockValue).prod) = 826512328771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_29
      · exact prime_oneHundredOneCU_347
      · exact prime_oneHundredOneCU_2737793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 826512328771) ^ 413256164385 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 826512328771) ^ 275504109590 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 826512328771) ^ 165302465754 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 826512328771) ^ 28500425130 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 826512328771) ^ 2381879910 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 826512328771) ^ 301890 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_885595788761 : Nat.Prime 885595788761 := by
  apply lucas_primality 885595788761 (3 : ZMod 885595788761)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (22139894719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (22139894719, 1)] : List FactorBlock).map factorBlockValue).prod) = 885595788761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_22139894719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 885595788761) ^ 442797894380 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 885595788761) ^ 177119157752 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 885595788761) ^ 40 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_910037913443 : Nat.Prime 910037913443 := by
  apply lucas_primality 910037913443 (2 : ZMod 910037913443)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (190837, 1), (340619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (190837, 1), (340619, 1)] : List FactorBlock).map factorBlockValue).prod) = 910037913443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_190837
      · exact prime_oneHundredOneCU_340619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 910037913443) ^ 455018956721 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 910037913443) ^ 130005416206 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 910037913443) ^ 4768666 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 910037913443) ^ 2671718 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_1004399463143 : Nat.Prime 1004399463143 := by
  apply lucas_primality 1004399463143 (5 : ZMod 1004399463143)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (1697, 1), (9546253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (1697, 1), (9546253, 1)] : List FactorBlock).map factorBlockValue).prod) = 1004399463143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_31
      · exact prime_oneHundredOneCU_1697
      · exact prime_oneHundredOneCU_9546253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1004399463143) ^ 502199731571 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1004399463143) ^ 32399982682 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1004399463143) ^ 591867686 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1004399463143) ^ 105214 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_1041041991683 : Nat.Prime 1041041991683 := by
  apply lucas_primality 1041041991683 (2 : ZMod 1041041991683)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (30937, 1), (218509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (30937, 1), (218509, 1)] : List FactorBlock).map factorBlockValue).prod) = 1041041991683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_11
      · exact prime_oneHundredOneCU_30937
      · exact prime_oneHundredOneCU_218509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1041041991683) ^ 520520995841 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1041041991683) ^ 148720284526 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1041041991683) ^ 94640181062 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1041041991683) ^ 33650386 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1041041991683) ^ 4764298 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_1085496744139 : Nat.Prime 1085496744139 := by
  apply lucas_primality 1085496744139 (2 : ZMod 1085496744139)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (180916124023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (180916124023, 1)] : List FactorBlock).map factorBlockValue).prod) = 1085496744139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_180916124023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1085496744139) ^ 542748372069 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1085496744139) ^ 361832248046 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1085496744139) ^ 6 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_1091215800893 : Nat.Prime 1091215800893 := by
  apply lucas_primality 1091215800893 (2 : ZMod 1091215800893)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (83, 1), (103, 1), (4558661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (83, 1), (103, 1), (4558661, 1)] : List FactorBlock).map factorBlockValue).prod) = 1091215800893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_83
      · exact prime_oneHundredOneCU_103
      · exact prime_oneHundredOneCU_4558661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1091215800893) ^ 545607900446 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1091215800893) ^ 155887971556 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1091215800893) ^ 13147178324 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1091215800893) ^ 10594328164 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1091215800893) ^ 239372 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_1101737377717 : Nat.Prime 1101737377717 := by
  apply lucas_primality 1101737377717 (2 : ZMod 1101737377717)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (91811448143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (91811448143, 1)] : List FactorBlock).map factorBlockValue).prod) = 1101737377717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_91811448143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1101737377717) ^ 550868688858 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1101737377717) ^ 367245792572 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1101737377717) ^ 12 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_1193892944317 : Nat.Prime 1193892944317 := by
  apply lucas_primality 1193892944317 (2 : ZMod 1193892944317)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2917, 1), (34107329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2917, 1), (34107329, 1)] : List FactorBlock).map factorBlockValue).prod) = 1193892944317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_2917
      · exact prime_oneHundredOneCU_34107329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1193892944317) ^ 596946472158 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1193892944317) ^ 397964314772 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1193892944317) ^ 409287948 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1193892944317) ^ 35004 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_1304022138577 : Nat.Prime 1304022138577 := by
  apply lucas_primality 1304022138577 (5 : ZMod 1304022138577)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (26237, 1), (1035451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (26237, 1), (1035451, 1)] : List FactorBlock).map factorBlockValue).prod) = 1304022138577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_26237
      · exact prime_oneHundredOneCU_1035451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1304022138577) ^ 652011069288 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1304022138577) ^ 434674046192 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1304022138577) ^ 49701648 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1304022138577) ^ 1259376 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_1558167497123 : Nat.Prime 1558167497123 := by
  apply lucas_primality 1558167497123 (2 : ZMod 1558167497123)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (41004407819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (41004407819, 1)] : List FactorBlock).map factorBlockValue).prod) = 1558167497123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_19
      · exact prime_oneHundredOneCU_41004407819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1558167497123) ^ 779083748561 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1558167497123) ^ 82008815638 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1558167497123) ^ 38 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_1592893656587 : Nat.Prime 1592893656587 := by
  apply lucas_primality 1592893656587 (2 : ZMod 1592893656587)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (64279, 1), (728851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (64279, 1), (728851, 1)] : List FactorBlock).map factorBlockValue).prod) = 1592893656587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_17
      · exact prime_oneHundredOneCU_64279
      · exact prime_oneHundredOneCU_728851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1592893656587) ^ 796446828293 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1592893656587) ^ 93699626858 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1592893656587) ^ 24780934 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1592893656587) ^ 2185486 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_2195398511447 : Nat.Prime 2195398511447 := by
  apply lucas_primality 2195398511447 (5 : ZMod 2195398511447)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (22402025627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (22402025627, 1)] : List FactorBlock).map factorBlockValue).prod) = 2195398511447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_22402025627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2195398511447) ^ 1097699255723 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2195398511447) ^ 313628358778 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2195398511447) ^ 98 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_2259895678289 : Nat.Prime 2259895678289 := by
  apply lucas_primality 2259895678289 (3 : ZMod 2259895678289)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (131, 1), (1078194503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (131, 1), (1078194503, 1)] : List FactorBlock).map factorBlockValue).prod) = 2259895678289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_131
      · exact prime_oneHundredOneCU_1078194503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2259895678289) ^ 1129947839144 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2259895678289) ^ 17251112048 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2259895678289) ^ 2096 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_2515613225623 : Nat.Prime 2515613225623 := by
  apply lucas_primality 2515613225623 (6 : ZMod 2515613225623)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (17, 1), (43, 1), (81936461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (17, 1), (43, 1), (81936461, 1)] : List FactorBlock).map factorBlockValue).prod) = 2515613225623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_17
      · exact prime_oneHundredOneCU_43
      · exact prime_oneHundredOneCU_81936461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2515613225623) ^ 1257806612811 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 2515613225623) ^ 838537741874 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 2515613225623) ^ 359373317946 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 2515613225623) ^ 147977248566 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 2515613225623) ^ 58502633154 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 2515613225623) ^ 30702 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_2904487127701 : Nat.Prime 2904487127701 := by
  apply lucas_primality 2904487127701 (2 : ZMod 2904487127701)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (37, 1), (73, 1), (3584459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (37, 1), (73, 1), (3584459, 1)] : List FactorBlock).map factorBlockValue).prod) = 2904487127701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_37
      · exact prime_oneHundredOneCU_73
      · exact prime_oneHundredOneCU_3584459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2904487127701) ^ 1452243563850 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2904487127701) ^ 968162375900 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2904487127701) ^ 580897425540 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2904487127701) ^ 78499652100 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2904487127701) ^ 39787494900 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2904487127701) ^ 810300 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_3071569907281 : Nat.Prime 3071569907281 := by
  apply lucas_primality 3071569907281 (19 : ZMod 3071569907281)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (7, 1), (1828315421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (7, 1), (1828315421, 1)] : List FactorBlock).map factorBlockValue).prod) = 3071569907281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_1828315421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 3071569907281) ^ 1535784953640 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (19 : ZMod 3071569907281) ^ 1023856635760 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (19 : ZMod 3071569907281) ^ 614313981456 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (19 : ZMod 3071569907281) ^ 438795701040 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (19 : ZMod 3071569907281) ^ 1680 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_3148787984161 : Nat.Prime 3148787984161 := by
  apply lucas_primality 3148787984161 (33 : ZMod 3148787984161)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (7, 1), (13, 1), (233, 1), (457, 1), (677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (7, 1), (13, 1), (233, 1), (457, 1), (677, 1)] : List FactorBlock).map factorBlockValue).prod) = 3148787984161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_13
      · exact prime_oneHundredOneCU_233
      · exact prime_oneHundredOneCU_457
      · exact prime_oneHundredOneCU_677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (33 : ZMod 3148787984161) ^ 1574393992080 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (33 : ZMod 3148787984161) ^ 1049595994720 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (33 : ZMod 3148787984161) ^ 629757596832 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (33 : ZMod 3148787984161) ^ 449826854880 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (33 : ZMod 3148787984161) ^ 242214460320 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (33 : ZMod 3148787984161) ^ 13514111520 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (33 : ZMod 3148787984161) ^ 6890126880 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (33 : ZMod 3148787984161) ^ 4651090080 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_5927552406869 : Nat.Prime 5927552406869 := by
  apply lucas_primality 5927552406869 (2 : ZMod 5927552406869)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41, 1), (2897, 1), (12476221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41, 1), (2897, 1), (12476221, 1)] : List FactorBlock).map factorBlockValue).prod) = 5927552406869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_41
      · exact prime_oneHundredOneCU_2897
      · exact prime_oneHundredOneCU_12476221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5927552406869) ^ 2963776203434 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 5927552406869) ^ 144574448948 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 5927552406869) ^ 2046100244 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 5927552406869) ^ 475108 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_6562275747949 : Nat.Prime 6562275747949 := by
  apply lucas_primality 6562275747949 (6 : ZMod 6562275747949)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (25693, 1), (2364917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (25693, 1), (2364917, 1)] : List FactorBlock).map factorBlockValue).prod) = 6562275747949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_25693
      · exact prime_oneHundredOneCU_2364917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 6562275747949) ^ 3281137873974 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 6562275747949) ^ 2187425249316 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 6562275747949) ^ 255411036 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 6562275747949) ^ 2774844 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_6721676600371 : Nat.Prime 6721676600371 := by
  apply lucas_primality 6721676600371 (10 : ZMod 6721676600371)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (224055886679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (224055886679, 1)] : List FactorBlock).map factorBlockValue).prod) = 6721676600371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_224055886679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 6721676600371) ^ 3360838300185 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (10 : ZMod 6721676600371) ^ 2240558866790 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (10 : ZMod 6721676600371) ^ 1344335320074 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (10 : ZMod 6721676600371) ^ 30 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_7121023250987 : Nat.Prime 7121023250987 := by
  apply lucas_primality 7121023250987 (2 : ZMod 7121023250987)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (191, 1), (269, 1), (69298967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (191, 1), (269, 1), (69298967, 1)] : List FactorBlock).map factorBlockValue).prod) = 7121023250987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_191
      · exact prime_oneHundredOneCU_269
      · exact prime_oneHundredOneCU_69298967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7121023250987) ^ 3560511625493 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7121023250987) ^ 37282844246 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7121023250987) ^ 26472205394 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7121023250987) ^ 102758 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_7525424586899 : Nat.Prime 7525424586899 := by
  apply lucas_primality 7525424586899 (2 : ZMod 7525424586899)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (22811, 1), (164951659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (22811, 1), (164951659, 1)] : List FactorBlock).map factorBlockValue).prod) = 7525424586899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_22811
      · exact prime_oneHundredOneCU_164951659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7525424586899) ^ 3762712293449 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7525424586899) ^ 329903318 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7525424586899) ^ 45622 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_8831984532089 : Nat.Prime 8831984532089 := by
  apply lucas_primality 8831984532089 (3 : ZMod 8831984532089)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (557521, 1), (1980191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (557521, 1), (1980191, 1)] : List FactorBlock).map factorBlockValue).prod) = 8831984532089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_557521
      · exact prime_oneHundredOneCU_1980191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 8831984532089) ^ 4415992266044 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 8831984532089) ^ 15841528 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 8831984532089) ^ 4460168 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_10831019656727 : Nat.Prime 10831019656727 := by
  apply lucas_primality 10831019656727 (5 : ZMod 10831019656727)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (109, 1), (3217, 1), (15444071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (109, 1), (3217, 1), (15444071, 1)] : List FactorBlock).map factorBlockValue).prod) = 10831019656727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_109
      · exact prime_oneHundredOneCU_3217
      · exact prime_oneHundredOneCU_15444071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 10831019656727) ^ 5415509828363 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 10831019656727) ^ 99367152814 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 10831019656727) ^ 3366807478 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 10831019656727) ^ 701306 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_11938929443171 : Nat.Prime 11938929443171 := by
  apply lucas_primality 11938929443171 (2 : ZMod 11938929443171)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1193892944317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1193892944317, 1)] : List FactorBlock).map factorBlockValue).prod) = 11938929443171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_1193892944317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11938929443171) ^ 5969464721585 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 11938929443171) ^ 2387785888634 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 11938929443171) ^ 10 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_12516148443823 : Nat.Prime 12516148443823 := by
  apply lucas_primality 12516148443823 (19 : ZMod 12516148443823)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (2557, 1), (42937339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (2557, 1), (42937339, 1)] : List FactorBlock).map factorBlockValue).prod) = 12516148443823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_19
      · exact prime_oneHundredOneCU_2557
      · exact prime_oneHundredOneCU_42937339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 12516148443823) ^ 6258074221911 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (19 : ZMod 12516148443823) ^ 4172049481274 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (19 : ZMod 12516148443823) ^ 658744654938 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (19 : ZMod 12516148443823) ^ 4894856646 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (19 : ZMod 12516148443823) ^ 291498 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_14136004461829 : Nat.Prime 14136004461829 := by
  apply lucas_primality 14136004461829 (2 : ZMod 14136004461829)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (37, 1), (5851, 1), (5441437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (37, 1), (5851, 1), (5441437, 1)] : List FactorBlock).map factorBlockValue).prod) = 14136004461829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_37
      · exact prime_oneHundredOneCU_5851
      · exact prime_oneHundredOneCU_5441437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14136004461829) ^ 7068002230914 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 14136004461829) ^ 4712001487276 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 14136004461829) ^ 382054174644 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 14136004461829) ^ 2415998028 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 14136004461829) ^ 2597844 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_15419884224881 : Nat.Prime 15419884224881 := by
  apply lucas_primality 15419884224881 (3 : ZMod 15419884224881)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (192748552811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (192748552811, 1)] : List FactorBlock).map factorBlockValue).prod) = 15419884224881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_192748552811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 15419884224881) ^ 7709942112440 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 15419884224881) ^ 3083976844976 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 15419884224881) ^ 80 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_26472557913107 : Nat.Prime 26472557913107 := by
  apply lucas_primality 26472557913107 (2 : ZMod 26472557913107)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12073, 1), (1096353761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12073, 1), (1096353761, 1)] : List FactorBlock).map factorBlockValue).prod) = 26472557913107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_12073
      · exact prime_oneHundredOneCU_1096353761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 26472557913107) ^ 13236278956553 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 26472557913107) ^ 2192707522 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 26472557913107) ^ 24146 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_26934866839061 : Nat.Prime 26934866839061 := by
  apply lucas_primality 26934866839061 (3 : ZMod 26934866839061)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (419, 1), (503, 1), (6390029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (419, 1), (503, 1), (6390029, 1)] : List FactorBlock).map factorBlockValue).prod) = 26934866839061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_419
      · exact prime_oneHundredOneCU_503
      · exact prime_oneHundredOneCU_6390029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 26934866839061) ^ 13467433419530 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 26934866839061) ^ 5386973367812 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 26934866839061) ^ 64283691740 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 26934866839061) ^ 53548443020 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 26934866839061) ^ 4215140 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_27096259861261 : Nat.Prime 27096259861261 := by
  apply lucas_primality 27096259861261 (2 : ZMod 27096259861261)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (41, 1), (587, 1), (1861, 1), (3361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (41, 1), (587, 1), (1861, 1), (3361, 1)] : List FactorBlock).map factorBlockValue).prod) = 27096259861261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_41
      · exact prime_oneHundredOneCU_587
      · exact prime_oneHundredOneCU_1861
      · exact prime_oneHundredOneCU_3361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 27096259861261) ^ 13548129930630 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 27096259861261) ^ 9032086620420 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 27096259861261) ^ 5419251972252 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 27096259861261) ^ 660884386860 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 27096259861261) ^ 46160578980 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 27096259861261) ^ 14560053660 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 27096259861261) ^ 8061963660 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_29044871277011 : Nat.Prime 29044871277011 := by
  apply lucas_primality 29044871277011 (6 : ZMod 29044871277011)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (2904487127701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (2904487127701, 1)] : List FactorBlock).map factorBlockValue).prod) = 29044871277011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_2904487127701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 29044871277011) ^ 14522435638505 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 29044871277011) ^ 5808974255402 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 29044871277011) ^ 10 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_33625949378447 : Nat.Prime 33625949378447 := by
  apply lucas_primality 33625949378447 (5 : ZMod 33625949378447)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (449, 1), (32561, 1), (37097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (449, 1), (32561, 1), (37097, 1)] : List FactorBlock).map factorBlockValue).prod) = 33625949378447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_31
      · exact prime_oneHundredOneCU_449
      · exact prime_oneHundredOneCU_32561
      · exact prime_oneHundredOneCU_37097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 33625949378447) ^ 16812974689223 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 33625949378447) ^ 1084708044466 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 33625949378447) ^ 74890755854 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 33625949378447) ^ 1032706286 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 33625949378447) ^ 906433118 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_34482377283527 : Nat.Prime 34482377283527 := by
  apply lucas_primality 34482377283527 (5 : ZMod 34482377283527)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (53, 1), (8792039083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (53, 1), (8792039083, 1)] : List FactorBlock).map factorBlockValue).prod) = 34482377283527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_37
      · exact prime_oneHundredOneCU_53
      · exact prime_oneHundredOneCU_8792039083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 34482377283527) ^ 17241188641763 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 34482377283527) ^ 931956142798 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 34482377283527) ^ 650610892142 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 34482377283527) ^ 3922 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_40913006899649 : Nat.Prime 40913006899649 := by
  apply lucas_primality 40913006899649 (3 : ZMod 40913006899649)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (13, 1), (43, 1), (107, 1), (433, 1), (24683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (13, 1), (43, 1), (107, 1), (433, 1), (24683, 1)] : List FactorBlock).map factorBlockValue).prod) = 40913006899649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_13
      · exact prime_oneHundredOneCU_43
      · exact prime_oneHundredOneCU_107
      · exact prime_oneHundredOneCU_433
      · exact prime_oneHundredOneCU_24683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 40913006899649) ^ 20456503449824 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 40913006899649) ^ 3147154376896 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 40913006899649) ^ 951465276736 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 40913006899649) ^ 382364550464 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 40913006899649) ^ 94487313856 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 40913006899649) ^ 1657537856 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_63225155487427 : Nat.Prime 63225155487427 := by
  apply lucas_primality 63225155487427 (3 : ZMod 63225155487427)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (619854465563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (619854465563, 1)] : List FactorBlock).map factorBlockValue).prod) = 63225155487427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_17
      · exact prime_oneHundredOneCU_619854465563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 63225155487427) ^ 31612577743713 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 63225155487427) ^ 21075051829142 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 63225155487427) ^ 3719126793378 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 63225155487427) ^ 102 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_103412843625659 : Nat.Prime 103412843625659 := by
  apply lucas_primality 103412843625659 (2 : ZMod 103412843625659)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (53, 1), (2971, 1), (6701467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (53, 1), (2971, 1), (6701467, 1)] : List FactorBlock).map factorBlockValue).prod) = 103412843625659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_53
      · exact prime_oneHundredOneCU_2971
      · exact prime_oneHundredOneCU_6701467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 103412843625659) ^ 51706421812829 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 103412843625659) ^ 14773263375094 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 103412843625659) ^ 1951185728786 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 103412843625659) ^ 34807419598 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 103412843625659) ^ 15431374 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_132484946310109 : Nat.Prime 132484946310109 := by
  apply lucas_primality 132484946310109 (2 : ZMod 132484946310109)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 2), (97, 1), (1811, 1), (427541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 2), (97, 1), (1811, 1), (427541, 1)] : List FactorBlock).map factorBlockValue).prod) = 132484946310109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_97
      · exact prime_oneHundredOneCU_1811
      · exact prime_oneHundredOneCU_427541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 132484946310109) ^ 66242473155054 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 132484946310109) ^ 44161648770036 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 132484946310109) ^ 18926420901444 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 132484946310109) ^ 1365824188764 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 132484946310109) ^ 73155685428 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 132484946310109) ^ 309876588 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_148553929284011 : Nat.Prime 148553929284011 := by
  apply lucas_primality 148553929284011 (2 : ZMod 148553929284011)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37, 1), (101, 1), (3975218873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37, 1), (101, 1), (3975218873, 1)] : List FactorBlock).map factorBlockValue).prod) = 148553929284011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_37
      · exact prime_oneHundredOneCU_101
      · exact prime_oneHundredOneCU_3975218873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 148553929284011) ^ 74276964642005 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 148553929284011) ^ 29710785856802 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 148553929284011) ^ 4014971061730 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 148553929284011) ^ 1470830983010 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 148553929284011) ^ 37370 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_156103578345527 : Nat.Prime 156103578345527 := by
  apply lucas_primality 156103578345527 (5 : ZMod 156103578345527)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (1592893656587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (1592893656587, 1)] : List FactorBlock).map factorBlockValue).prod) = 156103578345527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_1592893656587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 156103578345527) ^ 78051789172763 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 156103578345527) ^ 22300511192218 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 156103578345527) ^ 98 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_160539316822649 : Nat.Prime 160539316822649 := by
  apply lucas_primality 160539316822649 (3 : ZMod 160539316822649)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (139, 1), (144369889229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (139, 1), (144369889229, 1)] : List FactorBlock).map factorBlockValue).prod) = 160539316822649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_139
      · exact prime_oneHundredOneCU_144369889229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 160539316822649) ^ 80269658411324 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 160539316822649) ^ 1154959113832 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 160539316822649) ^ 1112 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_192995276509397 : Nat.Prime 192995276509397 := by
  apply lucas_primality 192995276509397 (2 : ZMod 192995276509397)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (1304022138577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (1304022138577, 1)] : List FactorBlock).map factorBlockValue).prod) = 192995276509397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_37
      · exact prime_oneHundredOneCU_1304022138577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 192995276509397) ^ 96497638254698 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 192995276509397) ^ 5216088554308 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 192995276509397) ^ 148 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_202147688107139 : Nat.Prime 202147688107139 := by
  apply lucas_primality 202147688107139 (2 : ZMod 202147688107139)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (743, 1), (8539, 1), (15930997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (743, 1), (8539, 1), (15930997, 1)] : List FactorBlock).map factorBlockValue).prod) = 202147688107139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_743
      · exact prime_oneHundredOneCU_8539
      · exact prime_oneHundredOneCU_15930997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 202147688107139) ^ 101073844053569 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 202147688107139) ^ 272069566766 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 202147688107139) ^ 23673461542 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 202147688107139) ^ 12688954 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_238778588863421 : Nat.Prime 238778588863421 := by
  apply lucas_primality 238778588863421 (2 : ZMod 238778588863421)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11938929443171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11938929443171, 1)] : List FactorBlock).map factorBlockValue).prod) = 238778588863421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_11938929443171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 238778588863421) ^ 119389294431710 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 238778588863421) ^ 47755717772684 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 238778588863421) ^ 20 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_313728829808159 : Nat.Prime 313728829808159 := by
  apply lucas_primality 313728829808159 (23 : ZMod 313728829808159)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (107, 1), (5827, 1), (251591311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (107, 1), (5827, 1), (251591311, 1)] : List FactorBlock).map factorBlockValue).prod) = 313728829808159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_107
      · exact prime_oneHundredOneCU_5827
      · exact prime_oneHundredOneCU_251591311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 313728829808159) ^ 156864414904079 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (23 : ZMod 313728829808159) ^ 2932045138394 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (23 : ZMod 313728829808159) ^ 53840540554 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (23 : ZMod 313728829808159) ^ 1246978 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_388607319411917 : Nat.Prime 388607319411917 := by
  apply lucas_primality 388607319411917 (2 : ZMod 388607319411917)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (8831984532089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (8831984532089, 1)] : List FactorBlock).map factorBlockValue).prod) = 388607319411917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_11
      · exact prime_oneHundredOneCU_8831984532089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 388607319411917) ^ 194303659705958 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 388607319411917) ^ 35327938128356 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 388607319411917) ^ 44 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_471502612935821 : Nat.Prime 471502612935821 := by
  apply lucas_primality 471502612935821 (3 : ZMod 471502612935821)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (257, 1), (5743, 1), (15972841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (257, 1), (5743, 1), (15972841, 1)] : List FactorBlock).map factorBlockValue).prod) = 471502612935821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_257
      · exact prime_oneHundredOneCU_5743
      · exact prime_oneHundredOneCU_15972841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 471502612935821) ^ 235751306467910 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 471502612935821) ^ 94300522587164 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 471502612935821) ^ 1834640517260 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 471502612935821) ^ 82100402740 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 471502612935821) ^ 29519020 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_491455549729351 : Nat.Prime 491455549729351 := by
  apply lucas_primality 491455549729351 (7 : ZMod 491455549729351)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (2063, 1), (6827, 1), (77543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (2063, 1), (6827, 1), (77543, 1)] : List FactorBlock).map factorBlockValue).prod) = 491455549729351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_2063
      · exact prime_oneHundredOneCU_6827
      · exact prime_oneHundredOneCU_77543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 491455549729351) ^ 245727774864675 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 491455549729351) ^ 163818516576450 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 491455549729351) ^ 98291109945870 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 491455549729351) ^ 238223727450 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 491455549729351) ^ 71987044050 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 491455549729351) ^ 6337845450 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_500082339303403 : Nat.Prime 500082339303403 := by
  apply lucas_primality 500082339303403 (3 : ZMod 500082339303403)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (521, 1), (1697, 1), (94269391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (521, 1), (1697, 1), (94269391, 1)] : List FactorBlock).map factorBlockValue).prod) = 500082339303403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_521
      · exact prime_oneHundredOneCU_1697
      · exact prime_oneHundredOneCU_94269391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 500082339303403) ^ 250041169651701 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 500082339303403) ^ 166694113101134 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 500082339303403) ^ 959850939162 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 500082339303403) ^ 294686116266 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 500082339303403) ^ 5304822 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_629588111600621 : Nat.Prime 629588111600621 := by
  apply lucas_primality 629588111600621 (2 : ZMod 629588111600621)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (29, 1), (1085496744139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (29, 1), (1085496744139, 1)] : List FactorBlock).map factorBlockValue).prod) = 629588111600621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_29
      · exact prime_oneHundredOneCU_1085496744139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 629588111600621) ^ 314794055800310 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 629588111600621) ^ 125917622320124 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 629588111600621) ^ 21709934882780 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 629588111600621) ^ 580 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_686379161959607 : Nat.Prime 686379161959607 := by
  apply lucas_primality 686379161959607 (5 : ZMod 686379161959607)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (9767, 1), (35137665709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (9767, 1), (35137665709, 1)] : List FactorBlock).map factorBlockValue).prod) = 686379161959607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_9767
      · exact prime_oneHundredOneCU_35137665709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 686379161959607) ^ 343189580979803 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 686379161959607) ^ 70275331418 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 686379161959607) ^ 19534 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_1099932931520623 : Nat.Prime 1099932931520623 := by
  apply lucas_primality 1099932931520623 (3 : ZMod 1099932931520623)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (19, 1), (47, 1), (79, 1), (96243773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (19, 1), (47, 1), (79, 1), (96243773, 1)] : List FactorBlock).map factorBlockValue).prod) = 1099932931520623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_19
      · exact prime_oneHundredOneCU_47
      · exact prime_oneHundredOneCU_79
      · exact prime_oneHundredOneCU_96243773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1099932931520623) ^ 549966465760311 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1099932931520623) ^ 366644310506874 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1099932931520623) ^ 57891206922138 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1099932931520623) ^ 23402828330226 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1099932931520623) ^ 13923201664818 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1099932931520623) ^ 11428614 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_1126453359944071 : Nat.Prime 1126453359944071 := by
  apply lucas_primality 1126453359944071 (3 : ZMod 1126453359944071)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (12516148443823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (12516148443823, 1)] : List FactorBlock).map factorBlockValue).prod) = 1126453359944071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_12516148443823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1126453359944071) ^ 563226679972035 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1126453359944071) ^ 375484453314690 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1126453359944071) ^ 225290671988814 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1126453359944071) ^ 90 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_1407858394697281 : Nat.Prime 1407858394697281 := by
  apply lucas_primality 1407858394697281 (11 : ZMod 1407858394697281)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 1), (1291, 1), (4523, 1), (83717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 1), (1291, 1), (4523, 1), (83717, 1)] : List FactorBlock).map factorBlockValue).prod) = 1407858394697281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_1291
      · exact prime_oneHundredOneCU_4523
      · exact prime_oneHundredOneCU_83717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1407858394697281) ^ 703929197348640 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (11 : ZMod 1407858394697281) ^ 469286131565760 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (11 : ZMod 1407858394697281) ^ 281571678939456 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (11 : ZMod 1407858394697281) ^ 1090517734080 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (11 : ZMod 1407858394697281) ^ 311266503360 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (11 : ZMod 1407858394697281) ^ 16816875840 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_3103208202618791 : Nat.Prime 3103208202618791 := by
  apply lucas_primality 3103208202618791 (7 : ZMod 3103208202618791)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (37, 1), (341063, 1), (3512987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (37, 1), (341063, 1), (3512987, 1)] : List FactorBlock).map factorBlockValue).prod) = 3103208202618791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_37
      · exact prime_oneHundredOneCU_341063
      · exact prime_oneHundredOneCU_3512987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3103208202618791) ^ 1551604101309395 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 3103208202618791) ^ 620641640523758 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 3103208202618791) ^ 443315457516970 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 3103208202618791) ^ 83870491962670 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 3103208202618791) ^ 9098636330 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 3103208202618791) ^ 883353170 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_3218454217781303 : Nat.Prime 3218454217781303 := by
  apply lucas_primality 3218454217781303 (5 : ZMod 3218454217781303)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (733, 1), (2195398511447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (733, 1), (2195398511447, 1)] : List FactorBlock).map factorBlockValue).prod) = 3218454217781303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_733
      · exact prime_oneHundredOneCU_2195398511447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3218454217781303) ^ 1609227108890651 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3218454217781303) ^ 4390797022894 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3218454217781303) ^ 1466 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_3772020903486569 : Nat.Prime 3772020903486569 := by
  apply lucas_primality 3772020903486569 (3 : ZMod 3772020903486569)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (471502612935821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (471502612935821, 1)] : List FactorBlock).map factorBlockValue).prod) = 3772020903486569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_471502612935821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 3772020903486569) ^ 1886010451743284 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3772020903486569) ^ 8 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_4962342325378469 : Nat.Prime 4962342325378469 := by
  apply lucas_primality 4962342325378469 (2 : ZMod 4962342325378469)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (44909, 1), (746606249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (44909, 1), (746606249, 1)] : List FactorBlock).map factorBlockValue).prod) = 4962342325378469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_37
      · exact prime_oneHundredOneCU_44909
      · exact prime_oneHundredOneCU_746606249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4962342325378469) ^ 2481171162689234 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4962342325378469) ^ 134117360145364 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4962342325378469) ^ 110497724852 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4962342325378469) ^ 6646532 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_5554117740897413 : Nat.Prime 5554117740897413 := by
  apply lucas_primality 5554117740897413 (2 : ZMod 5554117740897413)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (16421, 1), (84558153293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (16421, 1), (84558153293, 1)] : List FactorBlock).map factorBlockValue).prod) = 5554117740897413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_16421
      · exact prime_oneHundredOneCU_84558153293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5554117740897413) ^ 2777058870448706 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 5554117740897413) ^ 338232613172 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 5554117740897413) ^ 65684 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_10659631122050227 : Nat.Prime 10659631122050227 := by
  apply lucas_primality 10659631122050227 (2 : ZMod 10659631122050227)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (769, 1), (1498789, 1), (1541431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (769, 1), (1498789, 1), (1541431, 1)] : List FactorBlock).map factorBlockValue).prod) = 10659631122050227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_769
      · exact prime_oneHundredOneCU_1498789
      · exact prime_oneHundredOneCU_1541431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10659631122050227) ^ 5329815561025113 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 10659631122050227) ^ 3553210374016742 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 10659631122050227) ^ 13861678962354 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 10659631122050227) ^ 7112162634 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 10659631122050227) ^ 6915412446 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_11369929738039441 : Nat.Prime 11369929738039441 := by
  apply lucas_primality 11369929738039441 (22 : ZMod 11369929738039441)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (43, 1), (1101737377717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (43, 1), (1101737377717, 1)] : List FactorBlock).map factorBlockValue).prod) = 11369929738039441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_43
      · exact prime_oneHundredOneCU_1101737377717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 11369929738039441) ^ 5684964869019720 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (22 : ZMod 11369929738039441) ^ 3789976579346480 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (22 : ZMod 11369929738039441) ^ 2273985947607888 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (22 : ZMod 11369929738039441) ^ 264416970652080 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (22 : ZMod 11369929738039441) ^ 10320 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_11681246656954349 : Nat.Prime 11681246656954349 := by
  apply lucas_primality 11681246656954349 (2 : ZMod 11681246656954349)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3209, 1), (910037913443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3209, 1), (910037913443, 1)] : List FactorBlock).map factorBlockValue).prod) = 11681246656954349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3209
      · exact prime_oneHundredOneCU_910037913443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11681246656954349) ^ 5840623328477174 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 11681246656954349) ^ 3640151653772 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 11681246656954349) ^ 12836 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_14354580297007471 : Nat.Prime 14354580297007471 := by
  apply lucas_primality 14354580297007471 (3 : ZMod 14354580297007471)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (4091, 1), (8996972903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (4091, 1), (8996972903, 1)] : List FactorBlock).map factorBlockValue).prod) = 14354580297007471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_13
      · exact prime_oneHundredOneCU_4091
      · exact prime_oneHundredOneCU_8996972903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 14354580297007471) ^ 7177290148503735 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 14354580297007471) ^ 4784860099002490 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 14354580297007471) ^ 2870916059401494 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 14354580297007471) ^ 1104198484385190 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 14354580297007471) ^ 3508819432170 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 14354580297007471) ^ 1595490 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_14981622392240989 : Nat.Prime 14981622392240989 := by
  apply lucas_primality 14981622392240989 (2 : ZMod 14981622392240989)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (113, 1), (1004399463143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (113, 1), (1004399463143, 1)] : List FactorBlock).map factorBlockValue).prod) = 14981622392240989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_11
      · exact prime_oneHundredOneCU_113
      · exact prime_oneHundredOneCU_1004399463143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14981622392240989) ^ 7490811196120494 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 14981622392240989) ^ 4993874130746996 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 14981622392240989) ^ 1361965672021908 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 14981622392240989) ^ 132580729134876 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 14981622392240989) ^ 14916 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_16214789837114723 : Nat.Prime 16214789837114723 := by
  apply lucas_primality 16214789837114723 (2 : ZMod 16214789837114723)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (43, 1), (26934866839061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (43, 1), (26934866839061, 1)] : List FactorBlock).map factorBlockValue).prod) = 16214789837114723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_43
      · exact prime_oneHundredOneCU_26934866839061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 16214789837114723) ^ 8107394918557361 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 16214789837114723) ^ 2316398548159246 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 16214789837114723) ^ 377088135746854 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 16214789837114723) ^ 602 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_29968479920162249 : Nat.Prime 29968479920162249 := by
  apply lucas_primality 29968479920162249 (3 : ZMod 29968479920162249)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (1774067, 1), (124209779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (1774067, 1), (124209779, 1)] : List FactorBlock).map factorBlockValue).prod) = 29968479920162249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_17
      · exact prime_oneHundredOneCU_1774067
      · exact prime_oneHundredOneCU_124209779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 29968479920162249) ^ 14984239960081124 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 29968479920162249) ^ 1762851760009544 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 29968479920162249) ^ 16892529944 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 29968479920162249) ^ 241273112 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_30938768644343827 : Nat.Prime 30938768644343827 := by
  apply lucas_primality 30938768644343827 (2 : ZMod 30938768644343827)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (12379, 1), (129127, 1), (460841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (12379, 1), (129127, 1), (460841, 1)] : List FactorBlock).map factorBlockValue).prod) = 30938768644343827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_12379
      · exact prime_oneHundredOneCU_129127
      · exact prime_oneHundredOneCU_460841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30938768644343827) ^ 15469384322171913 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 30938768644343827) ^ 10312922881447942 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 30938768644343827) ^ 4419824092049118 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 30938768644343827) ^ 2499294663894 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 30938768644343827) ^ 239599531038 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 30938768644343827) ^ 67135451586 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_34939429071901951 : Nat.Prime 34939429071901951 := by
  apply lucas_primality 34939429071901951 (3 : ZMod 34939429071901951)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (4599737, 1), (50639749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (4599737, 1), (50639749, 1)] : List FactorBlock).map factorBlockValue).prod) = 34939429071901951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_4599737
      · exact prime_oneHundredOneCU_50639749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 34939429071901951) ^ 17469714535950975 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 34939429071901951) ^ 11646476357300650 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 34939429071901951) ^ 6987885814380390 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 34939429071901951) ^ 7595962350 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 34939429071901951) ^ 689960550 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_42638524488200909 : Nat.Prime 42638524488200909 := by
  apply lucas_primality 42638524488200909 (2 : ZMod 42638524488200909)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (10659631122050227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (10659631122050227, 1)] : List FactorBlock).map factorBlockValue).prod) = 42638524488200909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_10659631122050227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 42638524488200909) ^ 21319262244100454 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 42638524488200909) ^ 4 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_52956667040469611 : Nat.Prime 52956667040469611 := by
  apply lucas_primality 52956667040469611 (6 : ZMod 52956667040469611)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (1103, 1), (436468037917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (1103, 1), (436468037917, 1)] : List FactorBlock).map factorBlockValue).prod) = 52956667040469611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_11
      · exact prime_oneHundredOneCU_1103
      · exact prime_oneHundredOneCU_436468037917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 52956667040469611) ^ 26478333520234805 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 52956667040469611) ^ 10591333408093922 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 52956667040469611) ^ 4814242458224510 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 52956667040469611) ^ 48011484170870 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 52956667040469611) ^ 121330 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_56789523843429521 : Nat.Prime 56789523843429521 := by
  apply lucas_primality 56789523843429521 (3 : ZMod 56789523843429521)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (11, 1), (13, 2), (29, 1), (13167424979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (11, 1), (13, 2), (29, 1), (13167424979, 1)] : List FactorBlock).map factorBlockValue).prod) = 56789523843429521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_11
      · exact prime_oneHundredOneCU_13
      · exact prime_oneHundredOneCU_29
      · exact prime_oneHundredOneCU_13167424979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 56789523843429521) ^ 28394761921714760 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 56789523843429521) ^ 11357904768685904 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 56789523843429521) ^ 5162683985766320 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 56789523843429521) ^ 4368424911033040 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 56789523843429521) ^ 1958259442876880 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 56789523843429521) ^ 4312880 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_58575574717091693 : Nat.Prime 58575574717091693 := by
  apply lucas_primality 58575574717091693 (2 : ZMod 58575574717091693)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (1126453359944071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (1126453359944071, 1)] : List FactorBlock).map factorBlockValue).prod) = 58575574717091693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_13
      · exact prime_oneHundredOneCU_1126453359944071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 58575574717091693) ^ 29287787358545846 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 58575574717091693) ^ 4505813439776284 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 58575574717091693) ^ 52 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_62779480612992433 : Nat.Prime 62779480612992433 := by
  apply lucas_primality 62779480612992433 (5 : ZMod 62779480612992433)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (1021, 1), (427001582143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (1021, 1), (427001582143, 1)] : List FactorBlock).map factorBlockValue).prod) = 62779480612992433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_1021
      · exact prime_oneHundredOneCU_427001582143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 62779480612992433) ^ 31389740306496216 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 62779480612992433) ^ 20926493537664144 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 62779480612992433) ^ 61488227828592 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 62779480612992433) ^ 147024 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_76731832416789113 : Nat.Prime 76731832416789113 := by
  apply lucas_primality 76731832416789113 (3 : ZMod 76731832416789113)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (4517, 1), (668159, 1), (3178013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (4517, 1), (668159, 1), (3178013, 1)] : List FactorBlock).map factorBlockValue).prod) = 76731832416789113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_4517
      · exact prime_oneHundredOneCU_668159
      · exact prime_oneHundredOneCU_3178013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 76731832416789113) ^ 38365916208394556 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 76731832416789113) ^ 16987343904536 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 76731832416789113) ^ 114840677768 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 76731832416789113) ^ 24144593624 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_78029894988780187 : Nat.Prime 78029894988780187 := by
  apply lucas_primality 78029894988780187 (2 : ZMod 78029894988780187)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (379, 1), (2653481, 1), (12931669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (379, 1), (2653481, 1), (12931669, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029894988780187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_379
      · exact prime_oneHundredOneCU_2653481
      · exact prime_oneHundredOneCU_12931669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 78029894988780187) ^ 39014947494390093 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 78029894988780187) ^ 26009964996260062 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 78029894988780187) ^ 205883627938734 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 78029894988780187) ^ 29406615306 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 78029894988780187) ^ 6034015794 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_85277048976401819 : Nat.Prime 85277048976401819 := by
  apply lucas_primality 85277048976401819 (2 : ZMod 85277048976401819)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (42638524488200909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (42638524488200909, 1)] : List FactorBlock).map factorBlockValue).prod) = 85277048976401819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_42638524488200909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 85277048976401819) ^ 42638524488200909 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 85277048976401819) ^ 2 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_120045680483975713 : Nat.Prime 120045680483975713 := by
  apply lucas_primality 120045680483975713 (5 : ZMod 120045680483975713)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (41, 1), (71, 1), (79, 1), (13921, 1), (130201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (41, 1), (71, 1), (79, 1), (13921, 1), (130201, 1)] : List FactorBlock).map factorBlockValue).prod) = 120045680483975713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_41
      · exact prime_oneHundredOneCU_71
      · exact prime_oneHundredOneCU_79
      · exact prime_oneHundredOneCU_13921
      · exact prime_oneHundredOneCU_130201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 120045680483975713) ^ 60022840241987856 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 120045680483975713) ^ 40015226827991904 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 120045680483975713) ^ 2927943426438432 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 120045680483975713) ^ 1690784232168672 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 120045680483975713) ^ 1519565575746528 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 120045680483975713) ^ 8623351805472 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 120045680483975713) ^ 922002753312 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_140754145579009043 : Nat.Prime 140754145579009043 := by
  apply lucas_primality 140754145579009043 (2 : ZMod 140754145579009043)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (9883, 1), (7121023250987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (9883, 1), (7121023250987, 1)] : List FactorBlock).map factorBlockValue).prod) = 140754145579009043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_9883
      · exact prime_oneHundredOneCU_7121023250987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 140754145579009043) ^ 70377072789504521 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 140754145579009043) ^ 14242046501974 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 140754145579009043) ^ 19766 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_141863753035932383 : Nat.Prime 141863753035932383 := by
  apply lucas_primality 141863753035932383 (5 : ZMod 141863753035932383)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 2), (1423, 1), (197089, 1), (213791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 2), (1423, 1), (197089, 1), (213791, 1)] : List FactorBlock).map factorBlockValue).prod) = 141863753035932383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_13
      · exact prime_oneHundredOneCU_1423
      · exact prime_oneHundredOneCU_197089
      · exact prime_oneHundredOneCU_213791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 141863753035932383) ^ 70931876517966191 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 141863753035932383) ^ 20266250433704626 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 141863753035932383) ^ 10912596387379414 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 141863753035932383) ^ 99693431508034 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 141863753035932383) ^ 719795387038 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 141863753035932383) ^ 663562792802 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_157576823615107861 : Nat.Prime 157576823615107861 := by
  apply lucas_primality 157576823615107861 (2 : ZMod 157576823615107861)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (151, 1), (1699, 1), (10236954319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (151, 1), (1699, 1), (10236954319, 1)] : List FactorBlock).map factorBlockValue).prod) = 157576823615107861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_151
      · exact prime_oneHundredOneCU_1699
      · exact prime_oneHundredOneCU_10236954319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 157576823615107861) ^ 78788411807553930 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 157576823615107861) ^ 52525607871702620 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 157576823615107861) ^ 31515364723021572 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 157576823615107861) ^ 1043555123278860 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 157576823615107861) ^ 92746806130140 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 157576823615107861) ^ 15392940 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_172033178014496741 : Nat.Prime 172033178014496741 := by
  apply lucas_primality 172033178014496741 (2 : ZMod 172033178014496741)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (89, 1), (101, 1), (461, 1), (2657, 1), (781229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (89, 1), (101, 1), (461, 1), (2657, 1), (781229, 1)] : List FactorBlock).map factorBlockValue).prod) = 172033178014496741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_89
      · exact prime_oneHundredOneCU_101
      · exact prime_oneHundredOneCU_461
      · exact prime_oneHundredOneCU_2657
      · exact prime_oneHundredOneCU_781229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 172033178014496741) ^ 86016589007248370 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 172033178014496741) ^ 34406635602899348 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 172033178014496741) ^ 1932957056342660 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 172033178014496741) ^ 1703298792222740 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 172033178014496741) ^ 373173921940340 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 172033178014496741) ^ 64747150174820 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 172033178014496741) ^ 220208387060 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_195608070807371597 : Nat.Prime 195608070807371597 := by
  apply lucas_primality 195608070807371597 (2 : ZMod 195608070807371597)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (41, 2), (1601, 1), (2663, 1), (620303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (41, 2), (1601, 1), (2663, 1), (620303, 1)] : List FactorBlock).map factorBlockValue).prod) = 195608070807371597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_11
      · exact prime_oneHundredOneCU_41
      · exact prime_oneHundredOneCU_1601
      · exact prime_oneHundredOneCU_2663
      · exact prime_oneHundredOneCU_620303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 195608070807371597) ^ 97804035403685798 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 195608070807371597) ^ 17782551891579236 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 195608070807371597) ^ 4770928556277356 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 195608070807371597) ^ 122178682577996 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 195608070807371597) ^ 73454025838292 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 195608070807371597) ^ 315342777332 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_237513540764078233 : Nat.Prime 237513540764078233 := by
  apply lucas_primality 237513540764078233 (5 : ZMod 237513540764078233)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (139, 1), (1583, 1), (72091, 1), (623879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (139, 1), (1583, 1), (72091, 1), (623879, 1)] : List FactorBlock).map factorBlockValue).prod) = 237513540764078233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_139
      · exact prime_oneHundredOneCU_1583
      · exact prime_oneHundredOneCU_72091
      · exact prime_oneHundredOneCU_623879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 237513540764078233) ^ 118756770382039116 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 237513540764078233) ^ 79171180254692744 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 237513540764078233) ^ 1708730509094088 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 237513540764078233) ^ 150040139459304 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 237513540764078233) ^ 3294635124552 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 237513540764078233) ^ 380704496808 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_289559473191628877 : Nat.Prime 289559473191628877 := by
  apply lucas_primality 289559473191628877 (2 : ZMod 289559473191628877)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (83, 1), (1453, 1), (6659, 1), (90141559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (83, 1), (1453, 1), (6659, 1), (90141559, 1)] : List FactorBlock).map factorBlockValue).prod) = 289559473191628877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_83
      · exact prime_oneHundredOneCU_1453
      · exact prime_oneHundredOneCU_6659
      · exact prime_oneHundredOneCU_90141559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 289559473191628877) ^ 144779736595814438 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 289559473191628877) ^ 3488668351706372 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 289559473191628877) ^ 199283876938492 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 289559473191628877) ^ 43483927495364 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 289559473191628877) ^ 3212274964 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_1077871078096232729 : Nat.Prime 1077871078096232729 := by
  apply lucas_primality 1077871078096232729 (3 : ZMod 1077871078096232729)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (11, 1), (101, 1), (27773, 1), (623795071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (11, 1), (101, 1), (27773, 1), (623795071, 1)] : List FactorBlock).map factorBlockValue).prod) = 1077871078096232729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_11
      · exact prime_oneHundredOneCU_101
      · exact prime_oneHundredOneCU_27773
      · exact prime_oneHundredOneCU_623795071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1077871078096232729) ^ 538935539048116364 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1077871078096232729) ^ 153981582585176104 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1077871078096232729) ^ 97988279826930248 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1077871078096232729) ^ 10671990872239928 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1077871078096232729) ^ 38810034137336 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1077871078096232729) ^ 1727924968 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_1510277694830008817 : Nat.Prime 1510277694830008817 := by
  apply lucas_primality 1510277694830008817 (3 : ZMod 1510277694830008817)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (4931, 1), (9461, 1), (2023320961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (4931, 1), (9461, 1), (2023320961, 1)] : List FactorBlock).map factorBlockValue).prod) = 1510277694830008817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_4931
      · exact prime_oneHundredOneCU_9461
      · exact prime_oneHundredOneCU_2023320961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1510277694830008817) ^ 755138847415004408 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1510277694830008817) ^ 306282233792336 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1510277694830008817) ^ 159631930539056 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1510277694830008817) ^ 746435056 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_1920730887743611409 : Nat.Prime 1920730887743611409 := by
  apply lucas_primality 1920730887743611409 (3 : ZMod 1920730887743611409)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (120045680483975713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (120045680483975713, 1)] : List FactorBlock).map factorBlockValue).prod) = 1920730887743611409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_120045680483975713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1920730887743611409) ^ 960365443871805704 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1920730887743611409) ^ 16 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_2083795731702019627 : Nat.Prime 2083795731702019627 := by
  apply lucas_primality 2083795731702019627 (5 : ZMod 2083795731702019627)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (10597, 1), (12113, 1), (2705635211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (10597, 1), (12113, 1), (2705635211, 1)] : List FactorBlock).map factorBlockValue).prod) = 2083795731702019627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_10597
      · exact prime_oneHundredOneCU_12113
      · exact prime_oneHundredOneCU_2705635211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2083795731702019627) ^ 1041897865851009813 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2083795731702019627) ^ 694598577234006542 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2083795731702019627) ^ 196640155865058 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2083795731702019627) ^ 172029697985802 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2083795731702019627) ^ 770168766 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_2155742156192465459 : Nat.Prime 2155742156192465459 := by
  apply lucas_primality 2155742156192465459 (2 : ZMod 2155742156192465459)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1077871078096232729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1077871078096232729, 1)] : List FactorBlock).map factorBlockValue).prod) = 2155742156192465459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_1077871078096232729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 2155742156192465459) ^ 1077871078096232729 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2155742156192465459) ^ 2 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_2406986504562060313 : Nat.Prime 2406986504562060313 := by
  apply lucas_primality 2406986504562060313 (10 : ZMod 2406986504562060313)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (757, 1), (132484946310109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (757, 1), (132484946310109, 1)] : List FactorBlock).map factorBlockValue).prod) = 2406986504562060313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_757
      · exact prime_oneHundredOneCU_132484946310109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2406986504562060313) ^ 1203493252281030156 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (10 : ZMod 2406986504562060313) ^ 802328834854020104 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (10 : ZMod 2406986504562060313) ^ 3179638711442616 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (10 : ZMod 2406986504562060313) ^ 18168 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_3841461775487222819 : Nat.Prime 3841461775487222819 := by
  apply lucas_primality 3841461775487222819 (2 : ZMod 3841461775487222819)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1920730887743611409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1920730887743611409, 1)] : List FactorBlock).map factorBlockValue).prod) = 3841461775487222819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_1920730887743611409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 3841461775487222819) ^ 1920730887743611409 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3841461775487222819) ^ 2 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_3882528953024904883 : Nat.Prime 3882528953024904883 := by
  apply lucas_primality 3882528953024904883 (3 : ZMod 3882528953024904883)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (23, 1), (73, 1), (331, 1), (71399, 1), (776557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (23, 1), (73, 1), (331, 1), (71399, 1), (776557, 1)] : List FactorBlock).map factorBlockValue).prod) = 3882528953024904883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_23
      · exact prime_oneHundredOneCU_73
      · exact prime_oneHundredOneCU_331
      · exact prime_oneHundredOneCU_71399
      · exact prime_oneHundredOneCU_776557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3882528953024904883) ^ 1941264476512452441 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3882528953024904883) ^ 1294176317674968294 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3882528953024904883) ^ 554646993289272126 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3882528953024904883) ^ 168805606653256734 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3882528953024904883) ^ 53185328123628834 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3882528953024904883) ^ 11729694722129622 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3882528953024904883) ^ 54377917800318 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3882528953024904883) ^ 4999670279226 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_5884039990218495737 : Nat.Prime 5884039990218495737 := by
  apply lucas_primality 5884039990218495737 (3 : ZMod 5884039990218495737)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (37, 1), (103, 1), (192995276509397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (37, 1), (103, 1), (192995276509397, 1)] : List FactorBlock).map factorBlockValue).prod) = 5884039990218495737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_37
      · exact prime_oneHundredOneCU_103
      · exact prime_oneHundredOneCU_192995276509397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5884039990218495737) ^ 2942019995109247868 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 5884039990218495737) ^ 159028107843743128 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 5884039990218495737) ^ 57126601846781512 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 5884039990218495737) ^ 30488 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_7029068966051003161 : Nat.Prime 7029068966051003161 := by
  apply lucas_primality 7029068966051003161 (7 : ZMod 7029068966051003161)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (58575574717091693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (58575574717091693, 1)] : List FactorBlock).map factorBlockValue).prod) = 7029068966051003161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_58575574717091693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 7029068966051003161) ^ 3514534483025501580 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 7029068966051003161) ^ 2343022988683667720 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 7029068966051003161) ^ 1405813793210200632 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 7029068966051003161) ^ 120 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_8672224630524127747 : Nat.Prime 8672224630524127747 := by
  apply lucas_primality 8672224630524127747 (2 : ZMod 8672224630524127747)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (173, 1), (491455549729351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (173, 1), (491455549729351, 1)] : List FactorBlock).map factorBlockValue).prod) = 8672224630524127747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_17
      · exact prime_oneHundredOneCU_173
      · exact prime_oneHundredOneCU_491455549729351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8672224630524127747) ^ 4336112315262063873 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 8672224630524127747) ^ 2890741543508042582 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 8672224630524127747) ^ 510130860619066338 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 8672224630524127747) ^ 50128466072393802 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 8672224630524127747) ^ 17646 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_10192856794251677101 : Nat.Prime 10192856794251677101 := by
  apply lucas_primality 10192856794251677101 (6 : ZMod 10192856794251677101)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (193, 1), (2699, 1), (49633, 1), (438049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (193, 1), (2699, 1), (49633, 1), (438049, 1)] : List FactorBlock).map factorBlockValue).prod) = 10192856794251677101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_193
      · exact prime_oneHundredOneCU_2699
      · exact prime_oneHundredOneCU_49633
      · exact prime_oneHundredOneCU_438049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 10192856794251677101) ^ 5096428397125838550 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 10192856794251677101) ^ 3397618931417225700 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 10192856794251677101) ^ 2038571358850335420 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 10192856794251677101) ^ 52812729503894700 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 10192856794251677101) ^ 3776530861152900 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 10192856794251677101) ^ 205364511398700 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 10192856794251677101) ^ 23268759417900 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_10889210149038696451 : Nat.Prime 10889210149038696451 := by
  apply lucas_primality 10889210149038696451 (10 : ZMod 10889210149038696451)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (37, 1), (331, 1), (5927552406869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (37, 1), (331, 1), (5927552406869, 1)] : List FactorBlock).map factorBlockValue).prod) = 10889210149038696451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_37
      · exact prime_oneHundredOneCU_331
      · exact prime_oneHundredOneCU_5927552406869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 10889210149038696451) ^ 5444605074519348225 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (10 : ZMod 10889210149038696451) ^ 3629736716346232150 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (10 : ZMod 10889210149038696451) ^ 2177842029807739290 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (10 : ZMod 10889210149038696451) ^ 294302977001045850 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (10 : ZMod 10889210149038696451) ^ 32897915858122950 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (10 : ZMod 10889210149038696451) ^ 1837050 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_11879833572160177681 : Nat.Prime 11879833572160177681 := by
  apply lucas_primality 11879833572160177681 (11 : ZMod 11879833572160177681)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (7, 1), (977, 1), (1657, 1), (1456004603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (7, 1), (977, 1), (1657, 1), (1456004603, 1)] : List FactorBlock).map factorBlockValue).prod) = 11879833572160177681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_977
      · exact prime_oneHundredOneCU_1657
      · exact prime_oneHundredOneCU_1456004603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 11879833572160177681) ^ 5939916786080088840 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (11 : ZMod 11879833572160177681) ^ 3959944524053392560 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (11 : ZMod 11879833572160177681) ^ 2375966714432035536 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (11 : ZMod 11879833572160177681) ^ 1697119081737168240 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (11 : ZMod 11879833572160177681) ^ 12159502120941840 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (11 : ZMod 11879833572160177681) ^ 7169483145540240 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (11 : ZMod 11879833572160177681) ^ 8159200560 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_30530769037577686333 : Nat.Prime 30530769037577686333 := by
  apply lucas_primality 30530769037577686333 (2 : ZMod 30530769037577686333)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (13, 1), (103, 1), (4649, 1), (19462430731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (13, 1), (103, 1), (4649, 1), (19462430731, 1)] : List FactorBlock).map factorBlockValue).prod) = 30530769037577686333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_13
      · exact prime_oneHundredOneCU_103
      · exact prime_oneHundredOneCU_4649
      · exact prime_oneHundredOneCU_19462430731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30530769037577686333) ^ 15265384518788843166 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 30530769037577686333) ^ 10176923012525895444 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 30530769037577686333) ^ 4361538433939669476 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 30530769037577686333) ^ 2348520695198283564 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 30530769037577686333) ^ 296415233374540644 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 30530769037577686333) ^ 6567169076699868 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 30530769037577686333) ^ 1568702772 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_46717540652959178771 : Nat.Prime 46717540652959178771 := by
  apply lucas_primality 46717540652959178771 (6 : ZMod 46717540652959178771)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (151, 1), (30938768644343827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (151, 1), (30938768644343827, 1)] : List FactorBlock).map factorBlockValue).prod) = 46717540652959178771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_151
      · exact prime_oneHundredOneCU_30938768644343827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 46717540652959178771) ^ 23358770326479589385 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 46717540652959178771) ^ 9343508130591835754 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 46717540652959178771) ^ 309387686443438270 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 46717540652959178771) ^ 1510 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_93435081305918357543 : Nat.Prime 93435081305918357543 := by
  apply lucas_primality 93435081305918357543 (5 : ZMod 93435081305918357543)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (46717540652959178771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (46717540652959178771, 1)] : List FactorBlock).map factorBlockValue).prod) = 93435081305918357543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_46717540652959178771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 93435081305918357543) ^ 46717540652959178771 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 93435081305918357543) ^ 2 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_104847179766746890331 : Nat.Prime 104847179766746890331 := by
  apply lucas_primality 104847179766746890331 (6 : ZMod 104847179766746890331)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (13, 1), (709, 1), (103412843625659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (13, 1), (709, 1), (103412843625659, 1)] : List FactorBlock).map factorBlockValue).prod) = 104847179766746890331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_11
      · exact prime_oneHundredOneCU_13
      · exact prime_oneHundredOneCU_709
      · exact prime_oneHundredOneCU_103412843625659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 104847179766746890331) ^ 52423589883373445165 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 104847179766746890331) ^ 20969435953349378066 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 104847179766746890331) ^ 9531561796976990030 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 104847179766746890331) ^ 8065167674365145410 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 104847179766746890331) ^ 147880366384692370 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (6 : ZMod 104847179766746890331) ^ 1013870 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_116475868590747146491 : Nat.Prime 116475868590747146491 := by
  apply lucas_primality 116475868590747146491 (2 : ZMod 116475868590747146491)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (3882528953024904883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (3882528953024904883, 1)] : List FactorBlock).map factorBlockValue).prod) = 116475868590747146491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_3882528953024904883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 116475868590747146491) ^ 58237934295373573245 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 116475868590747146491) ^ 38825289530249048830 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 116475868590747146491) ^ 23295173718149429298 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 116475868590747146491) ^ 30 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_131239838674706934451 : Nat.Prime 131239838674706934451 := by
  apply lucas_primality 131239838674706934451 (3 : ZMod 131239838674706934451)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (20287, 1), (373231, 1), (115552379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (20287, 1), (373231, 1), (115552379, 1)] : List FactorBlock).map factorBlockValue).prod) = 131239838674706934451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_20287
      · exact prime_oneHundredOneCU_373231
      · exact prime_oneHundredOneCU_115552379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 131239838674706934451) ^ 65619919337353467225 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 131239838674706934451) ^ 43746612891568978150 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 131239838674706934451) ^ 26247967734941386890 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 131239838674706934451) ^ 6469159494982350 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 131239838674706934451) ^ 351631666915950 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 131239838674706934451) ^ 1135760594550 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_142679306740006772599 : Nat.Prime 142679306740006772599 := by
  apply lucas_primality 142679306740006772599 (3 : ZMod 142679306740006772599)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (79, 1), (97, 1), (3103208202618791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (79, 1), (97, 1), (3103208202618791, 1)] : List FactorBlock).map factorBlockValue).prod) = 142679306740006772599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_79
      · exact prime_oneHundredOneCU_97
      · exact prime_oneHundredOneCU_3103208202618791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 142679306740006772599) ^ 71339653370003386299 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 142679306740006772599) ^ 47559768913335590866 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 142679306740006772599) ^ 1806067173924136362 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 142679306740006772599) ^ 1470920688041306934 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 142679306740006772599) ^ 45978 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_182209691898088108321 : Nat.Prime 182209691898088108321 := by
  apply lucas_primality 182209691898088108321 (13 : ZMod 182209691898088108321)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (11, 1), (107, 1), (1589239, 1), (202938553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (11, 1), (107, 1), (1589239, 1), (202938553, 1)] : List FactorBlock).map factorBlockValue).prod) = 182209691898088108321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_11
      · exact prime_oneHundredOneCU_107
      · exact prime_oneHundredOneCU_1589239
      · exact prime_oneHundredOneCU_202938553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 182209691898088108321) ^ 91104845949044054160 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (13 : ZMod 182209691898088108321) ^ 60736563966029369440 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (13 : ZMod 182209691898088108321) ^ 36441938379617621664 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (13 : ZMod 182209691898088108321) ^ 16564517445280737120 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (13 : ZMod 182209691898088108321) ^ 1702894316804561760 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (13 : ZMod 182209691898088108321) ^ 114652164902880 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (13 : ZMod 182209691898088108321) ^ 897856465440 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_223585532239109282381 : Nat.Prime 223585532239109282381 := by
  apply lucas_primality 223585532239109282381 (2 : ZMod 223585532239109282381)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (144051547, 1), (77606085077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (144051547, 1), (77606085077, 1)] : List FactorBlock).map factorBlockValue).prod) = 223585532239109282381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_144051547
      · exact prime_oneHundredOneCU_77606085077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 223585532239109282381) ^ 111792766119554641190 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 223585532239109282381) ^ 44717106447821856476 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 223585532239109282381) ^ 1552121701540 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 223585532239109282381) ^ 2881030940 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_238634753642654320793 : Nat.Prime 238634753642654320793 := by
  apply lucas_primality 238634753642654320793 (3 : ZMod 238634753642654320793)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (37, 1), (41, 1), (677, 1), (29044871277011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (37, 1), (41, 1), (677, 1), (29044871277011, 1)] : List FactorBlock).map factorBlockValue).prod) = 238634753642654320793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_37
      · exact prime_oneHundredOneCU_41
      · exact prime_oneHundredOneCU_677
      · exact prime_oneHundredOneCU_29044871277011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 238634753642654320793) ^ 119317376821327160396 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 238634753642654320793) ^ 6449587936287954616 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 238634753642654320793) ^ 5820359844942788312 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 238634753642654320793) ^ 352488557817805496 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 238634753642654320793) ^ 8216072 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_351134527449510841501 : Nat.Prime 351134527449510841501 := by
  apply lucas_primality 351134527449510841501 (23 : ZMod 351134527449510841501)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 3), (78029894988780187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 3), (78029894988780187, 1)] : List FactorBlock).map factorBlockValue).prod) = 351134527449510841501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_78029894988780187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 351134527449510841501) ^ 175567263724755420750 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (23 : ZMod 351134527449510841501) ^ 117044842483170280500 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (23 : ZMod 351134527449510841501) ^ 70226905489902168300 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (23 : ZMod 351134527449510841501) ^ 4500 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_560610487835510145259 : Nat.Prime 560610487835510145259 := by
  apply lucas_primality 560610487835510145259 (2 : ZMod 560610487835510145259)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (93435081305918357543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (93435081305918357543, 1)] : List FactorBlock).map factorBlockValue).prod) = 560610487835510145259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_93435081305918357543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 560610487835510145259) ^ 280305243917755072629 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 560610487835510145259) ^ 186870162611836715086 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 560610487835510145259) ^ 6 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_868230948038144919379 : Nat.Prime 868230948038144919379 := by
  apply lucas_primality 868230948038144919379 (2 : ZMod 868230948038144919379)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (422595493, 1), (11045807161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (422595493, 1), (11045807161, 1)] : List FactorBlock).map factorBlockValue).prod) = 868230948038144919379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_31
      · exact prime_oneHundredOneCU_422595493
      · exact prime_oneHundredOneCU_11045807161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 868230948038144919379) ^ 434115474019072459689 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 868230948038144919379) ^ 289410316012714973126 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 868230948038144919379) ^ 28007449936714352238 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 868230948038144919379) ^ 2054520131946 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 868230948038144919379) ^ 78602761698 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_1008887329098073834813 : Nat.Prime 1008887329098073834813 := by
  apply lucas_primality 1008887329098073834813 (5 : ZMod 1008887329098073834813)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (2155742156192465459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (2155742156192465459, 1)] : List FactorBlock).map factorBlockValue).prod) = 1008887329098073834813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_13
      · exact prime_oneHundredOneCU_2155742156192465459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1008887329098073834813) ^ 504443664549036917406 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1008887329098073834813) ^ 336295776366024611604 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1008887329098073834813) ^ 77606717622928756524 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1008887329098073834813) ^ 468 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_1284926797586566181219 : Nat.Prime 1284926797586566181219 := by
  apply lucas_primality 1284926797586566181219 (2 : ZMod 1284926797586566181219)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (10889210149038696451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (10889210149038696451, 1)] : List FactorBlock).map factorBlockValue).prod) = 1284926797586566181219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_59
      · exact prime_oneHundredOneCU_10889210149038696451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1284926797586566181219) ^ 642463398793283090609 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1284926797586566181219) ^ 21778420298077392902 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1284926797586566181219) ^ 118 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_1514602684750102772401 : Nat.Prime 1514602684750102772401 := by
  apply lucas_primality 1514602684750102772401 (19 : ZMod 1514602684750102772401)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 2), (17, 1), (47, 1), (277, 1), (6151, 1), (309046583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 2), (17, 1), (47, 1), (277, 1), (6151, 1), (309046583, 1)] : List FactorBlock).map factorBlockValue).prod) = 1514602684750102772401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_17
      · exact prime_oneHundredOneCU_47
      · exact prime_oneHundredOneCU_277
      · exact prime_oneHundredOneCU_6151
      · exact prime_oneHundredOneCU_309046583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 1514602684750102772401) ^ 757301342375051386200 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (19 : ZMod 1514602684750102772401) ^ 504867561583367590800 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (19 : ZMod 1514602684750102772401) ^ 302920536950020554480 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (19 : ZMod 1514602684750102772401) ^ 89094275573535457200 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (19 : ZMod 1514602684750102772401) ^ 32225589037236229200 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (19 : ZMod 1514602684750102772401) ^ 5467879728339721200 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (19 : ZMod 1514602684750102772401) ^ 246236820801512400 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (19 : ZMod 1514602684750102772401) ^ 4900887982800 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_1924533038689948784323 : Nat.Prime 1924533038689948784323 := by
  apply lucas_primality 1924533038689948784323 (2 : ZMod 1924533038689948784323)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (11879833572160177681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (11879833572160177681, 1)] : List FactorBlock).map factorBlockValue).prod) = 1924533038689948784323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_11879833572160177681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1924533038689948784323) ^ 962266519344974392161 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1924533038689948784323) ^ 641511012896649594774 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1924533038689948784323) ^ 162 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_1927933678345985788007 : Nat.Prime 1927933678345985788007 := by
  apply lucas_primality 1927933678345985788007 (5 : ZMod 1927933678345985788007)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2141, 1), (6393091, 1), (70426246213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2141, 1), (6393091, 1), (70426246213, 1)] : List FactorBlock).map factorBlockValue).prod) = 1927933678345985788007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_2141
      · exact prime_oneHundredOneCU_6393091
      · exact prime_oneHundredOneCU_70426246213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1927933678345985788007) ^ 963966839172992894003 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1927933678345985788007) ^ 900482801656228766 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1927933678345985788007) ^ 301565186284066 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1927933678345985788007) ^ 27375215662 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_3306613028999647775719 : Nat.Prime 3306613028999647775719 := by
  apply lucas_primality 3306613028999647775719 (3 : ZMod 3306613028999647775719)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (797, 1), (16901, 1), (40913006899649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (797, 1), (16901, 1), (40913006899649, 1)] : List FactorBlock).map factorBlockValue).prod) = 3306613028999647775719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_797
      · exact prime_oneHundredOneCU_16901
      · exact prime_oneHundredOneCU_40913006899649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3306613028999647775719) ^ 1653306514499823887859 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3306613028999647775719) ^ 1102204342999882591906 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3306613028999647775719) ^ 4148824377665806494 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3306613028999647775719) ^ 195645998994121518 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3306613028999647775719) ^ 80820582 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_3994672005467173983811 : Nat.Prime 3994672005467173983811 := by
  apply lucas_primality 3994672005467173983811 (2 : ZMod 3994672005467173983811)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (13, 1), (37, 1), (67057, 1), (375299503421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (13, 1), (37, 1), (67057, 1), (375299503421, 1)] : List FactorBlock).map factorBlockValue).prod) = 3994672005467173983811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_11
      · exact prime_oneHundredOneCU_13
      · exact prime_oneHundredOneCU_37
      · exact prime_oneHundredOneCU_67057
      · exact prime_oneHundredOneCU_375299503421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3994672005467173983811) ^ 1997336002733586991905 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3994672005467173983811) ^ 1331557335155724661270 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3994672005467173983811) ^ 798934401093434796762 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3994672005467173983811) ^ 363152000497015816710 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3994672005467173983811) ^ 307282461959013383370 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3994672005467173983811) ^ 107964108255869567130 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3994672005467173983811) ^ 59571290178015330 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3994672005467173983811) ^ 10643957610 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_6686696990544804841133 : Nat.Prime 6686696990544804841133 := by
  apply lucas_primality 6686696990544804841133 (2 : ZMod 6686696990544804841133)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (37, 1), (34549, 1), (358711, 1), (520800883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (37, 1), (34549, 1), (358711, 1), (520800883, 1)] : List FactorBlock).map factorBlockValue).prod) = 6686696990544804841133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_37
      · exact prime_oneHundredOneCU_34549
      · exact prime_oneHundredOneCU_358711
      · exact prime_oneHundredOneCU_520800883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6686696990544804841133) ^ 3343348495272402420566 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 6686696990544804841133) ^ 955242427220686405876 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 6686696990544804841133) ^ 180721540284994725436 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 6686696990544804841133) ^ 193542417741318268 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 6686696990544804841133) ^ 18640903096210612 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 6686696990544804841133) ^ 12839258167204 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_6796910637026829926309 : Nat.Prime 6796910637026829926309 := by
  apply lucas_primality 6796910637026829926309 (2 : ZMod 6796910637026829926309)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (10141, 1), (1108957, 1), (11622852517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (10141, 1), (1108957, 1), (11622852517, 1)] : List FactorBlock).map factorBlockValue).prod) = 6796910637026829926309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_13
      · exact prime_oneHundredOneCU_10141
      · exact prime_oneHundredOneCU_1108957
      · exact prime_oneHundredOneCU_11622852517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6796910637026829926309) ^ 3398455318513414963154 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 6796910637026829926309) ^ 522839279771294609716 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 6796910637026829926309) ^ 670240670252127988 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 6796910637026829926309) ^ 6129102063494644 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 6796910637026829926309) ^ 584788512724 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_6988924923761760467041 : Nat.Prime 6988924923761760467041 := by
  apply lucas_primality 6988924923761760467041 (19 : ZMod 6988924923761760467041)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (7, 1), (421686977, 1), (1644218969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (7, 1), (421686977, 1), (1644218969, 1)] : List FactorBlock).map factorBlockValue).prod) = 6988924923761760467041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_421686977
      · exact prime_oneHundredOneCU_1644218969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 6988924923761760467041) ^ 3494462461880880233520 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (19 : ZMod 6988924923761760467041) ^ 2329641641253920155680 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (19 : ZMod 6988924923761760467041) ^ 1397784984752352093408 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (19 : ZMod 6988924923761760467041) ^ 998417846251680066720 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (19 : ZMod 6988924923761760467041) ^ 16573727207520 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (19 : ZMod 6988924923761760467041) ^ 4250604728160 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_10755327207134324270111 : Nat.Prime 10755327207134324270111 := by
  apply lucas_primality 10755327207134324270111 (17 : ZMod 10755327207134324270111)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (2011, 1), (174121, 1), (3071569907281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (2011, 1), (174121, 1), (3071569907281, 1)] : List FactorBlock).map factorBlockValue).prod) = 10755327207134324270111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_2011
      · exact prime_oneHundredOneCU_174121
      · exact prime_oneHundredOneCU_3071569907281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 10755327207134324270111) ^ 5377663603567162135055 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (17 : ZMod 10755327207134324270111) ^ 2151065441426864854022 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (17 : ZMod 10755327207134324270111) ^ 5348248238256750010 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (17 : ZMod 10755327207134324270111) ^ 61769270835420910 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (17 : ZMod 10755327207134324270111) ^ 3501573310 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_11524550401976386038721 : Nat.Prime 11524550401976386038721 := by
  apply lucas_primality 11524550401976386038721 (11 : ZMod 11524550401976386038721)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (17, 1), (1291, 1), (4418749, 1), (123787919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (17, 1), (1291, 1), (4418749, 1), (123787919, 1)] : List FactorBlock).map factorBlockValue).prod) = 11524550401976386038721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_17
      · exact prime_oneHundredOneCU_1291
      · exact prime_oneHundredOneCU_4418749
      · exact prime_oneHundredOneCU_123787919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 11524550401976386038721) ^ 5762275200988193019360 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (11 : ZMod 11524550401976386038721) ^ 3841516800658795346240 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (11 : ZMod 11524550401976386038721) ^ 2304910080395277207744 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (11 : ZMod 11524550401976386038721) ^ 677914729528022708160 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (11 : ZMod 11524550401976386038721) ^ 8926839970547161920 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (11 : ZMod 11524550401976386038721) ^ 2608102519961280 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (11 : ZMod 11524550401976386038721) ^ 93099152930880 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_15772547244995605471613 : Nat.Prime 15772547244995605471613 := by
  apply lucas_primality 15772547244995605471613 (2 : ZMod 15772547244995605471613)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (89, 1), (251, 1), (66333929, 1), (91758097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (89, 1), (251, 1), (66333929, 1), (91758097, 1)] : List FactorBlock).map factorBlockValue).prod) = 15772547244995605471613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_29
      · exact prime_oneHundredOneCU_89
      · exact prime_oneHundredOneCU_251
      · exact prime_oneHundredOneCU_66333929
      · exact prime_oneHundredOneCU_91758097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15772547244995605471613) ^ 7886273622497802735806 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 15772547244995605471613) ^ 543880939482607085228 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 15772547244995605471613) ^ 177219631966242758108 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 15772547244995605471613) ^ 62838833645400818612 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 15772547244995605471613) ^ 237774958950428 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 15772547244995605471613) ^ 171892702231996 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_37917427274616238815721 : Nat.Prime 37917427274616238815721 := by
  apply lucas_primality 37917427274616238815721 (7 : ZMod 37917427274616238815721)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (31, 1), (10192856794251677101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (31, 1), (10192856794251677101, 1)] : List FactorBlock).map factorBlockValue).prod) = 37917427274616238815721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_31
      · exact prime_oneHundredOneCU_10192856794251677101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 37917427274616238815721) ^ 18958713637308119407860 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 37917427274616238815721) ^ 12639142424872079605240 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 37917427274616238815721) ^ 7583485454923247763144 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 37917427274616238815721) ^ 1223142815310201252120 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 37917427274616238815721) ^ 3720 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_52152917699514745816679 : Nat.Prime 52152917699514745816679 := by
  apply lucas_primality 52152917699514745816679 (7 : ZMod 52152917699514745816679)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2731, 1), (222872401, 1), (42842087369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2731, 1), (222872401, 1), (42842087369, 1)] : List FactorBlock).map factorBlockValue).prod) = 52152917699514745816679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_2731
      · exact prime_oneHundredOneCU_222872401
      · exact prime_oneHundredOneCU_42842087369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 52152917699514745816679) ^ 26076458849757372908339 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 52152917699514745816679) ^ 19096637751561605938 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 52152917699514745816679) ^ 234003481209478 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 52152917699514745816679) ^ 1217329054262 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_55119932390541623699723 : Nat.Prime 55119932390541623699723 := by
  apply lucas_primality 55119932390541623699723 (2 : ZMod 55119932390541623699723)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (163, 1), (18917, 1), (388607319411917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (163, 1), (18917, 1), (388607319411917, 1)] : List FactorBlock).map factorBlockValue).prod) = 55119932390541623699723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_23
      · exact prime_oneHundredOneCU_163
      · exact prime_oneHundredOneCU_18917
      · exact prime_oneHundredOneCU_388607319411917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 55119932390541623699723) ^ 27559966195270811849861 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 55119932390541623699723) ^ 2396518799588766247814 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 55119932390541623699723) ^ 338159094420500758894 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 55119932390541623699723) ^ 2913777680950553666 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 55119932390541623699723) ^ 141839666 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_138294604823716632464653 : Nat.Prime 138294604823716632464653 := by
  apply lucas_primality 138294604823716632464653 (5 : ZMod 138294604823716632464653)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11524550401976386038721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11524550401976386038721, 1)] : List FactorBlock).map factorBlockValue).prod) = 138294604823716632464653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_11524550401976386038721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 138294604823716632464653) ^ 69147302411858316232326 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 138294604823716632464653) ^ 46098201607905544154884 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 138294604823716632464653) ^ 12 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_166700342023323824520769 : Nat.Prime 166700342023323824520769 := by
  apply lucas_primality 166700342023323824520769 (7 : ZMod 166700342023323824520769)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (868230948038144919379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (868230948038144919379, 1)] : List FactorBlock).map factorBlockValue).prod) = 166700342023323824520769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_868230948038144919379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 166700342023323824520769) ^ 83350171011661912260384 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 166700342023323824520769) ^ 55566780674441274840256 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 166700342023323824520769) ^ 192 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_184280188733184251581693 : Nat.Prime 184280188733184251581693 := by
  apply lucas_primality 184280188733184251581693 (2 : ZMod 184280188733184251581693)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (13, 1), (179, 1), (404533, 1), (580231, 1), (4016503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (13, 1), (179, 1), (404533, 1), (580231, 1), (4016503, 1)] : List FactorBlock).map factorBlockValue).prod) = 184280188733184251581693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_7
      · exact prime_oneHundredOneCU_13
      · exact prime_oneHundredOneCU_179
      · exact prime_oneHundredOneCU_404533
      · exact prime_oneHundredOneCU_580231
      · exact prime_oneHundredOneCU_4016503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 184280188733184251581693) ^ 92140094366592125790846 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 184280188733184251581693) ^ 61426729577728083860564 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 184280188733184251581693) ^ 26325741247597750225956 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 184280188733184251581693) ^ 14175399133321865506284 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 184280188733184251581693) ^ 1029498261079241628948 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 184280188733184251581693) ^ 455538086468061324 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 184280188733184251581693) ^ 317597971727095332 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 184280188733184251581693) ^ 45880754659758564 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_259350142684843848646979 : Nat.Prime 259350142684843848646979 := by
  apply lucas_primality 259350142684843848646979 (2 : ZMod 259350142684843848646979)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (15227, 1), (9725489, 1), (38071752181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (15227, 1), (9725489, 1), (38071752181, 1)] : List FactorBlock).map factorBlockValue).prod) = 259350142684843848646979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_23
      · exact prime_oneHundredOneCU_15227
      · exact prime_oneHundredOneCU_9725489
      · exact prime_oneHundredOneCU_38071752181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 259350142684843848646979) ^ 129675071342421924323489 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 259350142684843848646979) ^ 11276093160210602115086 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 259350142684843848646979) ^ 17032254724163909414 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 259350142684843848646979) ^ 26667054241164002 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 259350142684843848646979) ^ 6812140966138 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_1067094621981796993937923 : Nat.Prime 1067094621981796993937923 := by
  apply lucas_primality 1067094621981796993937923 (2 : ZMod 1067094621981796993937923)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1033807, 1), (172033178014496741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1033807, 1), (172033178014496741, 1)] : List FactorBlock).map factorBlockValue).prod) = 1067094621981796993937923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_1033807
      · exact prime_oneHundredOneCU_172033178014496741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1067094621981796993937923) ^ 533547310990898496968961 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1067094621981796993937923) ^ 355698207327265664645974 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1067094621981796993937923) ^ 1032199068086980446 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1067094621981796993937923) ^ 6202842 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_1188894085788952929882887 : Nat.Prime 1188894085788952929882887 := by
  apply lucas_primality 1188894085788952929882887 (10 : ZMod 1188894085788952929882887)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (17, 1), (409, 1), (563, 1), (11681246656954349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (17, 1), (409, 1), (563, 1), (11681246656954349, 1)] : List FactorBlock).map factorBlockValue).prod) = 1188894085788952929882887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_13
      · exact prime_oneHundredOneCU_17
      · exact prime_oneHundredOneCU_409
      · exact prime_oneHundredOneCU_563
      · exact prime_oneHundredOneCU_11681246656954349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1188894085788952929882887) ^ 594447042894476464941443 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (10 : ZMod 1188894085788952929882887) ^ 91453391214534840760222 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (10 : ZMod 1188894085788952929882887) ^ 69934946222879584110758 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (10 : ZMod 1188894085788952929882887) ^ 2906831505596461931254 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (10 : ZMod 1188894085788952929882887) ^ 2111712408150893303522 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (10 : ZMod 1188894085788952929882887) ^ 101778014 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_3112201712218126183763749 : Nat.Prime 3112201712218126183763749 := by
  apply lucas_primality 3112201712218126183763749 (7 : ZMod 3112201712218126183763749)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (259350142684843848646979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (259350142684843848646979, 1)] : List FactorBlock).map factorBlockValue).prod) = 3112201712218126183763749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_259350142684843848646979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 3112201712218126183763749) ^ 1556100856109063091881874 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 3112201712218126183763749) ^ 1037400570739375394587916 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (7 : ZMod 3112201712218126183763749) ^ 12 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_21897846193725484213945997 : Nat.Prime 21897846193725484213945997 := by
  apply lucas_primality 21897846193725484213945997 (2 : ZMod 21897846193725484213945997)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (509, 1), (10755327207134324270111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (509, 1), (10755327207134324270111, 1)] : List FactorBlock).map factorBlockValue).prod) = 21897846193725484213945997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_509
      · exact prime_oneHundredOneCU_10755327207134324270111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 21897846193725484213945997) ^ 10948923096862742106972998 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 21897846193725484213945997) ^ 43021308828537297080444 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 21897846193725484213945997) ^ 2036 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_24850979249611876257783043 : Nat.Prime 24850979249611876257783043 := by
  apply lucas_primality 24850979249611876257783043 (3 : ZMod 24850979249611876257783043)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (13, 1), (223, 1), (373, 1), (141863753035932383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (13, 1), (223, 1), (373, 1), (141863753035932383, 1)] : List FactorBlock).map factorBlockValue).prod) = 24850979249611876257783043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_13
      · exact prime_oneHundredOneCU_223
      · exact prime_oneHundredOneCU_373
      · exact prime_oneHundredOneCU_141863753035932383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 24850979249611876257783043) ^ 12425489624805938128891521 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 24850979249611876257783043) ^ 8283659749870625419261014 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 24850979249611876257783043) ^ 1911613788431682789060234 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 24850979249611876257783043) ^ 111439368832340252277054 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 24850979249611876257783043) ^ 66624609248289212487354 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 24850979249611876257783043) ^ 175174974 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_27312203864223482483679671 : Nat.Prime 27312203864223482483679671 := by
  apply lucas_primality 27312203864223482483679671 (13 : ZMod 27312203864223482483679671)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (47, 1), (84663223, 1), (686379161959607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (47, 1), (84663223, 1), (686379161959607, 1)] : List FactorBlock).map factorBlockValue).prod) = 27312203864223482483679671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_47
      · exact prime_oneHundredOneCU_84663223
      · exact prime_oneHundredOneCU_686379161959607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 27312203864223482483679671) ^ 13656101932111741241839835 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (13 : ZMod 27312203864223482483679671) ^ 5462440772844696496735934 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (13 : ZMod 27312203864223482483679671) ^ 581110720515393244333610 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (13 : ZMod 27312203864223482483679671) ^ 322598206121015290 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (13 : ZMod 27312203864223482483679671) ^ 39791714810 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_128951355609487111683204667 : Nat.Prime 128951355609487111683204667 := by
  apply lucas_primality 128951355609487111683204667 (3 : ZMod 128951355609487111683204667)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (151, 1), (911, 1), (108947, 1), (15419884224881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (151, 1), (911, 1), (108947, 1), (15419884224881, 1)] : List FactorBlock).map factorBlockValue).prod) = 128951355609487111683204667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_31
      · exact prime_oneHundredOneCU_151
      · exact prime_oneHundredOneCU_911
      · exact prime_oneHundredOneCU_108947
      · exact prime_oneHundredOneCU_15419884224881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 128951355609487111683204667) ^ 64475677804743555841602333 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 128951355609487111683204667) ^ 42983785203162370561068222 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 128951355609487111683204667) ^ 4159721148693132634942086 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 128951355609487111683204667) ^ 853982487480047097239766 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 128951355609487111683204667) ^ 141549237771116478247206 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 128951355609487111683204667) ^ 1183615479173241224478 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 128951355609487111683204667) ^ 8362666912986 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_147783360512852803735949903 : Nat.Prime 147783360512852803735949903 := by
  apply lucas_primality 147783360512852803735949903 (5 : ZMod 147783360512852803735949903)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (2228687, 1), (37239551, 1), (13288232669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (2228687, 1), (37239551, 1), (13288232669, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803735949903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_67
      · exact prime_oneHundredOneCU_2228687
      · exact prime_oneHundredOneCU_37239551
      · exact prime_oneHundredOneCU_13288232669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 147783360512852803735949903) ^ 73891680256426401867974951 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 147783360512852803735949903) ^ 2205721798699295578148506 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 147783360512852803735949903) ^ 66309607635730276946 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 147783360512852803735949903) ^ 3968451727918330802 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 147783360512852803735949903) ^ 11121370628737958 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_177427868193737095718644163 : Nat.Prime 177427868193737095718644163 := by
  apply lucas_primality 177427868193737095718644163 (2 : ZMod 177427868193737095718644163)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (41, 1), (6138871, 1), (11369929738039441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (41, 1), (6138871, 1), (11369929738039441, 1)] : List FactorBlock).map factorBlockValue).prod) = 177427868193737095718644163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_31
      · exact prime_oneHundredOneCU_41
      · exact prime_oneHundredOneCU_6138871
      · exact prime_oneHundredOneCU_11369929738039441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 177427868193737095718644163) ^ 88713934096868547859322081 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 177427868193737095718644163) ^ 5723479619152809539311102 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 177427868193737095718644163) ^ 4327508980335051115088882 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 177427868193737095718644163) ^ 28902361394096259022 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 177427868193737095718644163) ^ 15605010082 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_290532737942542738244884481 : Nat.Prime 290532737942542738244884481 := by
  apply lucas_primality 290532737942542738244884481 (3 : ZMod 290532737942542738244884481)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 11), (5, 1), (11, 1), (19, 1), (13681, 1), (470489, 1), (21090239767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 11), (5, 1), (11, 1), (19, 1), (13681, 1), (470489, 1), (21090239767, 1)] : List FactorBlock).map factorBlockValue).prod) = 290532737942542738244884481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_11
      · exact prime_oneHundredOneCU_19
      · exact prime_oneHundredOneCU_13681
      · exact prime_oneHundredOneCU_470489
      · exact prime_oneHundredOneCU_21090239767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 290532737942542738244884481) ^ 145266368971271369122442240 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 290532737942542738244884481) ^ 58106547588508547648976896 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 290532737942542738244884481) ^ 26412067085685703476807680 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 290532737942542738244884481) ^ 15291196733818038854993920 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 290532737942542738244884481) ^ 21236220886086012590080 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 290532737942542738244884481) ^ 617512286031220152320 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 290532737942542738244884481) ^ 13775696300861440 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_398029850981283551395491739 : Nat.Prime 398029850981283551395491739 := by
  apply lucas_primality 398029850981283551395491739 (2 : ZMod 398029850981283551395491739)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (3758093, 1), (5884039990218495737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (3758093, 1), (5884039990218495737, 1)] : List FactorBlock).map factorBlockValue).prod) = 398029850981283551395491739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_3758093
      · exact prime_oneHundredOneCU_5884039990218495737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 398029850981283551395491739) ^ 199014925490641775697745869 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 398029850981283551395491739) ^ 132676616993761183798497246 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 398029850981283551395491739) ^ 105912719823932923266 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 398029850981283551395491739) ^ 67645674 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_402050354526549041813628019 : Nat.Prime 402050354526549041813628019 := by
  apply lucas_primality 402050354526549041813628019 (2 : ZMod 402050354526549041813628019)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (17, 1), (367, 1), (503, 1), (57727, 1), (33625949378447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (17, 1), (367, 1), (503, 1), (57727, 1), (33625949378447, 1)] : List FactorBlock).map factorBlockValue).prod) = 402050354526549041813628019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_11
      · exact prime_oneHundredOneCU_17
      · exact prime_oneHundredOneCU_367
      · exact prime_oneHundredOneCU_503
      · exact prime_oneHundredOneCU_57727
      · exact prime_oneHundredOneCU_33625949378447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 402050354526549041813628019) ^ 201025177263274520906814009 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 402050354526549041813628019) ^ 134016784842183013937876006 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 402050354526549041813628019) ^ 36550032229686276528511638 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 402050354526549041813628019) ^ 23650020854502884812566354 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 402050354526549041813628019) ^ 1095505053205855699764654 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 402050354526549041813628019) ^ 799304879774451375375006 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 402050354526549041813628019) ^ 6964684714718399393934 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 402050354526549041813628019) ^ 11956550282094 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_612353616894282386762294983 : Nat.Prime 612353616894282386762294983 := by
  apply lucas_primality 612353616894282386762294983 (31 : ZMod 612353616894282386762294983)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (715303, 1), (142679306740006772599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (715303, 1), (142679306740006772599, 1)] : List FactorBlock).map factorBlockValue).prod) = 612353616894282386762294983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_715303
      · exact prime_oneHundredOneCU_142679306740006772599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (31 : ZMod 612353616894282386762294983) ^ 306176808447141193381147491 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (31 : ZMod 612353616894282386762294983) ^ 204117872298094128920764994 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (31 : ZMod 612353616894282386762294983) ^ 856075840440040635594 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (31 : ZMod 612353616894282386762294983) ^ 4291818 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_706561865647248907802648057 : Nat.Prime 706561865647248907802648057 := by
  apply lucas_primality 706561865647248907802648057 (3 : ZMod 706561865647248907802648057)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (379, 1), (6669683, 1), (34939429071901951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (379, 1), (6669683, 1), (34939429071901951, 1)] : List FactorBlock).map factorBlockValue).prod) = 706561865647248907802648057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_379
      · exact prime_oneHundredOneCU_6669683
      · exact prime_oneHundredOneCU_34939429071901951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 706561865647248907802648057) ^ 353280932823624453901324028 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 706561865647248907802648057) ^ 1864279328884561762012264 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 706561865647248907802648057) ^ 105936348946006715432 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (3 : ZMod 706561865647248907802648057) ^ 20222478856 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_1658457712422014797481215579 : Nat.Prime 1658457712422014797481215579 := by
  apply lucas_primality 1658457712422014797481215579 (2 : ZMod 1658457712422014797481215579)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (971, 1), (98369, 1), (4266391, 1), (678289370107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (971, 1), (98369, 1), (4266391, 1), (678289370107, 1)] : List FactorBlock).map factorBlockValue).prod) = 1658457712422014797481215579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_971
      · exact prime_oneHundredOneCU_98369
      · exact prime_oneHundredOneCU_4266391
      · exact prime_oneHundredOneCU_678289370107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1658457712422014797481215579) ^ 829228856211007398740607789 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1658457712422014797481215579) ^ 552819237474004932493738526 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1658457712422014797481215579) ^ 1707989405172002881031118 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1658457712422014797481215579) ^ 16859556490581532774362 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1658457712422014797481215579) ^ 388726141701971243958 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1658457712422014797481215579) ^ 2445059270441454 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_1705842218491215220266393167 : Nat.Prime 1705842218491215220266393167 := by
  apply lucas_primality 1705842218491215220266393167 (5 : ZMod 1705842218491215220266393167)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (29, 1), (67, 1), (8669, 1), (147139, 1), (26472557913107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (29, 1), (67, 1), (8669, 1), (147139, 1), (26472557913107, 1)] : List FactorBlock).map factorBlockValue).prod) = 1705842218491215220266393167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_13
      · exact prime_oneHundredOneCU_29
      · exact prime_oneHundredOneCU_67
      · exact prime_oneHundredOneCU_8669
      · exact prime_oneHundredOneCU_147139
      · exact prime_oneHundredOneCU_26472557913107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1705842218491215220266393167) ^ 852921109245607610133196583 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1705842218491215220266393167) ^ 131218632191631940020491782 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1705842218491215220266393167) ^ 58822145465214317940220454 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1705842218491215220266393167) ^ 25460331619271868959199898 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1705842218491215220266393167) ^ 196774970410798848802214 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1705842218491215220266393167) ^ 11593406360592468483994 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1705842218491215220266393167) ^ 64438133409338 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem prime_oneHundredOneCU_119408955294385065418647521701 : Nat.Prime 119408955294385065418647521701 := by
  apply lucas_primality 119408955294385065418647521701 (2 : ZMod 119408955294385065418647521701)
  · rw [← oneHundredOneCUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (398029850981283551395491739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (398029850981283551395491739, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredOneCU_2
      · exact prime_oneHundredOneCU_3
      · exact prime_oneHundredOneCU_5
      · exact prime_oneHundredOneCU_398029850981283551395491739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 119408955294385065418647521701) ^ 59704477647192532709323760850 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 119408955294385065418647521701) ^ 39802985098128355139549173900 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 119408955294385065418647521701) ^ 23881791058877013083729504340 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide
    · change (2 : ZMod 119408955294385065418647521701) ^ 300 ≠ 1
      rw [← oneHundredOneCUFastPow_eq_pow]
      decide

private theorem phi_oneHundredOneCU_119408955294385065418647521600 : Nat.totient 119408955294385065418647521600 = 46341165778325674593232896000 := by
  rw [← show ((([(2, 6), (5, 2), (41, 1), (181, 1), (93741461347, 1), (107280988123, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521600 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_5, prime_oneHundredOneCU_41, prime_oneHundredOneCU_181, prime_oneHundredOneCU_93741461347, prime_oneHundredOneCU_107280988123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521601 : Nat.totient 119408955294385065418647521601 = 74824895516928760494946437120 := by
  rw [← show ((([(3, 1), (17, 1), (1481, 1), (1567, 1), (1008887329098073834813, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521601 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_3, prime_oneHundredOneCU_17, prime_oneHundredOneCU_1481, prime_oneHundredOneCU_1567, prime_oneHundredOneCU_1008887329098073834813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521602 : Nat.totient 119408955294385065418647521602 = 59704475766523057007236272240 := by
  rw [← show ((([(2, 1), (32203397, 1), (2243137423, 1), (826512328771, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521602 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_32203397, prime_oneHundredOneCU_2243137423, prime_oneHundredOneCU_826512328771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521603 : Nat.totient 119408955294385065418647521603 = 106989796807429783046603569920 := by
  rw [← show ((([(19, 1), (23, 1), (89, 1), (469099, 1), (17608711, 1), (371683585739, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521603 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_19, prime_oneHundredOneCU_23, prime_oneHundredOneCU_89, prime_oneHundredOneCU_469099, prime_oneHundredOneCU_17608711, prime_oneHundredOneCU_371683585739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521604 : Nat.totient 119408955294385065418647521604 = 39241864186392641410285281792 := by
  rw [← show ((([(2, 2), (3, 1), (73, 1), (2473, 1), (55119932390541623699723, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521604 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_3, prime_oneHundredOneCU_73, prime_oneHundredOneCU_2473, prime_oneHundredOneCU_55119932390541623699723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521605 : Nat.totient 119408955294385065418647521605 = 92932177364692510508923321920 := by
  rw [← show ((([(5, 1), (59, 1), (107, 1), (947, 1), (3994672005467173983811, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521605 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_5, prime_oneHundredOneCU_59, prime_oneHundredOneCU_107, prime_oneHundredOneCU_947, prime_oneHundredOneCU_3994672005467173983811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521606 : Nat.totient 119408955294385065418647521606 = 51175259027145984426001074720 := by
  rw [← show ((([(2, 1), (7, 1), (6856781, 1), (798315283, 1), (1558167497123, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521606 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_7, prime_oneHundredOneCU_6856781, prime_oneHundredOneCU_798315283, prime_oneHundredOneCU_1558167497123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521607 : Nat.totient 119408955294385065418647521607 = 73206732723657027866611257600 := by
  rw [← show ((([(3, 2), (13, 1), (269, 1), (28909, 1), (131239838674706934451, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521607 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_3, prime_oneHundredOneCU_13, prime_oneHundredOneCU_269, prime_oneHundredOneCU_28909, prime_oneHundredOneCU_131239838674706934451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521608 : Nat.totient 119408955294385065418647521608 = 59704165025634093581335164160 := by
  rw [← show ((([(2, 3), (229127, 1), (1147103, 1), (56789523843429521, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521608 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_229127, prime_oneHundredOneCU_1147103, prime_oneHundredOneCU_56789523843429521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521609 : Nat.totient 119408955294385065418647521609 = 119345474207880868005902131200 := by
  rw [← show ((([(2161, 1), (23321, 1), (63697, 1), (96779, 1), (384357052403, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521609 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2161, prime_oneHundredOneCU_23321, prime_oneHundredOneCU_63697, prime_oneHundredOneCU_96779, prime_oneHundredOneCU_384357052403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521610 : Nat.totient 119408955294385065418647521610 = 28946570904280892122586261760 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (11, 1), (37643, 1), (104803, 1), (3074879, 1), (29828882687, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521610 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_3, prime_oneHundredOneCU_5, prime_oneHundredOneCU_11, prime_oneHundredOneCU_37643, prime_oneHundredOneCU_104803, prime_oneHundredOneCU_3074879, prime_oneHundredOneCU_29828882687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521611 : Nat.totient 119408955294385065418647521611 = 115733562759510330569301480960 := by
  rw [← show ((([(47, 1), (103, 1), (1387849, 1), (2361721, 1), (7525424586899, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521611 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_47, prime_oneHundredOneCU_103, prime_oneHundredOneCU_1387849, prime_oneHundredOneCU_2361721, prime_oneHundredOneCU_7525424586899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521612 : Nat.totient 119408955294385065418647521612 = 59649853239464085744356399280 := by
  rw [← show ((([(2, 2), (1093, 1), (27312203864223482483679671, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521612 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_1093, prime_oneHundredOneCU_27312203864223482483679671]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521613 : Nat.totient 119408955294385065418647521613 = 68194020194518746041470687680 := by
  rw [← show ((([(3, 1), (7, 1), (1987, 1), (12799, 1), (223585532239109282381, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521613 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_3, prime_oneHundredOneCU_7, prime_oneHundredOneCU_1987, prime_oneHundredOneCU_12799, prime_oneHundredOneCU_223585532239109282381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521614 : Nat.totient 119408955294385065418647521614 = 59455063883438246763527961600 := by
  rw [← show ((([(2, 1), (241, 1), (35447, 1), (6988924923761760467041, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521614 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_241, prime_oneHundredOneCU_35447, prime_oneHundredOneCU_6988924923761760467041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521615 : Nat.totient 119408955294385065418647521615 = 92445642808556179678952916240 := by
  rw [← show ((([(5, 1), (31, 2), (24850979249611876257783043, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521615 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_5, prime_oneHundredOneCU_31, prime_oneHundredOneCU_24850979249611876257783043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521616 : Nat.totient 119408955294385065418647521616 = 39761579819979300140537241600 := by
  rw [← show ((([(2, 4), (3, 3), (971, 1), (98369, 1), (4266391, 1), (678289370107, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521616 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_3, prime_oneHundredOneCU_971, prime_oneHundredOneCU_98369, prime_oneHundredOneCU_4266391, prime_oneHundredOneCU_678289370107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521617 : Nat.totient 119408955294385065418647521617 = 119408954943250537968796614000 := by
  rw [← show ((([(340066117, 1), (351134527449510841501, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521617 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_340066117, prime_oneHundredOneCU_351134527449510841501]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521618 : Nat.totient 119408955294385065418647521618 = 56192449549294381729773090816 := by
  rw [← show ((([(2, 1), (17, 1), (55942292969, 1), (62779480612992433, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521618 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_17, prime_oneHundredOneCU_55942292969, prime_oneHundredOneCU_62779480612992433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521619 : Nat.totient 119408955294385065418647521619 = 79603592408085132373238515016 := by
  rw [← show ((([(3, 1), (33479, 1), (1188894085788952929882887, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521619 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_3, prime_oneHundredOneCU_33479, prime_oneHundredOneCU_1188894085788952929882887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521620 : Nat.totient 119408955294385065418647521620 = 35938844410112841660684705792 := by
  rw [← show ((([(2, 2), (5, 1), (7, 1), (13, 1), (29, 1), (67, 1), (8669, 1), (147139, 1), (26472557913107, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521620 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_5, prime_oneHundredOneCU_7, prime_oneHundredOneCU_13, prime_oneHundredOneCU_29, prime_oneHundredOneCU_67, prime_oneHundredOneCU_8669, prime_oneHundredOneCU_147139, prime_oneHundredOneCU_26472557913107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521621 : Nat.totient 119408955294385065418647521621 = 108551928718748008051433706240 := by
  rw [← show ((([(11, 1), (65119, 1), (166700342023323824520769, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521621 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_11, prime_oneHundredOneCU_65119, prime_oneHundredOneCU_166700342023323824520769]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521622 : Nat.totient 119408955294385065418647521622 = 37458368600117566824161460000 := by
  rw [← show ((([(2, 1), (3, 1), (19, 1), (151, 1), (427802951, 1), (16214789837114723, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521622 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_3, prime_oneHundredOneCU_19, prime_oneHundredOneCU_151, prime_oneHundredOneCU_427802951, prime_oneHundredOneCU_16214789837114723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521623 : Nat.totient 119408955294385065418647521623 = 118695068992279243229702939904 := by
  rw [← show ((([(317, 1), (353, 1), (1067094621981796993937923, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521623 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_317, prime_oneHundredOneCU_353, prime_oneHundredOneCU_1067094621981796993937923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521624 : Nat.totient 119408955294385065418647521624 = 59113344205141121494379960800 := by
  rw [← show ((([(2, 3), (101, 1), (147783360512852803735949903, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521624 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_101, prime_oneHundredOneCU_147783360512852803735949903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521625 : Nat.totient 119408955294385065418647521625 = 63458139942687647161723488000 := by
  rw [← show ((([(3, 2), (5, 3), (281, 1), (362835530639, 1), (1041041991683, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521625 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_3, prime_oneHundredOneCU_5, prime_oneHundredOneCU_281, prime_oneHundredOneCU_362835530639, prime_oneHundredOneCU_1041041991683]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521626 : Nat.totient 119408955294385065418647521626 = 57105796476658088213299291200 := by
  rw [← show ((([(2, 1), (23, 1), (20149, 1), (163121016269, 1), (789797312651, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521626 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_23, prime_oneHundredOneCU_20149, prime_oneHundredOneCU_163121016269, prime_oneHundredOneCU_789797312651]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521627 : Nat.totient 119408955294385065418647521627 = 102214178175477358646059622400 := by
  rw [← show ((([(7, 1), (911, 1), (4259, 1), (1396270049, 1), (3148787984161, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521627 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_7, prime_oneHundredOneCU_911, prime_oneHundredOneCU_4259, prime_oneHundredOneCU_1396270049, prime_oneHundredOneCU_3148787984161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521628 : Nat.totient 119408955294385065418647521628 = 38721427472331041396530176000 := by
  rw [← show ((([(2, 2), (3, 1), (37, 1), (9151, 1), (51827, 1), (93281, 1), (95287, 1), (63797323, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521628 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_3, prime_oneHundredOneCU_37, prime_oneHundredOneCU_9151, prime_oneHundredOneCU_51827, prime_oneHundredOneCU_93281, prime_oneHundredOneCU_95287, prime_oneHundredOneCU_63797323]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521629 : Nat.totient 119408955294385065418647521629 = 119404891496372318636797198656 := by
  rw [← show ((([(43789, 1), (89317, 1), (30530769037577686333, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521629 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_43789, prime_oneHundredOneCU_89317, prime_oneHundredOneCU_30530769037577686333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521630 : Nat.totient 119408955294385065418647521630 = 47754250857214932867760933632 := by
  rw [← show ((([(2, 1), (5, 1), (5119, 1), (77837173, 1), (29968479920162249, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521630 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_5, prime_oneHundredOneCU_5119, prime_oneHundredOneCU_77837173, prime_oneHundredOneCU_29968479920162249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521631 : Nat.totient 119408955294385065418647521631 = 78179327709054239167239168000 := by
  rw [← show ((([(3, 1), (97, 1), (131, 1), (17191, 1), (182209691898088108321, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521631 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_3, prime_oneHundredOneCU_97, prime_oneHundredOneCU_131, prime_oneHundredOneCU_17191, prime_oneHundredOneCU_182209691898088108321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521632 : Nat.totient 119408955294385065418647521632 = 53778845587129220455437565440 := by
  rw [← show ((([(2, 5), (11, 1), (109, 1), (3112201712218126183763749, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521632 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_11, prime_oneHundredOneCU_109, prime_oneHundredOneCU_3112201712218126183763749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521633 : Nat.totient 119408955294385065418647521633 = 110223651040970829617213096736 := by
  rw [← show ((([(13, 2), (706561865647248907802648057, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521633 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_13, prime_oneHundredOneCU_706561865647248907802648057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521634 : Nat.totient 119408955294385065418647521634 = 33323426233780406790642309216 := by
  rw [← show ((([(2, 1), (3, 2), (7, 1), (43, 1), (10576519, 1), (2083795731702019627, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521634 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_3, prime_oneHundredOneCU_7, prime_oneHundredOneCU_43, prime_oneHundredOneCU_10576519, prime_oneHundredOneCU_2083795731702019627]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521635 : Nat.totient 119408955294385065418647521635 = 89907707657244310925967415296 := by
  rw [← show ((([(5, 1), (17, 1), (424849, 1), (3306613028999647775719, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521635 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_5, prime_oneHundredOneCU_17, prime_oneHundredOneCU_424849, prime_oneHundredOneCU_3306613028999647775719]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521636 : Nat.totient 119408955294385065418647521636 = 59704477647039068266397495808 := by
  rw [← show ((([(2, 2), (389046343393, 1), (76731832416789113, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521636 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_389046343393, prime_oneHundredOneCU_76731832416789113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521637 : Nat.totient 119408955294385065418647521637 = 78300151887761177520881138880 := by
  rw [← show ((([(3, 1), (61, 1), (97583, 1), (6686696990544804841133, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521637 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_3, prime_oneHundredOneCU_61, prime_oneHundredOneCU_97583, prime_oneHundredOneCU_6686696990544804841133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521638 : Nat.totient 119408955294385065418647521638 = 59503723758784227955737374208 := by
  rw [← show ((([(2, 1), (587, 1), (659, 1), (6997, 1), (639697, 1), (34482377283527, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521638 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_587, prime_oneHundredOneCU_659, prime_oneHundredOneCU_6997, prime_oneHundredOneCU_639697, prime_oneHundredOneCU_34482377283527]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521639 : Nat.totient 119408955294385065418647521639 = 119408955294147551375137558224 := by
  rw [← show ((([(502745885183, 1), (237513540764078233, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521639 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_502745885183, prime_oneHundredOneCU_237513540764078233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521640 : Nat.totient 119408955294385065418647521640 = 31830041265362985916396598528 := by
  rw [← show ((([(2, 3), (3, 1), (5, 1), (2579, 1), (1908690587, 1), (202147688107139, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521640 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_3, prime_oneHundredOneCU_5, prime_oneHundredOneCU_2579, prime_oneHundredOneCU_1908690587, prime_oneHundredOneCU_202147688107139]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521641 : Nat.totient 119408955294385065418647521641 = 94598695556894091804246702720 := by
  rw [← show ((([(7, 1), (19, 1), (41, 1), (21897846193725484213945997, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521641 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_7, prime_oneHundredOneCU_19, prime_oneHundredOneCU_41, prime_oneHundredOneCU_21897846193725484213945997]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521642 : Nat.totient 119408955294385065418647521642 = 59575526291583045597640555692 := by
  rw [← show ((([(2, 1), (463, 1), (128951355609487111683204667, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521642 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_463, prime_oneHundredOneCU_128951355609487111683204667]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521643 : Nat.totient 119408955294385065418647521643 = 72369063814778827526453043240 := by
  rw [← show ((([(3, 3), (11, 1), (402050354526549041813628019, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521643 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_3, prime_oneHundredOneCU_11, prime_oneHundredOneCU_402050354526549041813628019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521644 : Nat.totient 119408955294385065418647521644 = 59704432929359524754468578560 := by
  rw [← show ((([(2, 2), (1335319, 1), (9892441421, 1), (2259895678289, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521644 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_1335319, prime_oneHundredOneCU_9892441421, prime_oneHundredOneCU_2259895678289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521645 : Nat.totient 119408955294385065418647521645 = 93696725435427864393769565440 := by
  rw [← show ((([(5, 1), (53, 1), (3347, 1), (2542229, 1), (52956667040469611, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521645 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_5, prime_oneHundredOneCU_53, prime_oneHundredOneCU_3347, prime_oneHundredOneCU_2542229, prime_oneHundredOneCU_52956667040469611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521646 : Nat.totient 119408955294385065418647521646 = 35556016464716677528161427200 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (31, 1), (316349930761, 1), (156103578345527, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521646 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_3, prime_oneHundredOneCU_13, prime_oneHundredOneCU_31, prime_oneHundredOneCU_316349930761, prime_oneHundredOneCU_156103578345527]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521647 : Nat.totient 119408955294385065418647521647 = 119408903141467365903899415376 := by
  rw [← show ((([(2289593, 1), (52152917699514745816679, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521647 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2289593, prime_oneHundredOneCU_52152917699514745816679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521648 : Nat.totient 119408955294385065418647521648 = 51170479566201033177108412800 := by
  rw [← show ((([(2, 4), (7, 2), (10691, 1), (225326671, 1), (63225155487427, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521648 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_7, prime_oneHundredOneCU_10691, prime_oneHundredOneCU_225326671, prime_oneHundredOneCU_63225155487427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521649 : Nat.totient 119408955294385065418647521649 = 73510168221820089566043697152 := by
  rw [← show ((([(3, 1), (23, 1), (29, 1), (10177, 1), (41659, 1), (140754145579009043, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521649 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_3, prime_oneHundredOneCU_23, prime_oneHundredOneCU_29, prime_oneHundredOneCU_10177, prime_oneHundredOneCU_41659, prime_oneHundredOneCU_140754145579009043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521650 : Nat.totient 119408955294385065418647521650 = 47158979812233938936485473600 := by
  rw [← show ((([(2, 1), (5, 2), (79, 1), (203495898157, 1), (148553929284011, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521650 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_5, prime_oneHundredOneCU_79, prime_oneHundredOneCU_203495898157, prime_oneHundredOneCU_148553929284011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521651 : Nat.totient 119408955294385065418647521651 = 119408951349730790515479559680 := by
  rw [← show ((([(30879557, 1), (1537170241, 1), (2515613225623, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521651 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_30879557, prime_oneHundredOneCU_1537170241, prime_oneHundredOneCU_2515613225623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521652 : Nat.totient 119408955294385065418647521652 = 37461262870266327113814376704 := by
  rw [← show ((([(2, 2), (3, 2), (17, 1), (101203, 1), (1927933678345985788007, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521652 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_3, prime_oneHundredOneCU_17, prime_oneHundredOneCU_101203, prime_oneHundredOneCU_1927933678345985788007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521653 : Nat.totient 119408955294385065418647521653 = 118887518807117023660051320768 := by
  rw [← show ((([(229, 1), (93882864989, 1), (5554117740897413, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521653 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_229, prime_oneHundredOneCU_93882864989, prime_oneHundredOneCU_5554117740897413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521654 : Nat.totient 119408955294385065418647521654 = 54271157480660830232030999200 := by
  rw [← show ((([(2, 1), (11, 1), (9623, 1), (895874579, 1), (629588111600621, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521654 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_11, prime_oneHundredOneCU_9623, prime_oneHundredOneCU_895874579, prime_oneHundredOneCU_629588111600621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521655 : Nat.totient 119408955294385065418647521655 = 54586950807328721810927943552 := by
  rw [← show ((([(3, 1), (5, 1), (7, 1), (296040469, 1), (3841461775487222819, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521655 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_3, prime_oneHundredOneCU_5, prime_oneHundredOneCU_7, prime_oneHundredOneCU_296040469, prime_oneHundredOneCU_3841461775487222819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521656 : Nat.totient 119408955294385065418647521656 = 59704230842615796817017270016 := by
  rw [← show ((([(2, 3), (246809, 1), (12187067, 1), (4962342325378469, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521656 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_246809, prime_oneHundredOneCU_12187067, prime_oneHundredOneCU_4962342325378469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521657 : Nat.totient 119408955294385065418647521657 = 119406067865248287756714250624 := by
  rw [← show ((([(41357, 1), (765444629, 1), (3772020903486569, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521657 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_41357, prime_oneHundredOneCU_765444629, prime_oneHundredOneCU_3772020903486569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521658 : Nat.totient 119408955294385065418647521658 = 38794784229393385306741056000 := by
  rw [← show ((([(2, 1), (3, 1), (47, 1), (251, 1), (6359, 1), (1652509, 1), (160539316822649, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521658 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_3, prime_oneHundredOneCU_47, prime_oneHundredOneCU_251, prime_oneHundredOneCU_6359, prime_oneHundredOneCU_1652509, prime_oneHundredOneCU_160539316822649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521659 : Nat.totient 119408955294385065418647521659 = 109928144570682014763907651200 := by
  rw [← show ((([(13, 1), (373, 1), (156276031, 1), (157576823615107861, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521659 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_13, prime_oneHundredOneCU_373, prime_oneHundredOneCU_156276031, prime_oneHundredOneCU_157576823615107861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521660 : Nat.totient 119408955294385065418647521660 = 45249709333017776283832584960 := by
  rw [← show ((([(2, 2), (5, 1), (19, 1), (1085214341, 1), (289559473191628877, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521660 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_5, prime_oneHundredOneCU_19, prime_oneHundredOneCU_1085214341, prime_oneHundredOneCU_289559473191628877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521661 : Nat.totient 119408955294385065418647521661 = 79605970196166815231170169280 := by
  rw [← show ((([(3, 2), (885595788761, 1), (14981622392240989, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521661 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_3, prime_oneHundredOneCU_885595788761, prime_oneHundredOneCU_14981622392240989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521662 : Nat.totient 119408955294385065418647521662 = 50654225223835488784178657280 := by
  rw [← show ((([(2, 1), (7, 1), (127, 1), (431, 1), (177647, 1), (408782999, 1), (2145740353, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521662 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_7, prime_oneHundredOneCU_127, prime_oneHundredOneCU_431, prime_oneHundredOneCU_177647, prime_oneHundredOneCU_408782999, prime_oneHundredOneCU_2145740353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521663 : Nat.totient 119408955294385065418647521663 = 119408955294384326557719354840 := by
  rw [← show ((([(238778588863421, 1), (500082339303403, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521663 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_238778588863421, prime_oneHundredOneCU_500082339303403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521664 : Nat.totient 119408955294385065418647521664 = 38846859251971632061570928640 := by
  rw [← show ((([(2, 7), (3, 1), (59, 1), (139, 1), (37917427274616238815721, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521664 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_3, prime_oneHundredOneCU_59, prime_oneHundredOneCU_139, prime_oneHundredOneCU_37917427274616238815721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521665 : Nat.totient 119408955294385065418647521665 = 84495620825424523698341529600 := by
  rw [← show ((([(5, 1), (11, 1), (37, 1), (559649, 1), (104847179766746890331, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521665 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_5, prime_oneHundredOneCU_11, prime_oneHundredOneCU_37, prime_oneHundredOneCU_559649, prime_oneHundredOneCU_104847179766746890331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521666 : Nat.totient 119408955294385065418647521666 = 59704477530716664118064023380 := by
  rw [← show ((([(2, 1), (512590963, 1), (116475868590747146491, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521666 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_512590963, prime_oneHundredOneCU_116475868590747146491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521667 : Nat.totient 119408955294385065418647521667 = 79605693607047062845832842848 := by
  rw [← show ((([(3, 1), (287813, 1), (138294604823716632464653, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521667 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_3, prime_oneHundredOneCU_287813, prime_oneHundredOneCU_138294604823716632464653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521668 : Nat.totient 119408955294385065418647521668 = 59704474617987163209078796800 := by
  rw [← show ((([(2, 2), (19709617, 1), (1514602684750102772401, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521668 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_19709617, prime_oneHundredOneCU_1514602684750102772401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521669 : Nat.totient 119408955294385065418647521669 = 94826364132162901070354430720 := by
  rw [← show ((([(7, 1), (17, 2), (71, 1), (647, 1), (1284926797586566181219, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521669 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_7, prime_oneHundredOneCU_17, prime_oneHundredOneCU_71, prime_oneHundredOneCU_647, prime_oneHundredOneCU_1284926797586566181219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521670 : Nat.totient 119408955294385065418647521670 = 31560426986323755771974338560 := by
  rw [← show ((([(2, 1), (3, 4), (5, 1), (113, 1), (185599, 1), (7029068966051003161, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521670 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_3, prime_oneHundredOneCU_5, prime_oneHundredOneCU_113, prime_oneHundredOneCU_185599, prime_oneHundredOneCU_7029068966051003161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521671 : Nat.totient 119408955294385065418647521671 = 118215042355838175340999558464 := by
  rw [← show ((([(167, 1), (313, 1), (1187, 1), (1924533038689948784323, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521671 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_167, prime_oneHundredOneCU_313, prime_oneHundredOneCU_1187, prime_oneHundredOneCU_1924533038689948784323]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521672 : Nat.totient 119408955294385065418647521672 = 52702665393305559533907253248 := by
  rw [← show ((([(2, 3), (13, 1), (23, 1), (4057, 1), (1136060269, 1), (10831019656727, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521672 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_13, prime_oneHundredOneCU_23, prime_oneHundredOneCU_4057, prime_oneHundredOneCU_1136060269, prime_oneHundredOneCU_10831019656727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521673 : Nat.totient 119408955294385065418647521673 = 79299083519025438027481041600 := by
  rw [← show ((([(3, 1), (271, 1), (6037, 1), (3619491523, 1), (6721676600371, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521673 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_3, prime_oneHundredOneCU_271, prime_oneHundredOneCU_6037, prime_oneHundredOneCU_3619491523, prime_oneHundredOneCU_6721676600371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521674 : Nat.totient 119408955294385065418647521674 = 59704477645682254974961632960 := by
  rw [← show ((([(2, 1), (39532119061, 1), (1510277694830008817, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521674 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_39532119061, prime_oneHundredOneCU_1510277694830008817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521675 : Nat.totient 119408955294385065418647521675 = 95523478631733388649885865120 := by
  rw [← show ((([(5, 2), (25919, 1), (184280188733184251581693, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521675 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_5, prime_oneHundredOneCU_25919, prime_oneHundredOneCU_184280188733184251581693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521676 : Nat.totient 119408955294385065418647521676 = 30988637601735242354429952000 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (11, 1), (1217, 1), (26041, 1), (84828571, 1), (48070046327, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521676 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_3, prime_oneHundredOneCU_7, prime_oneHundredOneCU_11, prime_oneHundredOneCU_1217, prime_oneHundredOneCU_26041, prime_oneHundredOneCU_84828571, prime_oneHundredOneCU_48070046327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521677 : Nat.totient 119408955294385065418647521677 = 111322733426645602682334245760 := by
  rw [← show ((([(31, 1), (43, 1), (73, 1), (141499, 1), (8672224630524127747, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521677 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_31, prime_oneHundredOneCU_43, prime_oneHundredOneCU_73, prime_oneHundredOneCU_141499, prime_oneHundredOneCU_8672224630524127747]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521678 : Nat.totient 119408955294385065418647521678 = 57645702555901063430460473952 := by
  rw [← show ((([(2, 1), (29, 1), (6562275747949, 1), (313728829808159, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521678 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_29, prime_oneHundredOneCU_6562275747949, prime_oneHundredOneCU_313728829808159]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521679 : Nat.totient 119408955294385065418647521679 = 75414478856088108107434298112 := by
  rw [← show ((([(3, 2), (19, 1), (44273, 1), (15772547244995605471613, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521679 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_3, prime_oneHundredOneCU_19, prime_oneHundredOneCU_44273, prime_oneHundredOneCU_15772547244995605471613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521680 : Nat.totient 119408955294385065418647521680 = 46813036894420372346803630080 := by
  rw [← show ((([(2, 4), (5, 1), (83, 1), (179, 1), (421, 1), (238634753642654320793, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521680 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_5, prime_oneHundredOneCU_83, prime_oneHundredOneCU_179, prime_oneHundredOneCU_421, prime_oneHundredOneCU_238634753642654320793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521681 : Nat.totient 119408955294385065418647521681 = 119370853712717602618291200000 := by
  rw [← show ((([(3361, 1), (46381, 1), (6732583601, 1), (113774915941, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521681 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_3361, prime_oneHundredOneCU_46381, prime_oneHundredOneCU_6732583601, prime_oneHundredOneCU_113774915941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521682 : Nat.totient 119408955294385065418647521682 = 38832095892737534360644416000 := by
  rw [← show ((([(2, 1), (3, 1), (41, 1), (458531, 1), (22085454877, 1), (47932131341, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521682 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_3, prime_oneHundredOneCU_41, prime_oneHundredOneCU_458531, prime_oneHundredOneCU_22085454877, prime_oneHundredOneCU_47932131341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521683 : Nat.totient 119408955294385065418647521683 = 102350533095030994146088956864 := by
  rw [← show ((([(7, 1), (7087045213, 1), (2406986504562060313, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521683 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_7, prime_oneHundredOneCU_7087045213, prime_oneHundredOneCU_2406986504562060313]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521684 : Nat.totient 119408955294385065418647521684 = 59704476525971557038196971288 := by
  rw [← show ((([(2, 2), (53249519, 1), (560610487835510145259, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521684 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_53249519, prime_oneHundredOneCU_560610487835510145259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521685 : Nat.totient 119408955294385065418647521685 = 58785947221851109129180318272 := by
  rw [← show ((([(3, 1), (5, 1), (13, 1), (612353616894282386762294983, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521685 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_3, prime_oneHundredOneCU_5, prime_oneHundredOneCU_13, prime_oneHundredOneCU_612353616894282386762294983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521686 : Nat.totient 119408955294385065418647521686 = 56192449550247341587720342144 := by
  rw [← show ((([(2, 1), (17, 1), (1091215800893, 1), (3218454217781303, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521686 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_17, prime_oneHundredOneCU_1091215800893, prime_oneHundredOneCU_3218454217781303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521687 : Nat.totient 119408955294385065418647521687 = 106457402401465287526917235200 := by
  rw [← show ((([(11, 1), (67, 1), (227, 1), (21647, 1), (1523434819, 1), (21643224241, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521687 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_11, prime_oneHundredOneCU_67, prime_oneHundredOneCU_227, prime_oneHundredOneCU_21647, prime_oneHundredOneCU_1523434819, prime_oneHundredOneCU_21643224241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521688 : Nat.totient 119408955294385065418647521688 = 39802985098128355139549173872 := by
  rw [← show ((([(2, 3), (3, 2), (1658457712422014797481215579, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521688 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_3, prime_oneHundredOneCU_1658457712422014797481215579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521689 : Nat.totient 119408955294385065418647521689 = 118675570169586256055557623360 := by
  rw [← show ((([(163, 1), (145757, 1), (185485739, 1), (27096259861261, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521689 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_163, prime_oneHundredOneCU_145757, prime_oneHundredOneCU_185485739, prime_oneHundredOneCU_27096259861261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521690 : Nat.totient 119408955294385065418647521690 = 40940213243789165286393435984 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (1705842218491215220266393167, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521690 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_5, prime_oneHundredOneCU_7, prime_oneHundredOneCU_1705842218491215220266393167]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521691 : Nat.totient 119408955294385065418647521691 = 79024904720371624802608578560 := by
  rw [← show ((([(3, 1), (137, 1), (290532737942542738244884481, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521691 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_3, prime_oneHundredOneCU_137, prime_oneHundredOneCU_290532737942542738244884481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521692 : Nat.totient 119408955294385065418647521692 = 59032092190844240785816012800 := by
  rw [← show ((([(2, 2), (89, 1), (40841, 1), (572137, 1), (14354580297007471, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521692 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_89, prime_oneHundredOneCU_40841, prime_oneHundredOneCU_572137, prime_oneHundredOneCU_14354580297007471]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521693 : Nat.totient 119408955294385065418647521693 = 119258339322995378382016014336 := by
  rw [← show ((([(827, 1), (20399, 1), (329533, 1), (6163169, 1), (3485134333, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521693 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_827, prime_oneHundredOneCU_20399, prime_oneHundredOneCU_329533, prime_oneHundredOneCU_6163169, prime_oneHundredOneCU_3485134333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521694 : Nat.totient 119408955294385065418647521694 = 39802985098125511150750855680 := by
  rw [← show ((([(2, 1), (3, 1), (14136004461829, 1), (1407858394697281, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521694 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_3, prime_oneHundredOneCU_14136004461829, prime_oneHundredOneCU_1407858394697281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521695 : Nat.totient 119408955294385065418647521695 = 90900369823899346258641426432 := by
  rw [← show ((([(5, 1), (23, 1), (193, 1), (4891201387, 1), (1099932931520623, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521695 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_5, prime_oneHundredOneCU_23, prime_oneHundredOneCU_193, prime_oneHundredOneCU_4891201387, prime_oneHundredOneCU_1099932931520623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521696 : Nat.totient 119408955294385065418647521696 = 59657940841366794183103243008 := by
  rw [← show ((([(2, 5), (1283, 1), (34105789, 1), (85277048976401819, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521696 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_1283, prime_oneHundredOneCU_34105789, prime_oneHundredOneCU_85277048976401819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521697 : Nat.totient 119408955294385065418647521697 = 68233688591768906931454203936 := by
  rw [← show ((([(3, 3), (7, 2), (461413487, 1), (195608070807371597, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521697 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_3, prime_oneHundredOneCU_7, prime_oneHundredOneCU_461413487, prime_oneHundredOneCU_195608070807371597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521698 : Nat.totient 119408955294385065418647521698 = 45805740165051212239374873600 := by
  rw [← show ((([(2, 1), (11, 1), (13, 1), (19, 1), (53, 1), (61, 1), (6796910637026829926309, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521698 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_11, prime_oneHundredOneCU_13, prime_oneHundredOneCU_19, prime_oneHundredOneCU_53, prime_oneHundredOneCU_61, prime_oneHundredOneCU_6796910637026829926309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521699 : Nat.totient 119408955294385065418647521699 = 119231527426191328322928876864 := by
  rw [← show ((([(673, 1), (177427868193737095718644163, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521699 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_673, prime_oneHundredOneCU_177427868193737095718644163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521700 : Nat.totient 119408955294385065418647521700 = 31842388078502684111639339040 := by
  rw [← show ((([(2, 2), (3, 1), (5, 2), (398029850981283551395491739, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521700 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_2, prime_oneHundredOneCU_3, prime_oneHundredOneCU_5, prime_oneHundredOneCU_398029850981283551395491739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredOneCU_119408955294385065418647521701 : Nat.totient 119408955294385065418647521701 = 119408955294385065418647521700 := by
  rw [← show ((([(119408955294385065418647521701, 1)] : List FactorBlock).map factorBlockValue).prod) = 119408955294385065418647521701 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredOneCU_119408955294385065418647521701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredOneCU : certifiedKill 1 119408955294385065418647521599 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredOneCU_119408955294385065418647521600, phi_oneHundredOneCU_119408955294385065418647521601, phi_oneHundredOneCU_119408955294385065418647521602,
    phi_oneHundredOneCU_119408955294385065418647521603, phi_oneHundredOneCU_119408955294385065418647521604, phi_oneHundredOneCU_119408955294385065418647521605,
    phi_oneHundredOneCU_119408955294385065418647521606, phi_oneHundredOneCU_119408955294385065418647521607, phi_oneHundredOneCU_119408955294385065418647521608,
    phi_oneHundredOneCU_119408955294385065418647521609, phi_oneHundredOneCU_119408955294385065418647521610, phi_oneHundredOneCU_119408955294385065418647521611,
    phi_oneHundredOneCU_119408955294385065418647521612, phi_oneHundredOneCU_119408955294385065418647521613, phi_oneHundredOneCU_119408955294385065418647521614,
    phi_oneHundredOneCU_119408955294385065418647521615, phi_oneHundredOneCU_119408955294385065418647521616, phi_oneHundredOneCU_119408955294385065418647521617,
    phi_oneHundredOneCU_119408955294385065418647521618, phi_oneHundredOneCU_119408955294385065418647521619, phi_oneHundredOneCU_119408955294385065418647521620,
    phi_oneHundredOneCU_119408955294385065418647521621, phi_oneHundredOneCU_119408955294385065418647521622, phi_oneHundredOneCU_119408955294385065418647521623,
    phi_oneHundredOneCU_119408955294385065418647521624, phi_oneHundredOneCU_119408955294385065418647521625, phi_oneHundredOneCU_119408955294385065418647521626,
    phi_oneHundredOneCU_119408955294385065418647521627, phi_oneHundredOneCU_119408955294385065418647521628, phi_oneHundredOneCU_119408955294385065418647521629,
    phi_oneHundredOneCU_119408955294385065418647521630, phi_oneHundredOneCU_119408955294385065418647521631, phi_oneHundredOneCU_119408955294385065418647521632,
    phi_oneHundredOneCU_119408955294385065418647521633, phi_oneHundredOneCU_119408955294385065418647521634, phi_oneHundredOneCU_119408955294385065418647521635,
    phi_oneHundredOneCU_119408955294385065418647521636, phi_oneHundredOneCU_119408955294385065418647521637, phi_oneHundredOneCU_119408955294385065418647521638,
    phi_oneHundredOneCU_119408955294385065418647521639, phi_oneHundredOneCU_119408955294385065418647521640, phi_oneHundredOneCU_119408955294385065418647521641,
    phi_oneHundredOneCU_119408955294385065418647521642, phi_oneHundredOneCU_119408955294385065418647521643, phi_oneHundredOneCU_119408955294385065418647521644,
    phi_oneHundredOneCU_119408955294385065418647521645, phi_oneHundredOneCU_119408955294385065418647521646, phi_oneHundredOneCU_119408955294385065418647521647,
    phi_oneHundredOneCU_119408955294385065418647521648, phi_oneHundredOneCU_119408955294385065418647521649, phi_oneHundredOneCU_119408955294385065418647521650,
    phi_oneHundredOneCU_119408955294385065418647521651, phi_oneHundredOneCU_119408955294385065418647521652, phi_oneHundredOneCU_119408955294385065418647521653,
    phi_oneHundredOneCU_119408955294385065418647521654, phi_oneHundredOneCU_119408955294385065418647521655, phi_oneHundredOneCU_119408955294385065418647521656,
    phi_oneHundredOneCU_119408955294385065418647521657, phi_oneHundredOneCU_119408955294385065418647521658, phi_oneHundredOneCU_119408955294385065418647521659,
    phi_oneHundredOneCU_119408955294385065418647521660, phi_oneHundredOneCU_119408955294385065418647521661, phi_oneHundredOneCU_119408955294385065418647521662,
    phi_oneHundredOneCU_119408955294385065418647521663, phi_oneHundredOneCU_119408955294385065418647521664, phi_oneHundredOneCU_119408955294385065418647521665,
    phi_oneHundredOneCU_119408955294385065418647521666, phi_oneHundredOneCU_119408955294385065418647521667, phi_oneHundredOneCU_119408955294385065418647521668,
    phi_oneHundredOneCU_119408955294385065418647521669, phi_oneHundredOneCU_119408955294385065418647521670, phi_oneHundredOneCU_119408955294385065418647521671,
    phi_oneHundredOneCU_119408955294385065418647521672, phi_oneHundredOneCU_119408955294385065418647521673, phi_oneHundredOneCU_119408955294385065418647521674,
    phi_oneHundredOneCU_119408955294385065418647521675, phi_oneHundredOneCU_119408955294385065418647521676, phi_oneHundredOneCU_119408955294385065418647521677,
    phi_oneHundredOneCU_119408955294385065418647521678, phi_oneHundredOneCU_119408955294385065418647521679, phi_oneHundredOneCU_119408955294385065418647521680,
    phi_oneHundredOneCU_119408955294385065418647521681, phi_oneHundredOneCU_119408955294385065418647521682, phi_oneHundredOneCU_119408955294385065418647521683,
    phi_oneHundredOneCU_119408955294385065418647521684, phi_oneHundredOneCU_119408955294385065418647521685, phi_oneHundredOneCU_119408955294385065418647521686,
    phi_oneHundredOneCU_119408955294385065418647521687, phi_oneHundredOneCU_119408955294385065418647521688, phi_oneHundredOneCU_119408955294385065418647521689,
    phi_oneHundredOneCU_119408955294385065418647521690, phi_oneHundredOneCU_119408955294385065418647521691, phi_oneHundredOneCU_119408955294385065418647521692,
    phi_oneHundredOneCU_119408955294385065418647521693, phi_oneHundredOneCU_119408955294385065418647521694, phi_oneHundredOneCU_119408955294385065418647521695,
    phi_oneHundredOneCU_119408955294385065418647521696, phi_oneHundredOneCU_119408955294385065418647521697, phi_oneHundredOneCU_119408955294385065418647521698,
    phi_oneHundredOneCU_119408955294385065418647521699, phi_oneHundredOneCU_119408955294385065418647521700, phi_oneHundredOneCU_119408955294385065418647521701]

end TotientTailPeriodKiller
end Erdos249257
