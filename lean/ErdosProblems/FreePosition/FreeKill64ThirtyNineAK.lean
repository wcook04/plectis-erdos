import Batteries.Tactic.OpenPrivate
import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def thirtyNineAKFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem thirtyNineAKFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    thirtyNineAKFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [thirtyNineAKFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [thirtyNineAKFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then thirtyNineAKFastPow a n * thirtyNineAKFastPow a n * a
        else thirtyNineAKFastPow a n * thirtyNineAKFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_thirtyNineAK_2 : Nat.Prime 2 := by norm_num
private theorem prime_thirtyNineAK_3 : Nat.Prime 3 := by norm_num
private theorem prime_thirtyNineAK_5 : Nat.Prime 5 := by norm_num
private theorem prime_thirtyNineAK_7 : Nat.Prime 7 := by norm_num
private theorem prime_thirtyNineAK_11 : Nat.Prime 11 := by norm_num
private theorem prime_thirtyNineAK_13 : Nat.Prime 13 := by norm_num
private theorem prime_thirtyNineAK_17 : Nat.Prime 17 := by norm_num
private theorem prime_thirtyNineAK_19 : Nat.Prime 19 := by norm_num
private theorem prime_thirtyNineAK_23 : Nat.Prime 23 := by norm_num
private theorem prime_thirtyNineAK_29 : Nat.Prime 29 := by norm_num
private theorem prime_thirtyNineAK_31 : Nat.Prime 31 := by norm_num
private theorem prime_thirtyNineAK_37 : Nat.Prime 37 := by norm_num
private theorem prime_thirtyNineAK_41 : Nat.Prime 41 := by norm_num
private theorem prime_thirtyNineAK_43 : Nat.Prime 43 := by norm_num
private theorem prime_thirtyNineAK_47 : Nat.Prime 47 := by norm_num
private theorem prime_thirtyNineAK_53 : Nat.Prime 53 := by norm_num
private theorem prime_thirtyNineAK_59 : Nat.Prime 59 := by norm_num
private theorem prime_thirtyNineAK_61 : Nat.Prime 61 := by norm_num
private theorem prime_thirtyNineAK_67 : Nat.Prime 67 := by norm_num
private theorem prime_thirtyNineAK_71 : Nat.Prime 71 := by norm_num
private theorem prime_thirtyNineAK_73 : Nat.Prime 73 := by norm_num
private theorem prime_thirtyNineAK_79 : Nat.Prime 79 := by norm_num
private theorem prime_thirtyNineAK_83 : Nat.Prime 83 := by norm_num
private theorem prime_thirtyNineAK_89 : Nat.Prime 89 := by norm_num
private theorem prime_thirtyNineAK_97 : Nat.Prime 97 := by norm_num
private theorem prime_thirtyNineAK_101 : Nat.Prime 101 := by norm_num
private theorem prime_thirtyNineAK_103 : Nat.Prime 103 := by norm_num
private theorem prime_thirtyNineAK_107 : Nat.Prime 107 := by norm_num
private theorem prime_thirtyNineAK_109 : Nat.Prime 109 := by norm_num
private theorem prime_thirtyNineAK_113 : Nat.Prime 113 := by norm_num
private theorem prime_thirtyNineAK_127 : Nat.Prime 127 := by norm_num
private theorem prime_thirtyNineAK_131 : Nat.Prime 131 := by norm_num
private theorem prime_thirtyNineAK_137 : Nat.Prime 137 := by norm_num
private theorem prime_thirtyNineAK_139 : Nat.Prime 139 := by norm_num
private theorem prime_thirtyNineAK_149 : Nat.Prime 149 := by norm_num
private theorem prime_thirtyNineAK_157 : Nat.Prime 157 := by norm_num
private theorem prime_thirtyNineAK_163 : Nat.Prime 163 := by norm_num
private theorem prime_thirtyNineAK_167 : Nat.Prime 167 := by norm_num
private theorem prime_thirtyNineAK_173 : Nat.Prime 173 := by norm_num
private theorem prime_thirtyNineAK_181 : Nat.Prime 181 := by norm_num
private theorem prime_thirtyNineAK_191 : Nat.Prime 191 := by norm_num
private theorem prime_thirtyNineAK_193 : Nat.Prime 193 := by norm_num
private theorem prime_thirtyNineAK_197 : Nat.Prime 197 := by norm_num
private theorem prime_thirtyNineAK_199 : Nat.Prime 199 := by norm_num
private theorem prime_thirtyNineAK_211 : Nat.Prime 211 := by norm_num
private theorem prime_thirtyNineAK_223 : Nat.Prime 223 := by norm_num
private theorem prime_thirtyNineAK_227 : Nat.Prime 227 := by norm_num
private theorem prime_thirtyNineAK_229 : Nat.Prime 229 := by norm_num
private theorem prime_thirtyNineAK_239 : Nat.Prime 239 := by norm_num
private theorem prime_thirtyNineAK_241 : Nat.Prime 241 := by norm_num
private theorem prime_thirtyNineAK_251 : Nat.Prime 251 := by norm_num
private theorem prime_thirtyNineAK_257 : Nat.Prime 257 := by norm_num
private theorem prime_thirtyNineAK_263 : Nat.Prime 263 := by norm_num
private theorem prime_thirtyNineAK_269 : Nat.Prime 269 := by norm_num
private theorem prime_thirtyNineAK_271 : Nat.Prime 271 := by norm_num
private theorem prime_thirtyNineAK_281 : Nat.Prime 281 := by norm_num
private theorem prime_thirtyNineAK_307 : Nat.Prime 307 := by norm_num
private theorem prime_thirtyNineAK_311 : Nat.Prime 311 := by norm_num
private theorem prime_thirtyNineAK_313 : Nat.Prime 313 := by norm_num
private theorem prime_thirtyNineAK_337 : Nat.Prime 337 := by norm_num
private theorem prime_thirtyNineAK_347 : Nat.Prime 347 := by norm_num
private theorem prime_thirtyNineAK_349 : Nat.Prime 349 := by norm_num
private theorem prime_thirtyNineAK_359 : Nat.Prime 359 := by norm_num
private theorem prime_thirtyNineAK_367 : Nat.Prime 367 := by norm_num
private theorem prime_thirtyNineAK_383 : Nat.Prime 383 := by norm_num
private theorem prime_thirtyNineAK_397 : Nat.Prime 397 := by norm_num
private theorem prime_thirtyNineAK_409 : Nat.Prime 409 := by norm_num
private theorem prime_thirtyNineAK_419 : Nat.Prime 419 := by norm_num
private theorem prime_thirtyNineAK_457 : Nat.Prime 457 := by norm_num
private theorem prime_thirtyNineAK_467 : Nat.Prime 467 := by norm_num
private theorem prime_thirtyNineAK_487 : Nat.Prime 487 := by norm_num
private theorem prime_thirtyNineAK_499 : Nat.Prime 499 := by norm_num
private theorem prime_thirtyNineAK_521 : Nat.Prime 521 := by norm_num
private theorem prime_thirtyNineAK_523 : Nat.Prime 523 := by norm_num
private theorem prime_thirtyNineAK_547 : Nat.Prime 547 := by norm_num
private theorem prime_thirtyNineAK_557 : Nat.Prime 557 := by norm_num
private theorem prime_thirtyNineAK_563 : Nat.Prime 563 := by norm_num
private theorem prime_thirtyNineAK_619 : Nat.Prime 619 := by norm_num
private theorem prime_thirtyNineAK_631 : Nat.Prime 631 := by norm_num
private theorem prime_thirtyNineAK_647 : Nat.Prime 647 := by norm_num
private theorem prime_thirtyNineAK_653 : Nat.Prime 653 := by norm_num
private theorem prime_thirtyNineAK_659 : Nat.Prime 659 := by norm_num
private theorem prime_thirtyNineAK_661 : Nat.Prime 661 := by norm_num
private theorem prime_thirtyNineAK_691 : Nat.Prime 691 := by norm_num
private theorem prime_thirtyNineAK_719 : Nat.Prime 719 := by norm_num
private theorem prime_thirtyNineAK_727 : Nat.Prime 727 := by norm_num
private theorem prime_thirtyNineAK_733 : Nat.Prime 733 := by norm_num
private theorem prime_thirtyNineAK_739 : Nat.Prime 739 := by norm_num
private theorem prime_thirtyNineAK_751 : Nat.Prime 751 := by norm_num
private theorem prime_thirtyNineAK_769 : Nat.Prime 769 := by norm_num
private theorem prime_thirtyNineAK_787 : Nat.Prime 787 := by norm_num
private theorem prime_thirtyNineAK_809 : Nat.Prime 809 := by norm_num
private theorem prime_thirtyNineAK_887 : Nat.Prime 887 := by norm_num
private theorem prime_thirtyNineAK_967 : Nat.Prime 967 := by norm_num
private theorem prime_thirtyNineAK_971 : Nat.Prime 971 := by norm_num
private theorem prime_thirtyNineAK_977 : Nat.Prime 977 := by norm_num
private theorem prime_thirtyNineAK_1021 : Nat.Prime 1021 := by norm_num
private theorem prime_thirtyNineAK_1033 : Nat.Prime 1033 := by norm_num
private theorem prime_thirtyNineAK_1039 : Nat.Prime 1039 := by norm_num
private theorem prime_thirtyNineAK_1049 : Nat.Prime 1049 := by norm_num
private theorem prime_thirtyNineAK_1093 : Nat.Prime 1093 := by norm_num
private theorem prime_thirtyNineAK_1123 : Nat.Prime 1123 := by norm_num
private theorem prime_thirtyNineAK_1151 : Nat.Prime 1151 := by norm_num
private theorem prime_thirtyNineAK_1217 : Nat.Prime 1217 := by norm_num
private theorem prime_thirtyNineAK_1223 : Nat.Prime 1223 := by norm_num
private theorem prime_thirtyNineAK_1249 : Nat.Prime 1249 := by norm_num
private theorem prime_thirtyNineAK_1303 : Nat.Prime 1303 := by norm_num
private theorem prime_thirtyNineAK_1327 : Nat.Prime 1327 := by norm_num
private theorem prime_thirtyNineAK_1381 : Nat.Prime 1381 := by norm_num
private theorem prime_thirtyNineAK_1429 : Nat.Prime 1429 := by norm_num
private theorem prime_thirtyNineAK_1459 : Nat.Prime 1459 := by norm_num
private theorem prime_thirtyNineAK_1531 : Nat.Prime 1531 := by norm_num
private theorem prime_thirtyNineAK_1579 : Nat.Prime 1579 := by norm_num
private theorem prime_thirtyNineAK_1607 : Nat.Prime 1607 := by norm_num
private theorem prime_thirtyNineAK_1609 : Nat.Prime 1609 := by norm_num
private theorem prime_thirtyNineAK_1613 : Nat.Prime 1613 := by norm_num
private theorem prime_thirtyNineAK_1663 : Nat.Prime 1663 := by norm_num
private theorem prime_thirtyNineAK_1709 : Nat.Prime 1709 := by norm_num
private theorem prime_thirtyNineAK_1721 : Nat.Prime 1721 := by norm_num
private theorem prime_thirtyNineAK_1733 : Nat.Prime 1733 := by norm_num
private theorem prime_thirtyNineAK_1741 : Nat.Prime 1741 := by norm_num
private theorem prime_thirtyNineAK_1753 : Nat.Prime 1753 := by norm_num
private theorem prime_thirtyNineAK_1801 : Nat.Prime 1801 := by norm_num
private theorem prime_thirtyNineAK_1867 : Nat.Prime 1867 := by norm_num
private theorem prime_thirtyNineAK_1871 : Nat.Prime 1871 := by norm_num
private theorem prime_thirtyNineAK_1873 : Nat.Prime 1873 := by norm_num
private theorem prime_thirtyNineAK_1907 : Nat.Prime 1907 := by norm_num
private theorem prime_thirtyNineAK_1933 : Nat.Prime 1933 := by norm_num
private theorem prime_thirtyNineAK_2011 : Nat.Prime 2011 := by norm_num
private theorem prime_thirtyNineAK_2083 : Nat.Prime 2083 := by norm_num
private theorem prime_thirtyNineAK_2099 : Nat.Prime 2099 := by norm_num
private theorem prime_thirtyNineAK_2131 : Nat.Prime 2131 := by norm_num
private theorem prime_thirtyNineAK_2143 : Nat.Prime 2143 := by norm_num
private theorem prime_thirtyNineAK_2273 : Nat.Prime 2273 := by norm_num
private theorem prime_thirtyNineAK_2281 : Nat.Prime 2281 := by norm_num
private theorem prime_thirtyNineAK_2311 : Nat.Prime 2311 := by norm_num
private theorem prime_thirtyNineAK_2371 : Nat.Prime 2371 := by norm_num
private theorem prime_thirtyNineAK_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_thirtyNineAK_2593 : Nat.Prime 2593 := by norm_num
private theorem prime_thirtyNineAK_2719 : Nat.Prime 2719 := by norm_num
private theorem prime_thirtyNineAK_2767 : Nat.Prime 2767 := by norm_num
private theorem prime_thirtyNineAK_3011 : Nat.Prime 3011 := by norm_num
private theorem prime_thirtyNineAK_3041 : Nat.Prime 3041 := by norm_num
private theorem prime_thirtyNineAK_3089 : Nat.Prime 3089 := by norm_num
private theorem prime_thirtyNineAK_3109 : Nat.Prime 3109 := by norm_num
private theorem prime_thirtyNineAK_3137 : Nat.Prime 3137 := by norm_num
private theorem prime_thirtyNineAK_3163 : Nat.Prime 3163 := by norm_num
private theorem prime_thirtyNineAK_3259 : Nat.Prime 3259 := by norm_num
private theorem prime_thirtyNineAK_3299 : Nat.Prime 3299 := by norm_num
private theorem prime_thirtyNineAK_3391 : Nat.Prime 3391 := by norm_num
private theorem prime_thirtyNineAK_3583 : Nat.Prime 3583 := by norm_num
private theorem prime_thirtyNineAK_3691 : Nat.Prime 3691 := by norm_num
private theorem prime_thirtyNineAK_3877 : Nat.Prime 3877 := by norm_num
private theorem prime_thirtyNineAK_3919 : Nat.Prime 3919 := by norm_num
private theorem prime_thirtyNineAK_4001 : Nat.Prime 4001 := by norm_num
private theorem prime_thirtyNineAK_4003 : Nat.Prime 4003 := by norm_num
private theorem prime_thirtyNineAK_4093 : Nat.Prime 4093 := by norm_num
private theorem prime_thirtyNineAK_4099 : Nat.Prime 4099 := by norm_num
private theorem prime_thirtyNineAK_4159 : Nat.Prime 4159 := by norm_num
private theorem prime_thirtyNineAK_4243 : Nat.Prime 4243 := by norm_num
private theorem prime_thirtyNineAK_4357 : Nat.Prime 4357 := by norm_num
private theorem prime_thirtyNineAK_4591 : Nat.Prime 4591 := by norm_num
private theorem prime_thirtyNineAK_4639 : Nat.Prime 4639 := by norm_num
private theorem prime_thirtyNineAK_4987 : Nat.Prime 4987 := by norm_num
private theorem prime_thirtyNineAK_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_thirtyNineAK_5209 : Nat.Prime 5209 := by norm_num
private theorem prime_thirtyNineAK_5351 : Nat.Prime 5351 := by norm_num
private theorem prime_thirtyNineAK_5417 : Nat.Prime 5417 := by norm_num
private theorem prime_thirtyNineAK_5507 : Nat.Prime 5507 := by norm_num
private theorem prime_thirtyNineAK_5569 : Nat.Prime 5569 := by norm_num
private theorem prime_thirtyNineAK_5683 : Nat.Prime 5683 := by norm_num
private theorem prime_thirtyNineAK_6203 : Nat.Prime 6203 := by norm_num
private theorem prime_thirtyNineAK_6343 : Nat.Prime 6343 := by norm_num
private theorem prime_thirtyNineAK_6449 : Nat.Prime 6449 := by norm_num
private theorem prime_thirtyNineAK_6763 : Nat.Prime 6763 := by norm_num
private theorem prime_thirtyNineAK_7057 : Nat.Prime 7057 := by norm_num
private theorem prime_thirtyNineAK_7177 : Nat.Prime 7177 := by norm_num
private theorem prime_thirtyNineAK_7307 : Nat.Prime 7307 := by norm_num
private theorem prime_thirtyNineAK_7517 : Nat.Prime 7517 := by norm_num
private theorem prime_thirtyNineAK_7547 : Nat.Prime 7547 := by norm_num
private theorem prime_thirtyNineAK_7757 : Nat.Prime 7757 := by norm_num
private theorem prime_thirtyNineAK_8081 : Nat.Prime 8081 := by norm_num
private theorem prime_thirtyNineAK_8233 : Nat.Prime 8233 := by norm_num
private theorem prime_thirtyNineAK_8419 : Nat.Prime 8419 := by norm_num
private theorem prime_thirtyNineAK_8443 : Nat.Prime 8443 := by norm_num
private theorem prime_thirtyNineAK_8521 : Nat.Prime 8521 := by norm_num
private theorem prime_thirtyNineAK_8597 : Nat.Prime 8597 := by norm_num
private theorem prime_thirtyNineAK_8677 : Nat.Prime 8677 := by norm_num
private theorem prime_thirtyNineAK_8933 : Nat.Prime 8933 := by norm_num
private theorem prime_thirtyNineAK_9241 : Nat.Prime 9241 := by norm_num
private theorem prime_thirtyNineAK_9341 : Nat.Prime 9341 := by norm_num
private theorem prime_thirtyNineAK_9437 : Nat.Prime 9437 := by norm_num
private theorem prime_thirtyNineAK_9511 : Nat.Prime 9511 := by norm_num
private theorem prime_thirtyNineAK_9719 : Nat.Prime 9719 := by norm_num
private theorem prime_thirtyNineAK_9721 : Nat.Prime 9721 := by norm_num
private theorem prime_thirtyNineAK_9887 : Nat.Prime 9887 := by norm_num
private theorem prime_thirtyNineAK_10159 : Nat.Prime 10159 := by norm_num
private theorem prime_thirtyNineAK_10567 : Nat.Prime 10567 := by norm_num
private theorem prime_thirtyNineAK_10949 : Nat.Prime 10949 := by norm_num
private theorem prime_thirtyNineAK_11027 : Nat.Prime 11027 := by norm_num
private theorem prime_thirtyNineAK_11423 : Nat.Prime 11423 := by norm_num
private theorem prime_thirtyNineAK_11783 : Nat.Prime 11783 := by norm_num
private theorem prime_thirtyNineAK_12301 : Nat.Prime 12301 := by norm_num
private theorem prime_thirtyNineAK_12377 : Nat.Prime 12377 := by norm_num
private theorem prime_thirtyNineAK_12391 : Nat.Prime 12391 := by norm_num
private theorem prime_thirtyNineAK_12569 : Nat.Prime 12569 := by norm_num
private theorem prime_thirtyNineAK_12619 : Nat.Prime 12619 := by norm_num
private theorem prime_thirtyNineAK_13399 : Nat.Prime 13399 := by norm_num
private theorem prime_thirtyNineAK_13687 : Nat.Prime 13687 := by norm_num
private theorem prime_thirtyNineAK_13859 : Nat.Prime 13859 := by norm_num
private theorem prime_thirtyNineAK_14419 : Nat.Prime 14419 := by norm_num
private theorem prime_thirtyNineAK_14879 : Nat.Prime 14879 := by norm_num
private theorem prime_thirtyNineAK_15173 : Nat.Prime 15173 := by norm_num
private theorem prime_thirtyNineAK_15373 : Nat.Prime 15373 := by norm_num
private theorem prime_thirtyNineAK_15607 : Nat.Prime 15607 := by norm_num
private theorem prime_thirtyNineAK_15733 : Nat.Prime 15733 := by norm_num
private theorem prime_thirtyNineAK_15877 : Nat.Prime 15877 := by norm_num
private theorem prime_thirtyNineAK_16097 : Nat.Prime 16097 := by norm_num
private theorem prime_thirtyNineAK_16453 : Nat.Prime 16453 := by norm_num
private theorem prime_thirtyNineAK_17327 : Nat.Prime 17327 := by norm_num
private theorem prime_thirtyNineAK_17383 : Nat.Prime 17383 := by norm_num
private theorem prime_thirtyNineAK_17449 : Nat.Prime 17449 := by norm_num
private theorem prime_thirtyNineAK_17627 : Nat.Prime 17627 := by norm_num
private theorem prime_thirtyNineAK_19319 : Nat.Prime 19319 := by norm_num
private theorem prime_thirtyNineAK_19387 : Nat.Prime 19387 := by norm_num
private theorem prime_thirtyNineAK_19447 : Nat.Prime 19447 := by norm_num
private theorem prime_thirtyNineAK_20023 : Nat.Prime 20023 := by norm_num
private theorem prime_thirtyNineAK_21569 : Nat.Prime 21569 := by norm_num
private theorem prime_thirtyNineAK_21611 : Nat.Prime 21611 := by norm_num
private theorem prime_thirtyNineAK_22229 : Nat.Prime 22229 := by norm_num
private theorem prime_thirtyNineAK_23081 : Nat.Prime 23081 := by norm_num
private theorem prime_thirtyNineAK_23761 : Nat.Prime 23761 := by norm_num
private theorem prime_thirtyNineAK_23879 : Nat.Prime 23879 := by norm_num
private theorem prime_thirtyNineAK_24019 : Nat.Prime 24019 := by norm_num
private theorem prime_thirtyNineAK_24953 : Nat.Prime 24953 := by norm_num
private theorem prime_thirtyNineAK_25951 : Nat.Prime 25951 := by norm_num
private theorem prime_thirtyNineAK_28201 : Nat.Prime 28201 := by norm_num
private theorem prime_thirtyNineAK_28229 : Nat.Prime 28229 := by norm_num
private theorem prime_thirtyNineAK_28351 : Nat.Prime 28351 := by norm_num
private theorem prime_thirtyNineAK_32029 : Nat.Prime 32029 := by norm_num
private theorem prime_thirtyNineAK_33311 : Nat.Prime 33311 := by norm_num
private theorem prime_thirtyNineAK_33829 : Nat.Prime 33829 := by norm_num
private theorem prime_thirtyNineAK_34147 : Nat.Prime 34147 := by norm_num
private theorem prime_thirtyNineAK_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_thirtyNineAK_36263 : Nat.Prime 36263 := by norm_num
private theorem prime_thirtyNineAK_37013 : Nat.Prime 37013 := by norm_num
private theorem prime_thirtyNineAK_37309 : Nat.Prime 37309 := by norm_num
private theorem prime_thirtyNineAK_39581 : Nat.Prime 39581 := by norm_num
private theorem prime_thirtyNineAK_39791 : Nat.Prime 39791 := by norm_num
private theorem prime_thirtyNineAK_46817 : Nat.Prime 46817 := by norm_num
private theorem prime_thirtyNineAK_46861 : Nat.Prime 46861 := by norm_num
private theorem prime_thirtyNineAK_47149 : Nat.Prime 47149 := by norm_num
private theorem prime_thirtyNineAK_47659 : Nat.Prime 47659 := by norm_num
private theorem prime_thirtyNineAK_54949 : Nat.Prime 54949 := by norm_num
private theorem prime_thirtyNineAK_61343 : Nat.Prime 61343 := by norm_num
private theorem prime_thirtyNineAK_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_thirtyNineAK_65981 : Nat.Prime 65981 := by norm_num
private theorem prime_thirtyNineAK_67819 : Nat.Prime 67819 := by norm_num
private theorem prime_thirtyNineAK_74323 : Nat.Prime 74323 := by norm_num
private theorem prime_thirtyNineAK_76259 : Nat.Prime 76259 := by norm_num
private theorem prime_thirtyNineAK_76423 : Nat.Prime 76423 := by norm_num
private theorem prime_thirtyNineAK_77101 : Nat.Prime 77101 := by norm_num
private theorem prime_thirtyNineAK_79943 : Nat.Prime 79943 := by norm_num
private theorem prime_thirtyNineAK_81047 : Nat.Prime 81047 := by norm_num
private theorem prime_thirtyNineAK_81353 : Nat.Prime 81353 := by norm_num
private theorem prime_thirtyNineAK_82487 : Nat.Prime 82487 := by norm_num
private theorem prime_thirtyNineAK_83299 : Nat.Prime 83299 := by norm_num
private theorem prime_thirtyNineAK_84017 : Nat.Prime 84017 := by norm_num
private theorem prime_thirtyNineAK_85247 : Nat.Prime 85247 := by norm_num
private theorem prime_thirtyNineAK_85429 : Nat.Prime 85429 := by norm_num
private theorem prime_thirtyNineAK_85469 : Nat.Prime 85469 := by norm_num
private theorem prime_thirtyNineAK_88807 : Nat.Prime 88807 := by norm_num
private theorem prime_thirtyNineAK_93811 : Nat.Prime 93811 := by norm_num
private theorem prime_thirtyNineAK_95083 : Nat.Prime 95083 := by norm_num
private theorem prime_thirtyNineAK_96211 : Nat.Prime 96211 := by norm_num
private theorem prime_thirtyNineAK_96697 : Nat.Prime 96697 := by norm_num
private theorem prime_thirtyNineAK_98717 : Nat.Prime 98717 := by norm_num
private theorem prime_thirtyNineAK_104009 : Nat.Prime 104009 := by norm_num
private theorem prime_thirtyNineAK_105767 : Nat.Prime 105767 := by norm_num
private theorem prime_thirtyNineAK_108179 : Nat.Prime 108179 := by norm_num
private theorem prime_thirtyNineAK_113167 : Nat.Prime 113167 := by norm_num
private theorem prime_thirtyNineAK_114593 : Nat.Prime 114593 := by norm_num
private theorem prime_thirtyNineAK_118691 : Nat.Prime 118691 := by norm_num
private theorem prime_thirtyNineAK_119653 : Nat.Prime 119653 := by norm_num
private theorem prime_thirtyNineAK_124147 : Nat.Prime 124147 := by norm_num
private theorem prime_thirtyNineAK_131413 : Nat.Prime 131413 := by norm_num
private theorem prime_thirtyNineAK_145037 : Nat.Prime 145037 := by norm_num
private theorem prime_thirtyNineAK_145459 : Nat.Prime 145459 := by norm_num
private theorem prime_thirtyNineAK_146173 : Nat.Prime 146173 := by norm_num
private theorem prime_thirtyNineAK_153929 : Nat.Prime 153929 := by norm_num
private theorem prime_thirtyNineAK_158759 : Nat.Prime 158759 := by norm_num
private theorem prime_thirtyNineAK_159779 : Nat.Prime 159779 := by norm_num
private theorem prime_thirtyNineAK_161017 : Nat.Prime 161017 := by norm_num
private theorem prime_thirtyNineAK_166931 : Nat.Prime 166931 := by norm_num
private theorem prime_thirtyNineAK_181199 : Nat.Prime 181199 := by norm_num
private theorem prime_thirtyNineAK_184633 : Nat.Prime 184633 := by norm_num
private theorem prime_thirtyNineAK_209497 : Nat.Prime 209497 := by norm_num
private theorem prime_thirtyNineAK_209623 : Nat.Prime 209623 := by norm_num
private theorem prime_thirtyNineAK_217223 : Nat.Prime 217223 := by norm_num
private theorem prime_thirtyNineAK_243583 : Nat.Prime 243583 := by norm_num
private theorem prime_thirtyNineAK_244567 : Nat.Prime 244567 := by norm_num
private theorem prime_thirtyNineAK_252869 : Nat.Prime 252869 := by norm_num
private theorem prime_thirtyNineAK_254927 : Nat.Prime 254927 := by norm_num
private theorem prime_thirtyNineAK_264779 : Nat.Prime 264779 := by norm_num
private theorem prime_thirtyNineAK_265247 : Nat.Prime 265247 := by norm_num
private theorem prime_thirtyNineAK_272269 : Nat.Prime 272269 := by norm_num
private theorem prime_thirtyNineAK_276557 : Nat.Prime 276557 := by norm_num
private theorem prime_thirtyNineAK_318313 : Nat.Prime 318313 := by norm_num
private theorem prime_thirtyNineAK_335009 : Nat.Prime 335009 := by norm_num
private theorem prime_thirtyNineAK_347059 : Nat.Prime 347059 := by norm_num
private theorem prime_thirtyNineAK_392099 : Nat.Prime 392099 := by norm_num
private theorem prime_thirtyNineAK_395891 : Nat.Prime 395891 := by norm_num
private theorem prime_thirtyNineAK_409901 : Nat.Prime 409901 := by norm_num
private theorem prime_thirtyNineAK_413141 : Nat.Prime 413141 := by norm_num
private theorem prime_thirtyNineAK_452671 : Nat.Prime 452671 := by norm_num
private theorem prime_thirtyNineAK_452857 : Nat.Prime 452857 := by norm_num
private theorem prime_thirtyNineAK_517267 : Nat.Prime 517267 := by norm_num
private theorem prime_thirtyNineAK_556859 : Nat.Prime 556859 := by norm_num
private theorem prime_thirtyNineAK_558979 : Nat.Prime 558979 := by norm_num
private theorem prime_thirtyNineAK_586723 : Nat.Prime 586723 := by norm_num
private theorem prime_thirtyNineAK_597803 : Nat.Prime 597803 := by norm_num
private theorem prime_thirtyNineAK_618991 : Nat.Prime 618991 := by norm_num
private theorem prime_thirtyNineAK_657653 : Nat.Prime 657653 := by norm_num
private theorem prime_thirtyNineAK_660659 : Nat.Prime 660659 := by norm_num
private theorem prime_thirtyNineAK_667123 : Nat.Prime 667123 := by norm_num
private theorem prime_thirtyNineAK_708899 : Nat.Prime 708899 := by norm_num
private theorem prime_thirtyNineAK_759313 : Nat.Prime 759313 := by norm_num
private theorem prime_thirtyNineAK_774811 : Nat.Prime 774811 := by norm_num
private theorem prime_thirtyNineAK_802603 : Nat.Prime 802603 := by norm_num
private theorem prime_thirtyNineAK_809983 : Nat.Prime 809983 := by norm_num
private theorem prime_thirtyNineAK_955337 : Nat.Prime 955337 := by norm_num
private theorem prime_thirtyNineAK_999007 : Nat.Prime 999007 := by norm_num
private theorem prime_thirtyNineAK_1029563 : Nat.Prime 1029563 := by norm_num
private theorem prime_thirtyNineAK_1071761 : Nat.Prime 1071761 := by norm_num
private theorem prime_thirtyNineAK_1093943 : Nat.Prime 1093943 := by norm_num
private theorem prime_thirtyNineAK_1214159 : Nat.Prime 1214159 := by norm_num
private theorem prime_thirtyNineAK_1255519 : Nat.Prime 1255519 := by norm_num
private theorem prime_thirtyNineAK_1390841 : Nat.Prime 1390841 := by norm_num
private theorem prime_thirtyNineAK_1430419 : Nat.Prime 1430419 := by norm_num
private theorem prime_thirtyNineAK_1430543 : Nat.Prime 1430543 := by norm_num
private theorem prime_thirtyNineAK_1509031 : Nat.Prime 1509031 := by norm_num
private theorem prime_thirtyNineAK_1543501 : Nat.Prime 1543501 := by norm_num
private theorem prime_thirtyNineAK_1582963 : Nat.Prime 1582963 := by norm_num
private theorem prime_thirtyNineAK_1583749 : Nat.Prime 1583749 := by norm_num
private theorem prime_thirtyNineAK_1584001 : Nat.Prime 1584001 := by norm_num
private theorem prime_thirtyNineAK_1607371 : Nat.Prime 1607371 := by norm_num
private theorem prime_thirtyNineAK_1616627 : Nat.Prime 1616627 := by norm_num
private theorem prime_thirtyNineAK_1618531 : Nat.Prime 1618531 := by norm_num
private theorem prime_thirtyNineAK_1628203 : Nat.Prime 1628203 := by norm_num
private theorem prime_thirtyNineAK_1756691 : Nat.Prime 1756691 := by norm_num
private theorem prime_thirtyNineAK_1804477 : Nat.Prime 1804477 := by norm_num
private theorem prime_thirtyNineAK_1883989 : Nat.Prime 1883989 := by norm_num
private theorem prime_thirtyNineAK_1921687 : Nat.Prime 1921687 := by norm_num
private theorem prime_thirtyNineAK_1996289 : Nat.Prime 1996289 := by norm_num
private theorem prime_thirtyNineAK_2220277 : Nat.Prime 2220277 := by norm_num
private theorem prime_thirtyNineAK_2273119 : Nat.Prime 2273119 := by norm_num
private theorem prime_thirtyNineAK_2596501 : Nat.Prime 2596501 := by norm_num
private theorem prime_thirtyNineAK_2692367 : Nat.Prime 2692367 := by norm_num
private theorem prime_thirtyNineAK_2797999 : Nat.Prime 2797999 := by norm_num
private theorem prime_thirtyNineAK_2895439 : Nat.Prime 2895439 := by norm_num
private theorem prime_thirtyNineAK_3089857 : Nat.Prime 3089857 := by norm_num
private theorem prime_thirtyNineAK_3184277 : Nat.Prime 3184277 := by norm_num
private theorem prime_thirtyNineAK_3304963 : Nat.Prime 3304963 := by norm_num
private theorem prime_thirtyNineAK_3399569 : Nat.Prime 3399569 := by norm_num
private theorem prime_thirtyNineAK_3581129 : Nat.Prime 3581129 := by norm_num
private theorem prime_thirtyNineAK_3670757 : Nat.Prime 3670757 := by norm_num
private theorem prime_thirtyNineAK_4259207 : Nat.Prime 4259207 := by norm_num
private theorem prime_thirtyNineAK_4553573 : Nat.Prime 4553573 := by norm_num
private theorem prime_thirtyNineAK_4653827 : Nat.Prime 4653827 := by norm_num
private theorem prime_thirtyNineAK_4657739 : Nat.Prime 4657739 := by norm_num
private theorem prime_thirtyNineAK_4749527 : Nat.Prime 4749527 := by norm_num
private theorem prime_thirtyNineAK_4921601 : Nat.Prime 4921601 := by norm_num
private theorem prime_thirtyNineAK_5140117 : Nat.Prime 5140117 := by norm_num
private theorem prime_thirtyNineAK_5246567 : Nat.Prime 5246567 := by norm_num
private theorem prime_thirtyNineAK_5309207 : Nat.Prime 5309207 := by norm_num
private theorem prime_thirtyNineAK_6317807 : Nat.Prime 6317807 := by norm_num
private theorem prime_thirtyNineAK_6324089 : Nat.Prime 6324089 := by norm_num
private theorem prime_thirtyNineAK_6677087 : Nat.Prime 6677087 := by norm_num
private theorem prime_thirtyNineAK_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_thirtyNineAK_8042669 : Nat.Prime 8042669 := by norm_num
private theorem prime_thirtyNineAK_8270923 : Nat.Prime 8270923 := by norm_num
private theorem prime_thirtyNineAK_8274073 : Nat.Prime 8274073 := by norm_num
private theorem prime_thirtyNineAK_8411981 : Nat.Prime 8411981 := by norm_num
private theorem prime_thirtyNineAK_8896453 : Nat.Prime 8896453 := by norm_num
private theorem prime_thirtyNineAK_9269333 : Nat.Prime 9269333 := by norm_num
private theorem prime_thirtyNineAK_9320287 : Nat.Prime 9320287 := by norm_num
private theorem prime_thirtyNineAK_9389251 : Nat.Prime 9389251 := by norm_num
private theorem prime_thirtyNineAK_9744517 : Nat.Prime 9744517 := by norm_num
private theorem prime_thirtyNineAK_9792301 : Nat.Prime 9792301 := by norm_num
private theorem prime_thirtyNineAK_9794143 : Nat.Prime 9794143 := by norm_num
private theorem prime_thirtyNineAK_10537391 : Nat.Prime 10537391 := by norm_num
private theorem prime_thirtyNineAK_10550563 : Nat.Prime 10550563 := by norm_num
private theorem prime_thirtyNineAK_10747391 : Nat.Prime 10747391 := by norm_num
private theorem prime_thirtyNineAK_10801067 : Nat.Prime 10801067 := by norm_num
private theorem prime_thirtyNineAK_10958119 : Nat.Prime 10958119 := by norm_num
private theorem prime_thirtyNineAK_11542109 : Nat.Prime 11542109 := by norm_num
private theorem prime_thirtyNineAK_11826007 : Nat.Prime 11826007 := by norm_num
private theorem prime_thirtyNineAK_12245371 : Nat.Prime 12245371 := by norm_num
private theorem prime_thirtyNineAK_13821571 : Nat.Prime 13821571 := by norm_num
private theorem prime_thirtyNineAK_13837177 : Nat.Prime 13837177 := by norm_num
private theorem prime_thirtyNineAK_14999741 : Nat.Prime 14999741 := by norm_num
private theorem prime_thirtyNineAK_17007943 : Nat.Prime 17007943 := by norm_num
private theorem prime_thirtyNineAK_19430861 : Nat.Prime 19430861 := by norm_num
private theorem prime_thirtyNineAK_22285007 : Nat.Prime 22285007 := by norm_num
private theorem prime_thirtyNineAK_22724479 : Nat.Prime 22724479 := by norm_num
private theorem prime_thirtyNineAK_24089309 : Nat.Prime 24089309 := by norm_num
private theorem prime_thirtyNineAK_24309517 : Nat.Prime 24309517 := by norm_num
private theorem prime_thirtyNineAK_26146481 : Nat.Prime 26146481 := by norm_num
private theorem prime_thirtyNineAK_26281223 : Nat.Prime 26281223 := by norm_num
private theorem prime_thirtyNineAK_27509047 : Nat.Prime 27509047 := by norm_num

private theorem prime_thirtyNineAK_30659441 : Nat.Prime 30659441 := by
  apply lucas_primality 30659441 (11 : ZMod 30659441)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (7, 1), (53, 1), (1033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (7, 1), (53, 1), (1033, 1)] : List FactorBlock).map factorBlockValue).prod) = 30659441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_53
      · exact prime_thirtyNineAK_1033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 30659441) ^ 15329720 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (11 : ZMod 30659441) ^ 6131888 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (11 : ZMod 30659441) ^ 4379920 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (11 : ZMod 30659441) ^ 578480 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (11 : ZMod 30659441) ^ 29680 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_32282021 : Nat.Prime 32282021 := by
  apply lucas_primality 32282021 (2 : ZMod 32282021)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (83, 1), (19447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (83, 1), (19447, 1)] : List FactorBlock).map factorBlockValue).prod) = 32282021 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_83
      · exact prime_thirtyNineAK_19447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32282021) ^ 16141010 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 32282021) ^ 6456404 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 32282021) ^ 388940 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 32282021) ^ 1660 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_33371411 : Nat.Prime 33371411 := by
  apply lucas_primality 33371411 (6 : ZMod 33371411)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (37, 1), (47, 1), (101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (37, 1), (47, 1), (101, 1)] : List FactorBlock).map factorBlockValue).prod) = 33371411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_19
      · exact prime_thirtyNineAK_37
      · exact prime_thirtyNineAK_47
      · exact prime_thirtyNineAK_101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 33371411) ^ 16685705 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (6 : ZMod 33371411) ^ 6674282 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (6 : ZMod 33371411) ^ 1756390 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (6 : ZMod 33371411) ^ 901930 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (6 : ZMod 33371411) ^ 710030 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (6 : ZMod 33371411) ^ 330410 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_33891713 : Nat.Prime 33891713 := by
  apply lucas_primality 33891713 (3 : ZMod 33891713)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (264779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (264779, 1)] : List FactorBlock).map factorBlockValue).prod) = 33891713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_264779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 33891713) ^ 16945856 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 33891713) ^ 128 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_39198199 : Nat.Prime 39198199 := by
  apply lucas_primality 39198199 (6 : ZMod 39198199)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 2), (29, 1), (31, 1), (43, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 2), (29, 1), (31, 1), (43, 1)] : List FactorBlock).map factorBlockValue).prod) = 39198199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_13
      · exact prime_thirtyNineAK_29
      · exact prime_thirtyNineAK_31
      · exact prime_thirtyNineAK_43
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 39198199) ^ 19599099 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (6 : ZMod 39198199) ^ 13066066 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (6 : ZMod 39198199) ^ 3015246 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (6 : ZMod 39198199) ^ 1351662 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (6 : ZMod 39198199) ^ 1264458 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (6 : ZMod 39198199) ^ 911586 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_40346827 : Nat.Prime 40346827 := by
  apply lucas_primality 40346827 (2 : ZMod 40346827)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (517267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (517267, 1)] : List FactorBlock).map factorBlockValue).prod) = 40346827 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_13
      · exact prime_thirtyNineAK_517267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40346827) ^ 20173413 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 40346827) ^ 13448942 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 40346827) ^ 3103602 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 40346827) ^ 78 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_42857783 : Nat.Prime 42857783 := by
  apply lucas_primality 42857783 (5 : ZMod 42857783)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (17, 1), (114593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (17, 1), (114593, 1)] : List FactorBlock).map factorBlockValue).prod) = 42857783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_11
      · exact prime_thirtyNineAK_17
      · exact prime_thirtyNineAK_114593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 42857783) ^ 21428891 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 3896162 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 2521046 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 374 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_46053307 : Nat.Prime 46053307 := by
  apply lucas_primality 46053307 (2 : ZMod 46053307)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (13, 1), (17, 2), (227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (13, 1), (17, 2), (227, 1)] : List FactorBlock).map factorBlockValue).prod) = 46053307 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_13
      · exact prime_thirtyNineAK_17
      · exact prime_thirtyNineAK_227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 46053307) ^ 23026653 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 46053307) ^ 15351102 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 46053307) ^ 3542562 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 46053307) ^ 2709018 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 46053307) ^ 202878 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_48334903 : Nat.Prime 48334903 := by
  apply lucas_primality 48334903 (3 : ZMod 48334903)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 2), (9511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 2), (9511, 1)] : List FactorBlock).map factorBlockValue).prod) = 48334903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_11
      · exact prime_thirtyNineAK_9511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 48334903) ^ 24167451 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 48334903) ^ 16111634 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 48334903) ^ 6904986 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 48334903) ^ 4394082 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 48334903) ^ 5082 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_53009633 : Nat.Prime 53009633 := by
  apply lucas_primality 53009633 (3 : ZMod 53009633)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (13, 1), (79, 1), (1613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (13, 1), (79, 1), (1613, 1)] : List FactorBlock).map factorBlockValue).prod) = 53009633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_13
      · exact prime_thirtyNineAK_79
      · exact prime_thirtyNineAK_1613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 53009633) ^ 26504816 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 53009633) ^ 4077664 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 53009633) ^ 671008 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 53009633) ^ 32864 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_55565339 : Nat.Prime 55565339 := by
  apply lucas_primality 55565339 (2 : ZMod 55565339)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (191, 1), (145459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (191, 1), (145459, 1)] : List FactorBlock).map factorBlockValue).prod) = 55565339 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_191
      · exact prime_thirtyNineAK_145459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 55565339) ^ 27782669 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 55565339) ^ 290918 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 55565339) ^ 382 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_56471449 : Nat.Prime 56471449 := by
  apply lucas_primality 56471449 (7 : ZMod 56471449)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (409, 1), (523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (409, 1), (523, 1)] : List FactorBlock).map factorBlockValue).prod) = 56471449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_11
      · exact prime_thirtyNineAK_409
      · exact prime_thirtyNineAK_523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 56471449) ^ 28235724 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 56471449) ^ 18823816 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 56471449) ^ 5133768 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 56471449) ^ 138072 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 56471449) ^ 107976 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_60712807 : Nat.Prime 60712807 := by
  apply lucas_primality 60712807 (3 : ZMod 60712807)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (131413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (131413, 1)] : List FactorBlock).map factorBlockValue).prod) = 60712807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_11
      · exact prime_thirtyNineAK_131413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 60712807) ^ 30356403 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 60712807) ^ 20237602 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 60712807) ^ 8673258 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 60712807) ^ 5519346 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 60712807) ^ 462 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_61352219 : Nat.Prime 61352219 := by
  apply lucas_primality 61352219 (2 : ZMod 61352219)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (1804477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (1804477, 1)] : List FactorBlock).map factorBlockValue).prod) = 61352219 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_17
      · exact prime_thirtyNineAK_1804477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 61352219) ^ 30676109 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 61352219) ^ 3608954 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 61352219) ^ 34 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_68392019 : Nat.Prime 68392019 := by
  apply lucas_primality 68392019 (2 : ZMod 68392019)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (41, 1), (36263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (41, 1), (36263, 1)] : List FactorBlock).map factorBlockValue).prod) = 68392019 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_23
      · exact prime_thirtyNineAK_41
      · exact prime_thirtyNineAK_36263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 68392019) ^ 34196009 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 68392019) ^ 2973566 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 68392019) ^ 1668098 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 68392019) ^ 1886 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_80219981 : Nat.Prime 80219981 := by
  apply lucas_primality 80219981 (2 : ZMod 80219981)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (257, 1), (15607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (257, 1), (15607, 1)] : List FactorBlock).map factorBlockValue).prod) = 80219981 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_257
      · exact prime_thirtyNineAK_15607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 80219981) ^ 40109990 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 80219981) ^ 16043996 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 80219981) ^ 312140 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 80219981) ^ 5140 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_81540863 : Nat.Prime 81540863 := by
  apply lucas_primality 81540863 (5 : ZMod 81540863)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (181, 1), (17327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (181, 1), (17327, 1)] : List FactorBlock).map factorBlockValue).prod) = 81540863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_13
      · exact prime_thirtyNineAK_181
      · exact prime_thirtyNineAK_17327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 81540863) ^ 40770431 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 81540863) ^ 6272374 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 81540863) ^ 450502 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 81540863) ^ 4706 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_83511149 : Nat.Prime 83511149 := by
  apply lucas_primality 83511149 (2 : ZMod 83511149)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (31, 1), (96211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (31, 1), (96211, 1)] : List FactorBlock).map factorBlockValue).prod) = 83511149 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_31
      · exact prime_thirtyNineAK_96211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 83511149) ^ 41755574 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 83511149) ^ 11930164 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 83511149) ^ 2693908 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 83511149) ^ 868 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_84294913 : Nat.Prime 84294913 := by
  apply lucas_primality 84294913 (14 : ZMod 84294913)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (13, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (13, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod) = 84294913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_13
      · exact prime_thirtyNineAK_8443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 84294913) ^ 42147456 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 28098304 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 6484224 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 9984 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_104981389 : Nat.Prime 104981389 := by
  apply lucas_primality 104981389 (2 : ZMod 104981389)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (83, 1), (109, 1), (967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (83, 1), (109, 1), (967, 1)] : List FactorBlock).map factorBlockValue).prod) = 104981389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_83
      · exact prime_thirtyNineAK_109
      · exact prime_thirtyNineAK_967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 104981389) ^ 52490694 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 104981389) ^ 34993796 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 104981389) ^ 1264836 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 104981389) ^ 963132 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 104981389) ^ 108564 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_106019267 : Nat.Prime 106019267 := by
  apply lucas_primality 106019267 (2 : ZMod 106019267)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53009633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53009633, 1)] : List FactorBlock).map factorBlockValue).prod) = 106019267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_53009633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 106019267) ^ 53009633 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 106019267) ^ 2 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_109193459 : Nat.Prime 109193459 := by
  apply lucas_primality 109193459 (2 : ZMod 109193459)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (149, 1), (33311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (149, 1), (33311, 1)] : List FactorBlock).map factorBlockValue).prod) = 109193459 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_11
      · exact prime_thirtyNineAK_149
      · exact prime_thirtyNineAK_33311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 109193459) ^ 54596729 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 109193459) ^ 9926678 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 109193459) ^ 732842 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 109193459) ^ 3278 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_148272073 : Nat.Prime 148272073 := by
  apply lucas_primality 148272073 (5 : ZMod 148272073)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (41, 1), (67, 1), (173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (41, 1), (67, 1), (173, 1)] : List FactorBlock).map factorBlockValue).prod) = 148272073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_13
      · exact prime_thirtyNineAK_41
      · exact prime_thirtyNineAK_67
      · exact prime_thirtyNineAK_173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 148272073) ^ 74136036 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 148272073) ^ 49424024 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 148272073) ^ 11405544 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 148272073) ^ 3616392 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 148272073) ^ 2213016 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 148272073) ^ 857064 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_148364669 : Nat.Prime 148364669 := by
  apply lucas_primality 148364669 (2 : ZMod 148364669)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1607, 1), (23081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1607, 1), (23081, 1)] : List FactorBlock).map factorBlockValue).prod) = 148364669 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_1607
      · exact prime_thirtyNineAK_23081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 148364669) ^ 74182334 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 148364669) ^ 92324 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 148364669) ^ 6428 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_148648817 : Nat.Prime 148648817 := by
  apply lucas_primality 148648817 (3 : ZMod 148648817)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (17, 1), (23, 1), (23761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (17, 1), (23, 1), (23761, 1)] : List FactorBlock).map factorBlockValue).prod) = 148648817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_17
      · exact prime_thirtyNineAK_23
      · exact prime_thirtyNineAK_23761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 148648817) ^ 74324408 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 148648817) ^ 8744048 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 148648817) ^ 6462992 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 148648817) ^ 6256 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_148662851 : Nat.Prime 148662851 := by
  apply lucas_primality 148662851 (2 : ZMod 148662851)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (269, 1), (1579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (269, 1), (1579, 1)] : List FactorBlock).map factorBlockValue).prod) = 148662851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_269
      · exact prime_thirtyNineAK_1579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 148662851) ^ 74331425 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 148662851) ^ 29732570 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 148662851) ^ 21237550 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 148662851) ^ 552650 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 148662851) ^ 94150 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_158288029 : Nat.Prime 158288029 := by
  apply lucas_primality 158288029 (6 : ZMod 158288029)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (157, 1), (84017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (157, 1), (84017, 1)] : List FactorBlock).map factorBlockValue).prod) = 158288029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_157
      · exact prime_thirtyNineAK_84017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 158288029) ^ 79144014 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (6 : ZMod 158288029) ^ 52762676 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (6 : ZMod 158288029) ^ 1008204 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (6 : ZMod 158288029) ^ 1884 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_160439963 : Nat.Prime 160439963 := by
  apply lucas_primality 160439963 (2 : ZMod 160439963)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (80219981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (80219981, 1)] : List FactorBlock).map factorBlockValue).prod) = 160439963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_80219981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 160439963) ^ 80219981 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 160439963) ^ 2 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_164681581 : Nat.Prime 164681581 := by
  apply lucas_primality 164681581 (10 : ZMod 164681581)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (392099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (392099, 1)] : List FactorBlock).map factorBlockValue).prod) = 164681581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_392099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 164681581) ^ 82340790 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (10 : ZMod 164681581) ^ 54893860 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (10 : ZMod 164681581) ^ 32936316 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (10 : ZMod 164681581) ^ 23525940 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (10 : ZMod 164681581) ^ 420 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_168197789 : Nat.Prime 168197789 := by
  apply lucas_primality 168197789 (2 : ZMod 168197789)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (113, 1), (33829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (113, 1), (33829, 1)] : List FactorBlock).map factorBlockValue).prod) = 168197789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_11
      · exact prime_thirtyNineAK_113
      · exact prime_thirtyNineAK_33829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 168197789) ^ 84098894 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 168197789) ^ 15290708 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 168197789) ^ 1488476 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 168197789) ^ 4972 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_189673039 : Nat.Prime 189673039 := by
  apply lucas_primality 189673039 (3 : ZMod 189673039)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (10537391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (10537391, 1)] : List FactorBlock).map factorBlockValue).prod) = 189673039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_10537391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 189673039) ^ 94836519 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 189673039) ^ 63224346 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 189673039) ^ 18 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_220118471 : Nat.Prime 220118471 := by
  apply lucas_primality 220118471 (11 : ZMod 220118471)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (13, 1), (153929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (13, 1), (153929, 1)] : List FactorBlock).map factorBlockValue).prod) = 220118471 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_11
      · exact prime_thirtyNineAK_13
      · exact prime_thirtyNineAK_153929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 220118471) ^ 110059235 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (11 : ZMod 220118471) ^ 44023694 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (11 : ZMod 220118471) ^ 20010770 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (11 : ZMod 220118471) ^ 16932190 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (11 : ZMod 220118471) ^ 1430 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_225885797 : Nat.Prime 225885797 := by
  apply lucas_primality 225885797 (2 : ZMod 225885797)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (56471449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (56471449, 1)] : List FactorBlock).map factorBlockValue).prod) = 225885797 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_56471449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 225885797) ^ 112942898 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 225885797) ^ 4 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_230395727 : Nat.Prime 230395727 := by
  apply lucas_primality 230395727 (5 : ZMod 230395727)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (131, 1), (79943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (131, 1), (79943, 1)] : List FactorBlock).map factorBlockValue).prod) = 230395727 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_11
      · exact prime_thirtyNineAK_131
      · exact prime_thirtyNineAK_79943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 230395727) ^ 115197863 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 230395727) ^ 20945066 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 230395727) ^ 1758746 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 230395727) ^ 2882 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_231014083 : Nat.Prime 231014083 := by
  apply lucas_primality 231014083 (3 : ZMod 231014083)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (1303, 1), (2273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (1303, 1), (2273, 1)] : List FactorBlock).map factorBlockValue).prod) = 231014083 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_13
      · exact prime_thirtyNineAK_1303
      · exact prime_thirtyNineAK_2273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 231014083) ^ 115507041 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 231014083) ^ 77004694 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 231014083) ^ 17770314 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 231014083) ^ 177294 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 231014083) ^ 101634 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_291863717 : Nat.Prime 291863717 := by
  apply lucas_primality 291863717 (2 : ZMod 291863717)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1531, 1), (47659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1531, 1), (47659, 1)] : List FactorBlock).map factorBlockValue).prod) = 291863717 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_1531
      · exact prime_thirtyNineAK_47659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 291863717) ^ 145931858 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 291863717) ^ 190636 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 291863717) ^ 6124 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_320879927 : Nat.Prime 320879927 := by
  apply lucas_primality 320879927 (5 : ZMod 320879927)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (160439963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (160439963, 1)] : List FactorBlock).map factorBlockValue).prod) = 320879927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_160439963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 320879927) ^ 160439963 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 320879927) ^ 2 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_360347051 : Nat.Prime 360347051 := by
  apply lucas_primality 360347051 (2 : ZMod 360347051)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (1029563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (1029563, 1)] : List FactorBlock).map factorBlockValue).prod) = 360347051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_1029563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 360347051) ^ 180173525 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 360347051) ^ 72069410 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 360347051) ^ 51478150 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 360347051) ^ 350 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_387194683 : Nat.Prime 387194683 := by
  apply lucas_primality 387194683 (3 : ZMod 387194683)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (523, 1), (17627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (523, 1), (17627, 1)] : List FactorBlock).map factorBlockValue).prod) = 387194683 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_523
      · exact prime_thirtyNineAK_17627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 387194683) ^ 193597341 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 387194683) ^ 129064894 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 387194683) ^ 55313526 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 387194683) ^ 740334 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 387194683) ^ 21966 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_429845593 : Nat.Prime 429845593 := by
  apply lucas_primality 429845593 (5 : ZMod 429845593)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (1628203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (1628203, 1)] : List FactorBlock).map factorBlockValue).prod) = 429845593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_11
      · exact prime_thirtyNineAK_1628203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 429845593) ^ 214922796 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 429845593) ^ 143281864 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 429845593) ^ 39076872 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 429845593) ^ 264 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_440144753 : Nat.Prime 440144753 := by
  apply lucas_primality 440144753 (3 : ZMod 440144753)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (27509047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (27509047, 1)] : List FactorBlock).map factorBlockValue).prod) = 440144753 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_27509047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 440144753) ^ 220072376 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 440144753) ^ 16 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_442966529 : Nat.Prime 442966529 := by
  apply lucas_primality 442966529 (3 : ZMod 442966529)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (89, 1), (9721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (89, 1), (9721, 1)] : List FactorBlock).map factorBlockValue).prod) = 442966529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_89
      · exact prime_thirtyNineAK_9721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 442966529) ^ 221483264 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 442966529) ^ 4977152 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 442966529) ^ 45568 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_481786181 : Nat.Prime 481786181 := by
  apply lucas_primality 481786181 (2 : ZMod 481786181)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (24089309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (24089309, 1)] : List FactorBlock).map factorBlockValue).prod) = 481786181 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_24089309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 481786181) ^ 240893090 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 481786181) ^ 96357236 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 481786181) ^ 20 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_509536337 : Nat.Prime 509536337 := by
  apply lucas_primality 509536337 (3 : ZMod 509536337)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (31, 1), (83, 1), (12377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (31, 1), (83, 1), (12377, 1)] : List FactorBlock).map factorBlockValue).prod) = 509536337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_31
      · exact prime_thirtyNineAK_83
      · exact prime_thirtyNineAK_12377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 509536337) ^ 254768168 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 509536337) ^ 16436656 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 509536337) ^ 6138992 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 509536337) ^ 41168 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_680185699 : Nat.Prime 680185699 := by
  apply lucas_primality 680185699 (2 : ZMod 680185699)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1327, 1), (85429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1327, 1), (85429, 1)] : List FactorBlock).map factorBlockValue).prod) = 680185699 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_1327
      · exact prime_thirtyNineAK_85429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 680185699) ^ 340092849 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 680185699) ^ 226728566 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 680185699) ^ 512574 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 680185699) ^ 7962 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_752335981 : Nat.Prime 752335981 := by
  apply lucas_primality 752335981 (6 : ZMod 752335981)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (23, 1), (29, 1), (1709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (23, 1), (29, 1), (1709, 1)] : List FactorBlock).map factorBlockValue).prod) = 752335981 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_11
      · exact prime_thirtyNineAK_23
      · exact prime_thirtyNineAK_29
      · exact prime_thirtyNineAK_1709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 752335981) ^ 376167990 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (6 : ZMod 752335981) ^ 250778660 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (6 : ZMod 752335981) ^ 150467196 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (6 : ZMod 752335981) ^ 68394180 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (6 : ZMod 752335981) ^ 32710260 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (6 : ZMod 752335981) ^ 25942620 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (6 : ZMod 752335981) ^ 440220 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_758692157 : Nat.Prime 758692157 := by
  apply lucas_primality 758692157 (2 : ZMod 758692157)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (189673039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (189673039, 1)] : List FactorBlock).map factorBlockValue).prod) = 758692157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_189673039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 758692157) ^ 379346078 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 758692157) ^ 4 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_909764209 : Nat.Prime 909764209 := by
  apply lucas_primality 909764209 (11 : ZMod 909764209)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (6317807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (6317807, 1)] : List FactorBlock).map factorBlockValue).prod) = 909764209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_6317807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 909764209) ^ 454882104 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (11 : ZMod 909764209) ^ 303254736 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (11 : ZMod 909764209) ^ 144 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_910838081 : Nat.Prime 910838081 := by
  apply lucas_primality 910838081 (3 : ZMod 910838081)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (173, 1), (16453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (173, 1), (16453, 1)] : List FactorBlock).map factorBlockValue).prod) = 910838081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_173
      · exact prime_thirtyNineAK_16453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 910838081) ^ 455419040 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 910838081) ^ 182167616 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 910838081) ^ 5264960 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 910838081) ^ 55360 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_918428923 : Nat.Prime 918428923 := by
  apply lucas_primality 918428923 (2 : ZMod 918428923)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (17007943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (17007943, 1)] : List FactorBlock).map factorBlockValue).prod) = 918428923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_17007943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 918428923) ^ 459214461 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 918428923) ^ 306142974 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 918428923) ^ 54 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_974854703 : Nat.Prime 974854703 := by
  apply lucas_primality 974854703 (5 : ZMod 974854703)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (6677087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (6677087, 1)] : List FactorBlock).map factorBlockValue).prod) = 974854703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_73
      · exact prime_thirtyNineAK_6677087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 974854703) ^ 487427351 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 974854703) ^ 13354174 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 974854703) ^ 146 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_1095294437 : Nat.Prime 1095294437 := by
  apply lucas_primality 1095294437 (2 : ZMod 1095294437)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3583, 1), (76423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3583, 1), (76423, 1)] : List FactorBlock).map factorBlockValue).prod) = 1095294437 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3583
      · exact prime_thirtyNineAK_76423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1095294437) ^ 547647218 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1095294437) ^ 305692 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1095294437) ^ 14332 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_1160494157 : Nat.Prime 1160494157 := by
  apply lucas_primality 1160494157 (2 : ZMod 1160494157)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (521, 1), (556859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (521, 1), (556859, 1)] : List FactorBlock).map factorBlockValue).prod) = 1160494157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_521
      · exact prime_thirtyNineAK_556859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1160494157) ^ 580247078 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1160494157) ^ 2227436 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1160494157) ^ 2084 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_1160978177 : Nat.Prime 1160978177 := by
  apply lucas_primality 1160978177 (5 : ZMod 1160978177)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (23, 1), (269, 1), (733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (23, 1), (269, 1), (733, 1)] : List FactorBlock).map factorBlockValue).prod) = 1160978177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_23
      · exact prime_thirtyNineAK_269
      · exact prime_thirtyNineAK_733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1160978177) ^ 580489088 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1160978177) ^ 50477312 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1160978177) ^ 4315904 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1160978177) ^ 1583872 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_1222615931 : Nat.Prime 1222615931 := by
  apply lucas_primality 1222615931 (2 : ZMod 1222615931)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) = 1222615931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_29
      · exact prime_thirtyNineAK_113
      · exact prime_thirtyNineAK_37309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1222615931) ^ 611307965 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 244523186 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 42159170 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 10819610 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 32770 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_1275617569 : Nat.Prime 1275617569 := by
  apply lucas_primality 1275617569 (13 : ZMod 1275617569)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (53, 1), (239, 1), (1049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (53, 1), (239, 1), (1049, 1)] : List FactorBlock).map factorBlockValue).prod) = 1275617569 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_53
      · exact prime_thirtyNineAK_239
      · exact prime_thirtyNineAK_1049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 1275617569) ^ 637808784 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (13 : ZMod 1275617569) ^ 425205856 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (13 : ZMod 1275617569) ^ 24068256 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (13 : ZMod 1275617569) ^ 5337312 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (13 : ZMod 1275617569) ^ 1216032 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_1307287211 : Nat.Prime 1307287211 := by
  apply lucas_primality 1307287211 (2 : ZMod 1307287211)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (887, 1), (7757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (887, 1), (7757, 1)] : List FactorBlock).map factorBlockValue).prod) = 1307287211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_19
      · exact prime_thirtyNineAK_887
      · exact prime_thirtyNineAK_7757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1307287211) ^ 653643605 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1307287211) ^ 261457442 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1307287211) ^ 68804590 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1307287211) ^ 1473830 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1307287211) ^ 168530 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_1317915923 : Nat.Prime 1317915923 := by
  apply lucas_primality 1317915923 (2 : ZMod 1317915923)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (59, 1), (313, 1), (2099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (59, 1), (313, 1), (2099, 1)] : List FactorBlock).map factorBlockValue).prod) = 1317915923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_17
      · exact prime_thirtyNineAK_59
      · exact prime_thirtyNineAK_313
      · exact prime_thirtyNineAK_2099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1317915923) ^ 658957961 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1317915923) ^ 77524466 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1317915923) ^ 22337558 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1317915923) ^ 4210594 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1317915923) ^ 627878 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_1474306679 : Nat.Prime 1474306679 := by
  apply lucas_primality 1474306679 (17 : ZMod 1474306679)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (127, 1), (457, 1), (977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (127, 1), (457, 1), (977, 1)] : List FactorBlock).map factorBlockValue).prod) = 1474306679 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_13
      · exact prime_thirtyNineAK_127
      · exact prime_thirtyNineAK_457
      · exact prime_thirtyNineAK_977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 1474306679) ^ 737153339 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (17 : ZMod 1474306679) ^ 113408206 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (17 : ZMod 1474306679) ^ 11608714 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (17 : ZMod 1474306679) ^ 3226054 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (17 : ZMod 1474306679) ^ 1509014 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_1747878553 : Nat.Prime 1747878553 := by
  apply lucas_primality 1747878553 (10 : ZMod 1747878553)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (19, 1), (349, 1), (523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (19, 1), (349, 1), (523, 1)] : List FactorBlock).map factorBlockValue).prod) = 1747878553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_19
      · exact prime_thirtyNineAK_349
      · exact prime_thirtyNineAK_523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1747878553) ^ 873939276 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (10 : ZMod 1747878553) ^ 582626184 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (10 : ZMod 1747878553) ^ 249696936 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (10 : ZMod 1747878553) ^ 91993608 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (10 : ZMod 1747878553) ^ 5008248 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (10 : ZMod 1747878553) ^ 3342024 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_2531601659 : Nat.Prime 2531601659 := by
  apply lucas_primality 2531601659 (2 : ZMod 2531601659)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (383, 1), (3304963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (383, 1), (3304963, 1)] : List FactorBlock).map factorBlockValue).prod) = 2531601659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_383
      · exact prime_thirtyNineAK_3304963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2531601659) ^ 1265800829 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2531601659) ^ 6609926 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2531601659) ^ 766 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_3540386347 : Nat.Prime 3540386347 := by
  apply lucas_primality 3540386347 (11 : ZMod 3540386347)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (84294913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (84294913, 1)] : List FactorBlock).map factorBlockValue).prod) = 3540386347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_84294913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 3540386347) ^ 1770193173 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 1180128782 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 505769478 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 42 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_3810125287 : Nat.Prime 3810125287 := by
  apply lucas_primality 3810125287 (3 : ZMod 3810125287)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (79, 1), (243583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (79, 1), (243583, 1)] : List FactorBlock).map factorBlockValue).prod) = 3810125287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_11
      · exact prime_thirtyNineAK_79
      · exact prime_thirtyNineAK_243583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3810125287) ^ 1905062643 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3810125287) ^ 1270041762 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3810125287) ^ 346375026 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3810125287) ^ 48229434 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3810125287) ^ 15642 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_4113109993 : Nat.Prime 4113109993 := by
  apply lucas_primality 4113109993 (5 : ZMod 4113109993)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7177, 1), (23879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7177, 1), (23879, 1)] : List FactorBlock).map factorBlockValue).prod) = 4113109993 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_7177
      · exact prime_thirtyNineAK_23879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4113109993) ^ 2056554996 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 4113109993) ^ 1371036664 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 4113109993) ^ 573096 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 4113109993) ^ 172248 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_4499780951 : Nat.Prime 4499780951 := by
  apply lucas_primality 4499780951 (7 : ZMod 4499780951)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (23, 1), (558979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (23, 1), (558979, 1)] : List FactorBlock).map factorBlockValue).prod) = 4499780951 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_23
      · exact prime_thirtyNineAK_558979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4499780951) ^ 2249890475 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 4499780951) ^ 899956190 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 4499780951) ^ 642825850 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 4499780951) ^ 195642650 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 4499780951) ^ 8050 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_4598633189 : Nat.Prime 4598633189 := by
  apply lucas_primality 4598633189 (2 : ZMod 4598633189)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (139, 1), (8270923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (139, 1), (8270923, 1)] : List FactorBlock).map factorBlockValue).prod) = 4598633189 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_139
      · exact prime_thirtyNineAK_8270923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4598633189) ^ 2299316594 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4598633189) ^ 33083692 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4598633189) ^ 556 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_4644344281 : Nat.Prime 4644344281 := by
  apply lucas_primality 4644344281 (7 : ZMod 4644344281)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (127, 1), (193, 1), (1579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (127, 1), (193, 1), (1579, 1)] : List FactorBlock).map factorBlockValue).prod) = 4644344281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_127
      · exact prime_thirtyNineAK_193
      · exact prime_thirtyNineAK_1579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4644344281) ^ 2322172140 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 4644344281) ^ 1548114760 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 4644344281) ^ 928868856 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 4644344281) ^ 36569640 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 4644344281) ^ 24063960 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 4644344281) ^ 2941320 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_5327453741 : Nat.Prime 5327453741 := by
  apply lucas_primality 5327453741 (2 : ZMod 5327453741)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (499, 1), (76259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (499, 1), (76259, 1)] : List FactorBlock).map factorBlockValue).prod) = 5327453741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_499
      · exact prime_thirtyNineAK_76259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5327453741) ^ 2663726870 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5327453741) ^ 1065490748 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5327453741) ^ 761064820 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5327453741) ^ 10676260 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5327453741) ^ 69860 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_5834431507 : Nat.Prime 5834431507 := by
  apply lucas_primality 5834431507 (2 : ZMod 5834431507)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (26281223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (26281223, 1)] : List FactorBlock).map factorBlockValue).prod) = 5834431507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_37
      · exact prime_thirtyNineAK_26281223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5834431507) ^ 2917215753 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5834431507) ^ 1944810502 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5834431507) ^ 157687338 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5834431507) ^ 222 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_6071280701 : Nat.Prime 6071280701 := by
  apply lucas_primality 6071280701 (2 : ZMod 6071280701)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (60712807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (60712807, 1)] : List FactorBlock).map factorBlockValue).prod) = 6071280701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_60712807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6071280701) ^ 3035640350 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6071280701) ^ 1214256140 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6071280701) ^ 100 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_6391408799 : Nat.Prime 6391408799 := by
  apply lucas_primality 6391408799 (23 : ZMod 6391408799)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (223, 1), (161017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (223, 1), (161017, 1)] : List FactorBlock).map factorBlockValue).prod) = 6391408799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_89
      · exact prime_thirtyNineAK_223
      · exact prime_thirtyNineAK_161017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 6391408799) ^ 3195704399 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 71813582 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 28661026 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 39694 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_8155417087 : Nat.Prime 8155417087 := by
  apply lucas_primality 8155417087 (3 : ZMod 8155417087)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (37, 1), (12245371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (37, 1), (12245371, 1)] : List FactorBlock).map factorBlockValue).prod) = 8155417087 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_37
      · exact prime_thirtyNineAK_12245371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8155417087) ^ 4077708543 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 8155417087) ^ 2718472362 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 8155417087) ^ 220416678 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 8155417087) ^ 666 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_8637501007 : Nat.Prime 8637501007 := by
  apply lucas_primality 8637501007 (3 : ZMod 8637501007)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (23, 1), (113, 1), (184633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (23, 1), (113, 1), (184633, 1)] : List FactorBlock).map factorBlockValue).prod) = 8637501007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_23
      · exact prime_thirtyNineAK_113
      · exact prime_thirtyNineAK_184633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8637501007) ^ 4318750503 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 8637501007) ^ 2879167002 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 8637501007) ^ 375543522 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 8637501007) ^ 76438062 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 8637501007) ^ 46782 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_9277522589 : Nat.Prime 9277522589 := by
  apply lucas_primality 9277522589 (2 : ZMod 9277522589)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (53, 1), (1509031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (53, 1), (1509031, 1)] : List FactorBlock).map factorBlockValue).prod) = 9277522589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_29
      · exact prime_thirtyNineAK_53
      · exact prime_thirtyNineAK_1509031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9277522589) ^ 4638761294 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 319914572 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 175047596 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 6148 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_9292672393 : Nat.Prime 9292672393 := by
  apply lucas_primality 9292672393 (10 : ZMod 9292672393)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (387194683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (387194683, 1)] : List FactorBlock).map factorBlockValue).prod) = 9292672393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_387194683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 9292672393) ^ 4646336196 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (10 : ZMod 9292672393) ^ 3097557464 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (10 : ZMod 9292672393) ^ 24 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_9316388509 : Nat.Prime 9316388509 := by
  apply lucas_primality 9316388509 (2 : ZMod 9316388509)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (37, 1), (41, 1), (113, 1), (647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (37, 1), (41, 1), (113, 1), (647, 1)] : List FactorBlock).map factorBlockValue).prod) = 9316388509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_37
      · exact prime_thirtyNineAK_41
      · exact prime_thirtyNineAK_113
      · exact prime_thirtyNineAK_647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9316388509) ^ 4658194254 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 9316388509) ^ 3105462836 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 9316388509) ^ 1330912644 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 9316388509) ^ 251794284 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 9316388509) ^ 227228988 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 9316388509) ^ 82445916 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 9316388509) ^ 14399364 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_9456603047 : Nat.Prime 9456603047 := by
  apply lucas_primality 9456603047 (5 : ZMod 9456603047)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (429845593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (429845593, 1)] : List FactorBlock).map factorBlockValue).prod) = 9456603047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_11
      · exact prime_thirtyNineAK_429845593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 9456603047) ^ 4728301523 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 9456603047) ^ 859691186 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 9456603047) ^ 22 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_9975615259 : Nat.Prime 9975615259 := by
  apply lucas_primality 9975615259 (2 : ZMod 9975615259)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (19, 1), (1663, 1), (7517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (19, 1), (1663, 1), (7517, 1)] : List FactorBlock).map factorBlockValue).prod) = 9975615259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_19
      · exact prime_thirtyNineAK_1663
      · exact prime_thirtyNineAK_7517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9975615259) ^ 4987807629 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 9975615259) ^ 3325205086 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 9975615259) ^ 1425087894 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 9975615259) ^ 525032382 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 9975615259) ^ 5998566 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 9975615259) ^ 1327074 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_11928834361 : Nat.Prime 11928834361 := by
  apply lucas_primality 11928834361 (7 : ZMod 11928834361)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (5, 1), (211, 1), (17449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (5, 1), (211, 1), (17449, 1)] : List FactorBlock).map factorBlockValue).prod) = 11928834361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_211
      · exact prime_thirtyNineAK_17449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 11928834361) ^ 5964417180 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 11928834361) ^ 3976278120 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 11928834361) ^ 2385766872 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 11928834361) ^ 56534760 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 11928834361) ^ 683640 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_13001360959 : Nat.Prime 13001360959 := by
  apply lucas_primality 13001360959 (3 : ZMod 13001360959)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (37, 1), (229, 1), (85247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (37, 1), (229, 1), (85247, 1)] : List FactorBlock).map factorBlockValue).prod) = 13001360959 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_37
      · exact prime_thirtyNineAK_229
      · exact prime_thirtyNineAK_85247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13001360959) ^ 6500680479 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 13001360959) ^ 4333786986 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 13001360959) ^ 351388134 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 13001360959) ^ 56774502 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 13001360959) ^ 152514 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_15334122119 : Nat.Prime 15334122119 := by
  apply lucas_primality 15334122119 (7 : ZMod 15334122119)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1095294437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1095294437, 1)] : List FactorBlock).map factorBlockValue).prod) = 15334122119 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_1095294437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 15334122119) ^ 7667061059 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 15334122119) ^ 2190588874 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 15334122119) ^ 14 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_19167809209 : Nat.Prime 19167809209 := by
  apply lucas_primality 19167809209 (7 : ZMod 19167809209)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (3011, 1), (265247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (3011, 1), (265247, 1)] : List FactorBlock).map factorBlockValue).prod) = 19167809209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_3011
      · exact prime_thirtyNineAK_265247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 19167809209) ^ 9583904604 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 19167809209) ^ 6389269736 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 19167809209) ^ 6365928 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 19167809209) ^ 72264 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_19514955419 : Nat.Prime 19514955419 := by
  apply lucas_primality 19514955419 (2 : ZMod 19514955419)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 1), (53, 1), (89, 1), (17383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 1), (53, 1), (89, 1), (17383, 1)] : List FactorBlock).map factorBlockValue).prod) = 19514955419 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_17
      · exact prime_thirtyNineAK_53
      · exact prime_thirtyNineAK_89
      · exact prime_thirtyNineAK_17383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 19514955419) ^ 9757477709 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 19514955419) ^ 2787850774 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 19514955419) ^ 1147938554 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 19514955419) ^ 368206706 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 19514955419) ^ 219269162 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 19514955419) ^ 1122646 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_19900204619 : Nat.Prime 19900204619 := by
  apply lucas_primality 19900204619 (2 : ZMod 19900204619)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (4243, 1), (335009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (4243, 1), (335009, 1)] : List FactorBlock).map factorBlockValue).prod) = 19900204619 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_4243
      · exact prime_thirtyNineAK_335009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 19900204619) ^ 9950102309 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 19900204619) ^ 2842886374 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 19900204619) ^ 4690126 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 19900204619) ^ 59402 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_29486133581 : Nat.Prime 29486133581 := by
  apply lucas_primality 29486133581 (2 : ZMod 29486133581)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1474306679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1474306679, 1)] : List FactorBlock).map factorBlockValue).prod) = 29486133581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_1474306679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 29486133581) ^ 14743066790 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 29486133581) ^ 5897226716 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 29486133581) ^ 20 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_29572479331 : Nat.Prime 29572479331 := by
  apply lucas_primality 29572479331 (2 : ZMod 29572479331)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1217, 1), (809983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1217, 1), (809983, 1)] : List FactorBlock).map factorBlockValue).prod) = 29572479331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_1217
      · exact prime_thirtyNineAK_809983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 29572479331) ^ 14786239665 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 29572479331) ^ 9857493110 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 29572479331) ^ 5914495866 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 29572479331) ^ 24299490 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 29572479331) ^ 36510 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_30429025931 : Nat.Prime 30429025931 := by
  apply lucas_primality 30429025931 (2 : ZMod 30429025931)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (71, 1), (42857783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (71, 1), (42857783, 1)] : List FactorBlock).map factorBlockValue).prod) = 30429025931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_71
      · exact prime_thirtyNineAK_42857783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 30429025931) ^ 15214512965 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 6085805186 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 428577830 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 710 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_31255102133 : Nat.Prime 31255102133 := by
  apply lucas_primality 31255102133 (2 : ZMod 31255102133)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (73, 1), (4653827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (73, 1), (4653827, 1)] : List FactorBlock).map factorBlockValue).prod) = 31255102133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_23
      · exact prime_thirtyNineAK_73
      · exact prime_thirtyNineAK_4653827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 31255102133) ^ 15627551066 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 31255102133) ^ 1358917484 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 31255102133) ^ 428152084 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 31255102133) ^ 6716 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_34020590371 : Nat.Prime 34020590371 := by
  apply lucas_primality 34020590371 (2 : ZMod 34020590371)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (167, 1), (229, 1), (2281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (167, 1), (229, 1), (2281, 1)] : List FactorBlock).map factorBlockValue).prod) = 34020590371 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_13
      · exact prime_thirtyNineAK_167
      · exact prime_thirtyNineAK_229
      · exact prime_thirtyNineAK_2281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 34020590371) ^ 17010295185 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 34020590371) ^ 11340196790 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 34020590371) ^ 6804118074 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 34020590371) ^ 2616968490 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 34020590371) ^ 203716110 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 34020590371) ^ 148561530 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 34020590371) ^ 14914770 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_37836611801 : Nat.Prime 37836611801 := by
  apply lucas_primality 37836611801 (3 : ZMod 37836611801)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (13, 1), (3137, 1), (4639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (13, 1), (3137, 1), (4639, 1)] : List FactorBlock).map factorBlockValue).prod) = 37836611801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_13
      · exact prime_thirtyNineAK_3137
      · exact prime_thirtyNineAK_4639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 37836611801) ^ 18918305900 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 37836611801) ^ 7567322360 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 37836611801) ^ 2910508600 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 37836611801) ^ 12061400 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 37836611801) ^ 8156200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_45520224601 : Nat.Prime 45520224601 := by
  apply lucas_primality 45520224601 (13 : ZMod 45520224601)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (23, 1), (241, 1), (13687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (23, 1), (241, 1), (13687, 1)] : List FactorBlock).map factorBlockValue).prod) = 45520224601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_23
      · exact prime_thirtyNineAK_241
      · exact prime_thirtyNineAK_13687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 45520224601) ^ 22760112300 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (13 : ZMod 45520224601) ^ 15173408200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (13 : ZMod 45520224601) ^ 9104044920 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (13 : ZMod 45520224601) ^ 1979140200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (13 : ZMod 45520224601) ^ 188880600 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (13 : ZMod 45520224601) ^ 3325800 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_48559520011 : Nat.Prime 48559520011 := by
  apply lucas_primality 48559520011 (2 : ZMod 48559520011)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (8933, 1), (181199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (8933, 1), (181199, 1)] : List FactorBlock).map factorBlockValue).prod) = 48559520011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_8933
      · exact prime_thirtyNineAK_181199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 48559520011) ^ 24279760005 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 48559520011) ^ 16186506670 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 48559520011) ^ 9711904002 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 48559520011) ^ 5435970 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 48559520011) ^ 267990 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_72863556869 : Nat.Prime 72863556869 := by
  apply lucas_primality 72863556869 (2 : ZMod 72863556869)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (73, 1), (5309207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (73, 1), (5309207, 1)] : List FactorBlock).map factorBlockValue).prod) = 72863556869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_47
      · exact prime_thirtyNineAK_73
      · exact prime_thirtyNineAK_5309207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 72863556869) ^ 36431778434 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 72863556869) ^ 1550288444 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 72863556869) ^ 998130916 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 72863556869) ^ 13724 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_75504561983 : Nat.Prime 75504561983 := by
  apply lucas_primality 75504561983 (5 : ZMod 75504561983)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1741, 1), (4003, 1), (5417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1741, 1), (4003, 1), (5417, 1)] : List FactorBlock).map factorBlockValue).prod) = 75504561983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_1741
      · exact prime_thirtyNineAK_4003
      · exact prime_thirtyNineAK_5417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 75504561983) ^ 37752280991 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 75504561983) ^ 43368502 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 75504561983) ^ 18861994 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 75504561983) ^ 13938446 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_104941231333 : Nat.Prime 104941231333 := by
  apply lucas_primality 104941231333 (2 : ZMod 104941231333)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (47, 1), (311, 1), (85469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (47, 1), (311, 1), (85469, 1)] : List FactorBlock).map factorBlockValue).prod) = 104941231333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_47
      · exact prime_thirtyNineAK_311
      · exact prime_thirtyNineAK_85469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 104941231333) ^ 52470615666 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 104941231333) ^ 34980410444 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 104941231333) ^ 14991604476 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 104941231333) ^ 2232792156 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 104941231333) ^ 337431612 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 104941231333) ^ 1227828 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_106168510121 : Nat.Prime 106168510121 := by
  apply lucas_primality 106168510121 (6 : ZMod 106168510121)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (271, 1), (9794143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (271, 1), (9794143, 1)] : List FactorBlock).map factorBlockValue).prod) = 106168510121 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_271
      · exact prime_thirtyNineAK_9794143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 106168510121) ^ 53084255060 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (6 : ZMod 106168510121) ^ 21233702024 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (6 : ZMod 106168510121) ^ 391765720 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (6 : ZMod 106168510121) ^ 10840 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_113743851409 : Nat.Prime 113743851409 := by
  apply lucas_primality 113743851409 (7 : ZMod 113743851409)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (11, 1), (67, 1), (1071761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (11, 1), (67, 1), (1071761, 1)] : List FactorBlock).map factorBlockValue).prod) = 113743851409 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_11
      · exact prime_thirtyNineAK_67
      · exact prime_thirtyNineAK_1071761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 113743851409) ^ 56871925704 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 113743851409) ^ 37914617136 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 113743851409) ^ 10340350128 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 113743851409) ^ 1697669424 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 113743851409) ^ 106128 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_147041875891 : Nat.Prime 147041875891 := by
  apply lucas_primality 147041875891 (10 : ZMod 147041875891)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 2), (13, 1), (787, 1), (3259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 2), (13, 1), (787, 1), (3259, 1)] : List FactorBlock).map factorBlockValue).prod) = 147041875891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_13
      · exact prime_thirtyNineAK_787
      · exact prime_thirtyNineAK_3259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 147041875891) ^ 73520937945 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (10 : ZMod 147041875891) ^ 49013958630 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (10 : ZMod 147041875891) ^ 29408375178 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (10 : ZMod 147041875891) ^ 21005982270 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (10 : ZMod 147041875891) ^ 11310913530 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (10 : ZMod 147041875891) ^ 186838470 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (10 : ZMod 147041875891) ^ 45118710 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_155493355051 : Nat.Prime 155493355051 := by
  apply lucas_primality 155493355051 (3 : ZMod 155493355051)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (5, 2), (11, 2), (105767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (5, 2), (11, 2), (105767, 1)] : List FactorBlock).map factorBlockValue).prod) = 155493355051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_11
      · exact prime_thirtyNineAK_105767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 155493355051) ^ 77746677525 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 155493355051) ^ 51831118350 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 155493355051) ^ 31098671010 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 155493355051) ^ 14135759550 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 155493355051) ^ 1470150 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_187530612799 : Nat.Prime 187530612799 := by
  apply lucas_primality 187530612799 (6 : ZMod 187530612799)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31255102133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31255102133, 1)] : List FactorBlock).map factorBlockValue).prod) = 187530612799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_31255102133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 187530612799) ^ 93765306399 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (6 : ZMod 187530612799) ^ 62510204266 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (6 : ZMod 187530612799) ^ 6 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_212140652989 : Nat.Prime 212140652989 := by
  apply lucas_primality 212140652989 (2 : ZMod 212140652989)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (41, 1), (39198199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (41, 1), (39198199, 1)] : List FactorBlock).map factorBlockValue).prod) = 212140652989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_11
      · exact prime_thirtyNineAK_41
      · exact prime_thirtyNineAK_39198199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 212140652989) ^ 106070326494 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 212140652989) ^ 70713550996 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 212140652989) ^ 19285513908 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 212140652989) ^ 5174162268 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 212140652989) ^ 5412 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_213502379527 : Nat.Prime 213502379527 := by
  apply lucas_primality 213502379527 (3 : ZMod 213502379527)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (1317915923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (1317915923, 1)] : List FactorBlock).map factorBlockValue).prod) = 213502379527 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_1317915923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 213502379527) ^ 106751189763 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 213502379527) ^ 71167459842 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 213502379527) ^ 162 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_268040606881 : Nat.Prime 268040606881 := by
  apply lucas_primality 268040606881 (7 : ZMod 268040606881)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (1609, 1), (347059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (1609, 1), (347059, 1)] : List FactorBlock).map factorBlockValue).prod) = 268040606881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_1609
      · exact prime_thirtyNineAK_347059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 268040606881) ^ 134020303440 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 268040606881) ^ 89346868960 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 268040606881) ^ 53608121376 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 268040606881) ^ 166588320 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 268040606881) ^ 772320 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_277508030299 : Nat.Prime 277508030299 := by
  apply lucas_primality 277508030299 (3 : ZMod 277508030299)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (149, 1), (1429, 1), (217223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (149, 1), (1429, 1), (217223, 1)] : List FactorBlock).map factorBlockValue).prod) = 277508030299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_149
      · exact prime_thirtyNineAK_1429
      · exact prime_thirtyNineAK_217223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 277508030299) ^ 138754015149 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 92502676766 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 1862470002 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 194197362 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 1277526 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_318960960511 : Nat.Prime 318960960511 := by
  apply lucas_primality 318960960511 (17 : ZMod 318960960511)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (9719, 1), (1093943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (9719, 1), (1093943, 1)] : List FactorBlock).map factorBlockValue).prod) = 318960960511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_9719
      · exact prime_thirtyNineAK_1093943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 318960960511) ^ 159480480255 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (17 : ZMod 318960960511) ^ 106320320170 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (17 : ZMod 318960960511) ^ 63792192102 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (17 : ZMod 318960960511) ^ 32818290 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (17 : ZMod 318960960511) ^ 291570 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_364181272591 : Nat.Prime 364181272591 := by
  apply lucas_primality 364181272591 (13 : ZMod 364181272591)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1801, 1), (2131, 1), (3163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1801, 1), (2131, 1), (3163, 1)] : List FactorBlock).map factorBlockValue).prod) = 364181272591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_1801
      · exact prime_thirtyNineAK_2131
      · exact prime_thirtyNineAK_3163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 364181272591) ^ 182090636295 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (13 : ZMod 364181272591) ^ 121393757530 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (13 : ZMod 364181272591) ^ 72836254518 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (13 : ZMod 364181272591) ^ 202210590 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (13 : ZMod 364181272591) ^ 170896890 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (13 : ZMod 364181272591) ^ 115137930 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_375380267527 : Nat.Prime 375380267527 := by
  apply lucas_primality 375380267527 (5 : ZMod 375380267527)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (127, 1), (157, 1), (95083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (127, 1), (157, 1), (95083, 1)] : List FactorBlock).map factorBlockValue).prod) = 375380267527 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_11
      · exact prime_thirtyNineAK_127
      · exact prime_thirtyNineAK_157
      · exact prime_thirtyNineAK_95083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 375380267527) ^ 187690133763 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 375380267527) ^ 125126755842 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 375380267527) ^ 34125478866 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 375380267527) ^ 2955750138 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 375380267527) ^ 2390957118 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 375380267527) ^ 3947922 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_462094662389 : Nat.Prime 462094662389 := by
  apply lucas_primality 462094662389 (2 : ZMod 462094662389)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) = 462094662389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_17
      · exact prime_thirtyNineAK_397
      · exact prime_thirtyNineAK_2531
      · exact prime_thirtyNineAK_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 462094662389) ^ 231047331194 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 27182038964 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 1163966404 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 182573948 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 68326876 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_625380452107 : Nat.Prime 625380452107 := by
  apply lucas_primality 625380452107 (2 : ZMod 625380452107)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (653, 1), (9389251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (653, 1), (9389251, 1)] : List FactorBlock).map factorBlockValue).prod) = 625380452107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_17
      · exact prime_thirtyNineAK_653
      · exact prime_thirtyNineAK_9389251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 625380452107) ^ 312690226053 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 625380452107) ^ 208460150702 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 625380452107) ^ 36787085418 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 625380452107) ^ 957703602 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 625380452107) ^ 66606 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_906007626637 : Nat.Prime 906007626637 := by
  apply lucas_primality 906007626637 (2 : ZMod 906007626637)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 3), (220118471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 3), (220118471, 1)] : List FactorBlock).map factorBlockValue).prod) = 906007626637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_220118471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 906007626637) ^ 453003813318 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 906007626637) ^ 302002542212 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 906007626637) ^ 129429660948 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 906007626637) ^ 4116 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_964862349257 : Nat.Prime 964862349257 := by
  apply lucas_primality 964862349257 (5 : ZMod 964862349257)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (9277522589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (9277522589, 1)] : List FactorBlock).map factorBlockValue).prod) = 964862349257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_13
      · exact prime_thirtyNineAK_9277522589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 964862349257) ^ 482431174628 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 964862349257) ^ 74220180712 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 964862349257) ^ 104 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_1357820525291 : Nat.Prime 1357820525291 := by
  apply lucas_primality 1357820525291 (2 : ZMod 1357820525291)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (12391, 1), (10958119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (12391, 1), (10958119, 1)] : List FactorBlock).map factorBlockValue).prod) = 1357820525291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_12391
      · exact prime_thirtyNineAK_10958119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1357820525291) ^ 678910262645 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1357820525291) ^ 271564105058 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1357820525291) ^ 109581190 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1357820525291) ^ 123910 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_35279
      · exact prime_thirtyNineAK_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_1820808984041 : Nat.Prime 1820808984041 := by
  apply lucas_primality 1820808984041 (3 : ZMod 1820808984041)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (45520224601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (45520224601, 1)] : List FactorBlock).map factorBlockValue).prod) = 1820808984041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_45520224601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1820808984041) ^ 910404492020 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1820808984041) ^ 364161796808 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1820808984041) ^ 40 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_2715641050583 : Nat.Prime 2715641050583 := by
  apply lucas_primality 2715641050583 (5 : ZMod 2715641050583)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1357820525291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1357820525291, 1)] : List FactorBlock).map factorBlockValue).prod) = 2715641050583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_1357820525291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 2715641050583) ^ 1357820525291 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 2715641050583) ^ 2 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_3272997965299 : Nat.Prime 3272997965299 := by
  apply lucas_primality 3272997965299 (2 : ZMod 3272997965299)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (719, 1), (758692157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (719, 1), (758692157, 1)] : List FactorBlock).map factorBlockValue).prod) = 3272997965299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_719
      · exact prime_thirtyNineAK_758692157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3272997965299) ^ 1636498982649 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3272997965299) ^ 1090999321766 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3272997965299) ^ 4552152942 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3272997965299) ^ 4314 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_5254059754157 : Nat.Prime 5254059754157 := by
  apply lucas_primality 5254059754157 (2 : ZMod 5254059754157)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (276557, 1), (4749527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (276557, 1), (4749527, 1)] : List FactorBlock).map factorBlockValue).prod) = 5254059754157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_276557
      · exact prime_thirtyNineAK_4749527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5254059754157) ^ 2627029877078 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5254059754157) ^ 18998108 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5254059754157) ^ 1106228 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_5452977238001 : Nat.Prime 5452977238001 := by
  apply lucas_primality 5452977238001 (3 : ZMod 5452977238001)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 3), (19, 1), (3877, 1), (37013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 3), (19, 1), (3877, 1), (37013, 1)] : List FactorBlock).map factorBlockValue).prod) = 5452977238001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_19
      · exact prime_thirtyNineAK_3877
      · exact prime_thirtyNineAK_37013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5452977238001) ^ 2726488619000 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5452977238001) ^ 1090595447600 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5452977238001) ^ 286998802000 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5452977238001) ^ 1406494000 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5452977238001) ^ 147326000 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_10935886832407 : Nat.Prime 10935886832407 := by
  apply lucas_primality 10935886832407 (5 : ZMod 10935886832407)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (547, 1), (691, 1), (1607371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (547, 1), (691, 1), (1607371, 1)] : List FactorBlock).map factorBlockValue).prod) = 10935886832407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_547
      · exact prime_thirtyNineAK_691
      · exact prime_thirtyNineAK_1607371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 10935886832407) ^ 5467943416203 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 10935886832407) ^ 3645295610802 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 10935886832407) ^ 19992480498 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 10935886832407) ^ 15826174866 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 10935886832407) ^ 6803586 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_11888851128907 : Nat.Prime 11888851128907 := by
  apply lucas_primality 11888851128907 (3 : ZMod 11888851128907)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (89, 1), (3041, 1), (318313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (89, 1), (3041, 1), (318313, 1)] : List FactorBlock).map factorBlockValue).prod) = 11888851128907 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_23
      · exact prime_thirtyNineAK_89
      · exact prime_thirtyNineAK_3041
      · exact prime_thirtyNineAK_318313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11888851128907) ^ 5944425564453 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 11888851128907) ^ 3962950376302 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 11888851128907) ^ 516906570822 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 11888851128907) ^ 133582596954 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 11888851128907) ^ 3909520266 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 11888851128907) ^ 37349562 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_18757992323353 : Nat.Prime 18757992323353 := by
  apply lucas_primality 18757992323353 (5 : ZMod 18757992323353)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (37, 1), (918428923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (37, 1), (918428923, 1)] : List FactorBlock).map factorBlockValue).prod) = 18757992323353 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_23
      · exact prime_thirtyNineAK_37
      · exact prime_thirtyNineAK_918428923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 18757992323353) ^ 9378996161676 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 18757992323353) ^ 6252664107784 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 18757992323353) ^ 815564883624 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 18757992323353) ^ 506972765496 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 18757992323353) ^ 20424 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_20592344991601 : Nat.Prime 20592344991601 := by
  apply lucas_primality 20592344991601 (13 : ZMod 20592344991601)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 2), (9241, 1), (618991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 2), (9241, 1), (618991, 1)] : List FactorBlock).map factorBlockValue).prod) = 20592344991601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_9241
      · exact prime_thirtyNineAK_618991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 20592344991601) ^ 10296172495800 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (13 : ZMod 20592344991601) ^ 6864114997200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (13 : ZMod 20592344991601) ^ 4118468998320 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (13 : ZMod 20592344991601) ^ 2228367600 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (13 : ZMod 20592344991601) ^ 33267600 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_23969429172811 : Nat.Prime 23969429172811 := by
  apply lucas_primality 23969429172811 (3 : ZMod 23969429172811)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (11, 1), (17, 2), (23, 1), (1214159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (11, 1), (17, 2), (23, 1), (1214159, 1)] : List FactorBlock).map factorBlockValue).prod) = 23969429172811 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_11
      · exact prime_thirtyNineAK_17
      · exact prime_thirtyNineAK_23
      · exact prime_thirtyNineAK_1214159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 23969429172811) ^ 11984714586405 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 23969429172811) ^ 7989809724270 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 23969429172811) ^ 4793885834562 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 23969429172811) ^ 2179039015710 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 23969429172811) ^ 1409966421930 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 23969429172811) ^ 1042149094470 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 23969429172811) ^ 19741590 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_24705200084659 : Nat.Prime 24705200084659 := by
  apply lucas_primality 24705200084659 (2 : ZMod 24705200084659)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (229, 1), (12569, 1), (1430543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (229, 1), (12569, 1), (1430543, 1)] : List FactorBlock).map factorBlockValue).prod) = 24705200084659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_229
      · exact prime_thirtyNineAK_12569
      · exact prime_thirtyNineAK_1430543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24705200084659) ^ 12352600042329 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 24705200084659) ^ 8235066694886 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 24705200084659) ^ 107882969802 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 24705200084659) ^ 1965566082 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 24705200084659) ^ 17269806 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_27988803909181 : Nat.Prime 27988803909181 := by
  apply lucas_primality 27988803909181 (2 : ZMod 27988803909181)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (155493355051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (155493355051, 1)] : List FactorBlock).map factorBlockValue).prod) = 27988803909181 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_155493355051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 27988803909181) ^ 13994401954590 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 27988803909181) ^ 9329601303060 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 27988803909181) ^ 5597760781836 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 27988803909181) ^ 180 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_28322570842457 : Nat.Prime 28322570842457 := by
  apply lucas_primality 28322570842457 (5 : ZMod 28322570842457)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (17, 1), (5569, 1), (3399569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (17, 1), (5569, 1), (3399569, 1)] : List FactorBlock).map factorBlockValue).prod) = 28322570842457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_11
      · exact prime_thirtyNineAK_17
      · exact prime_thirtyNineAK_5569
      · exact prime_thirtyNineAK_3399569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 28322570842457) ^ 14161285421228 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 28322570842457) ^ 2574779167496 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 28322570842457) ^ 1666033578968 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 28322570842457) ^ 5085755224 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 28322570842457) ^ 8331224 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_37050550126357 : Nat.Prime 37050550126357 := by
  apply lucas_primality 37050550126357 (2 : ZMod 37050550126357)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (67, 1), (149, 1), (241, 1), (98717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (67, 1), (149, 1), (241, 1), (98717, 1)] : List FactorBlock).map factorBlockValue).prod) = 37050550126357 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_13
      · exact prime_thirtyNineAK_67
      · exact prime_thirtyNineAK_149
      · exact prime_thirtyNineAK_241
      · exact prime_thirtyNineAK_98717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 37050550126357) ^ 18525275063178 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 37050550126357) ^ 12350183375452 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 37050550126357) ^ 2850042317412 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 37050550126357) ^ 552993285468 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 37050550126357) ^ 248661410244 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 37050550126357) ^ 153736722516 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 37050550126357) ^ 375320868 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_38836932723637 : Nat.Prime 38836932723637 := by
  apply lucas_primality 38836932723637 (2 : ZMod 38836932723637)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (83, 1), (631, 1), (971, 1), (2767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (83, 1), (631, 1), (971, 1), (2767, 1)] : List FactorBlock).map factorBlockValue).prod) = 38836932723637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_23
      · exact prime_thirtyNineAK_83
      · exact prime_thirtyNineAK_631
      · exact prime_thirtyNineAK_971
      · exact prime_thirtyNineAK_2767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 38836932723637) ^ 19418466361818 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 38836932723637) ^ 12945644241212 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 38836932723637) ^ 1688562292332 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 38836932723637) ^ 467914852092 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 38836932723637) ^ 61548229356 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 38836932723637) ^ 39996841116 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 38836932723637) ^ 14035754508 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_46954750354909 : Nat.Prime 46954750354909 := by
  apply lucas_primality 46954750354909 (2 : ZMod 46954750354909)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (17, 1), (23, 1), (909764209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (17, 1), (23, 1), (909764209, 1)] : List FactorBlock).map factorBlockValue).prod) = 46954750354909 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_11
      · exact prime_thirtyNineAK_17
      · exact prime_thirtyNineAK_23
      · exact prime_thirtyNineAK_909764209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 46954750354909) ^ 23477375177454 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 46954750354909) ^ 15651583451636 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 46954750354909) ^ 4268613668628 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 46954750354909) ^ 2762044138524 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 46954750354909) ^ 2041510884996 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 46954750354909) ^ 51612 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_47013026270429 : Nat.Prime 47013026270429 := by
  apply lucas_primality 47013026270429 (2 : ZMod 47013026270429)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (101, 1), (81353, 1), (1430419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (101, 1), (81353, 1), (1430419, 1)] : List FactorBlock).map factorBlockValue).prod) = 47013026270429 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_101
      · exact prime_thirtyNineAK_81353
      · exact prime_thirtyNineAK_1430419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 47013026270429) ^ 23506513135214 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 47013026270429) ^ 465475507628 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 47013026270429) ^ 577889276 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 47013026270429) ^ 32866612 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_50456514775123 : Nat.Prime 50456514775123 := by
  apply lucas_primality 50456514775123 (2 : ZMod 50456514775123)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (2593, 1), (360347051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (2593, 1), (360347051, 1)] : List FactorBlock).map factorBlockValue).prod) = 50456514775123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_2593
      · exact prime_thirtyNineAK_360347051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 50456514775123) ^ 25228257387561 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 50456514775123) ^ 16818838258374 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 50456514775123) ^ 19458740754 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 50456514775123) ^ 140022 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_56990096752577 : Nat.Prime 56990096752577 := by
  apply lucas_primality 56990096752577 (3 : ZMod 56990096752577)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (13, 1), (59, 1), (1160978177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (13, 1), (59, 1), (1160978177, 1)] : List FactorBlock).map factorBlockValue).prod) = 56990096752577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_13
      · exact prime_thirtyNineAK_59
      · exact prime_thirtyNineAK_1160978177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 56990096752577) ^ 28495048376288 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 56990096752577) ^ 4383853596352 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 56990096752577) ^ 965933843264 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 56990096752577) ^ 49088 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_65360989560707 : Nat.Prime 65360989560707 := by
  apply lucas_primality 65360989560707 (2 : ZMod 65360989560707)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (209497, 1), (22285007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (209497, 1), (22285007, 1)] : List FactorBlock).map factorBlockValue).prod) = 65360989560707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_209497
      · exact prime_thirtyNineAK_22285007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 65360989560707) ^ 32680494780353 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 65360989560707) ^ 9337284222958 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 65360989560707) ^ 311990098 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 65360989560707) ^ 2932958 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_75763511577581 : Nat.Prime 75763511577581 := by
  apply lucas_primality 75763511577581 (3 : ZMod 75763511577581)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (4159, 1), (910838081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (4159, 1), (910838081, 1)] : List FactorBlock).map factorBlockValue).prod) = 75763511577581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_4159
      · exact prime_thirtyNineAK_910838081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 75763511577581) ^ 37881755788790 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 75763511577581) ^ 15152702315516 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 75763511577581) ^ 18216761620 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 75763511577581) ^ 83180 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_102102247358591 : Nat.Prime 102102247358591 := by
  apply lucas_primality 102102247358591 (14 : ZMod 102102247358591)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (523, 1), (10159, 1), (1921687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (523, 1), (10159, 1), (1921687, 1)] : List FactorBlock).map factorBlockValue).prod) = 102102247358591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_523
      · exact prime_thirtyNineAK_10159
      · exact prime_thirtyNineAK_1921687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 102102247358591) ^ 51051123679295 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (14 : ZMod 102102247358591) ^ 20420449471718 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (14 : ZMod 102102247358591) ^ 195224182330 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (14 : ZMod 102102247358591) ^ 10050423010 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (14 : ZMod 102102247358591) ^ 53131570 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_119134327776067 : Nat.Prime 119134327776067 := by
  apply lucas_primality 119134327776067 (7 : ZMod 119134327776067)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (213502379527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (213502379527, 1)] : List FactorBlock).map factorBlockValue).prod) = 119134327776067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_31
      · exact prime_thirtyNineAK_213502379527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 119134327776067) ^ 59567163888033 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 119134327776067) ^ 39711442592022 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 119134327776067) ^ 3843042831486 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 119134327776067) ^ 558 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_120700677594017 : Nat.Prime 120700677594017 := by
  apply lucas_primality 120700677594017 (3 : ZMod 120700677594017)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (13, 2), (313, 1), (3691, 1), (19319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (13, 2), (313, 1), (3691, 1), (19319, 1)] : List FactorBlock).map factorBlockValue).prod) = 120700677594017 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_13
      · exact prime_thirtyNineAK_313
      · exact prime_thirtyNineAK_3691
      · exact prime_thirtyNineAK_19319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 120700677594017) ^ 60350338797008 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 120700677594017) ^ 9284667507232 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 120700677594017) ^ 385625168032 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 120700677594017) ^ 32701348576 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 120700677594017) ^ 6247770464 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_130664957523739 : Nat.Prime 130664957523739 := by
  apply lucas_primality 130664957523739 (2 : ZMod 130664957523739)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (31, 1), (2083, 1), (30659441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (31, 1), (2083, 1), (30659441, 1)] : List FactorBlock).map factorBlockValue).prod) = 130664957523739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_11
      · exact prime_thirtyNineAK_31
      · exact prime_thirtyNineAK_2083
      · exact prime_thirtyNineAK_30659441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 130664957523739) ^ 65332478761869 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 130664957523739) ^ 43554985841246 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 130664957523739) ^ 11878632502158 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 130664957523739) ^ 4214998629798 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 130664957523739) ^ 62729216286 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 130664957523739) ^ 4261818 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_160284903568781 : Nat.Prime 160284903568781 := by
  apply lucas_primality 160284903568781 (2 : ZMod 160284903568781)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 1), (61, 1), (113, 1), (68392019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 1), (61, 1), (113, 1), (68392019, 1)] : List FactorBlock).map factorBlockValue).prod) = 160284903568781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_17
      · exact prime_thirtyNineAK_61
      · exact prime_thirtyNineAK_113
      · exact prime_thirtyNineAK_68392019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 160284903568781) ^ 80142451784390 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 160284903568781) ^ 32056980713756 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 160284903568781) ^ 9428523739340 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 160284903568781) ^ 2627621369980 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 160284903568781) ^ 1418450474060 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 160284903568781) ^ 2343620 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_184286892688891 : Nat.Prime 184286892688891 := by
  apply lucas_primality 184286892688891 (10 : ZMod 184286892688891)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (101, 1), (557, 1), (109193459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (101, 1), (557, 1), (109193459, 1)] : List FactorBlock).map factorBlockValue).prod) = 184286892688891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_101
      · exact prime_thirtyNineAK_557
      · exact prime_thirtyNineAK_109193459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 184286892688891) ^ 92143446344445 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (10 : ZMod 184286892688891) ^ 61428964229630 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (10 : ZMod 184286892688891) ^ 36857378537778 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (10 : ZMod 184286892688891) ^ 1824622699890 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (10 : ZMod 184286892688891) ^ 330856180770 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (10 : ZMod 184286892688891) ^ 1687710 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_226043412291283 : Nat.Prime 226043412291283 := by
  apply lucas_primality 226043412291283 (2 : ZMod 226043412291283)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (359, 1), (104941231333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (359, 1), (104941231333, 1)] : List FactorBlock).map factorBlockValue).prod) = 226043412291283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_359
      · exact prime_thirtyNineAK_104941231333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 226043412291283) ^ 113021706145641 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 226043412291283) ^ 75347804097094 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 226043412291283) ^ 629647387998 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 226043412291283) ^ 2154 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_266466049533457 : Nat.Prime 266466049533457 := by
  apply lucas_primality 266466049533457 (10 : ZMod 266466049533457)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (17, 1), (53, 1), (521, 1), (11826007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (17, 1), (53, 1), (521, 1), (11826007, 1)] : List FactorBlock).map factorBlockValue).prod) = 266466049533457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_17
      · exact prime_thirtyNineAK_53
      · exact prime_thirtyNineAK_521
      · exact prime_thirtyNineAK_11826007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 266466049533457) ^ 133233024766728 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (10 : ZMod 266466049533457) ^ 88822016511152 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (10 : ZMod 266466049533457) ^ 15674473501968 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (10 : ZMod 266466049533457) ^ 5027661311952 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (10 : ZMod 266466049533457) ^ 511451150736 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (10 : ZMod 266466049533457) ^ 22532208 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_304128603975499 : Nat.Prime 304128603975499 := by
  apply lucas_primality 304128603975499 (3 : ZMod 304128603975499)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (103, 1), (3109, 1), (158288029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (103, 1), (3109, 1), (158288029, 1)] : List FactorBlock).map factorBlockValue).prod) = 304128603975499 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_103
      · exact prime_thirtyNineAK_3109
      · exact prime_thirtyNineAK_158288029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 304128603975499) ^ 152064301987749 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 304128603975499) ^ 101376201325166 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 304128603975499) ^ 2952704892966 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 304128603975499) ^ 97822001922 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 304128603975499) ^ 1921362 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_366444555641737 : Nat.Prime 366444555641737 := by
  apply lucas_primality 366444555641737 (5 : ZMod 366444555641737)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (13, 1), (487, 1), (1381, 1), (158759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (13, 1), (487, 1), (1381, 1), (158759, 1)] : List FactorBlock).map factorBlockValue).prod) = 366444555641737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_11
      · exact prime_thirtyNineAK_13
      · exact prime_thirtyNineAK_487
      · exact prime_thirtyNineAK_1381
      · exact prime_thirtyNineAK_158759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 366444555641737) ^ 183222277820868 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 366444555641737) ^ 122148185213912 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 366444555641737) ^ 33313141421976 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 366444555641737) ^ 28188042741672 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 366444555641737) ^ 752452886328 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 366444555641737) ^ 265347252456 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 366444555641737) ^ 2308181304 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_376104210163433 : Nat.Prime 376104210163433 := by
  apply lucas_primality 376104210163433 (3 : ZMod 376104210163433)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (47013026270429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (47013026270429, 1)] : List FactorBlock).map factorBlockValue).prod) = 376104210163433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_47013026270429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 376104210163433) ^ 188052105081716 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 376104210163433) ^ 8 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_627106793434213 : Nat.Prime 627106793434213 := by
  apply lucas_primality 627106793434213 (2 : ZMod 627106793434213)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (13, 1), (8419, 1), (9744517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (13, 1), (8419, 1), (9744517, 1)] : List FactorBlock).map factorBlockValue).prod) = 627106793434213 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_13
      · exact prime_thirtyNineAK_8419
      · exact prime_thirtyNineAK_9744517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 627106793434213) ^ 313553396717106 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 627106793434213) ^ 209035597811404 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 627106793434213) ^ 89586684776316 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 627106793434213) ^ 48238984110324 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 627106793434213) ^ 74487087948 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 627106793434213) ^ 64354836 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_686809978352741 : Nat.Prime 686809978352741 := by
  apply lucas_primality 686809978352741 (3 : ZMod 686809978352741)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (359, 1), (1867, 1), (4657739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (359, 1), (1867, 1), (4657739, 1)] : List FactorBlock).map factorBlockValue).prod) = 686809978352741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_11
      · exact prime_thirtyNineAK_359
      · exact prime_thirtyNineAK_1867
      · exact prime_thirtyNineAK_4657739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 686809978352741) ^ 343404989176370 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 686809978352741) ^ 137361995670548 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 686809978352741) ^ 62437270759340 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 686809978352741) ^ 1913119716860 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 686809978352741) ^ 367868226220 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 686809978352741) ^ 147455660 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_898106685584249 : Nat.Prime 898106685584249 := by
  apply lucas_primality 898106685584249 (3 : ZMod 898106685584249)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (54949, 1), (291863717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (54949, 1), (291863717, 1)] : List FactorBlock).map factorBlockValue).prod) = 898106685584249 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_54949
      · exact prime_thirtyNineAK_291863717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 898106685584249) ^ 449053342792124 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 898106685584249) ^ 128300955083464 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 898106685584249) ^ 16344368152 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 898106685584249) ^ 3077144 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_1091318243936369 : Nat.Prime 1091318243936369 := by
  apply lucas_primality 1091318243936369 (3 : ZMod 1091318243936369)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (31, 1), (59, 1), (5327453741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (31, 1), (59, 1), (5327453741, 1)] : List FactorBlock).map factorBlockValue).prod) = 1091318243936369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_31
      · exact prime_thirtyNineAK_59
      · exact prime_thirtyNineAK_5327453741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1091318243936369) ^ 545659121968184 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1091318243936369) ^ 155902606276624 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1091318243936369) ^ 35203814320528 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1091318243936369) ^ 18496919388752 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1091318243936369) ^ 204848 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_1259718704296139 : Nat.Prime 1259718704296139 := by
  apply lucas_primality 1259718704296139 (2 : ZMod 1259718704296139)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (37050550126357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (37050550126357, 1)] : List FactorBlock).map factorBlockValue).prod) = 1259718704296139 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_17
      · exact prime_thirtyNineAK_37050550126357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1259718704296139) ^ 629859352148069 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1259718704296139) ^ 74101100252714 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1259718704296139) ^ 34 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_1428925076923349 : Nat.Prime 1428925076923349 := by
  apply lucas_primality 1428925076923349 (2 : ZMod 1428925076923349)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (37, 1), (419, 1), (15877, 1), (46817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (37, 1), (419, 1), (15877, 1), (46817, 1)] : List FactorBlock).map factorBlockValue).prod) = 1428925076923349 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_31
      · exact prime_thirtyNineAK_37
      · exact prime_thirtyNineAK_419
      · exact prime_thirtyNineAK_15877
      · exact prime_thirtyNineAK_46817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1428925076923349) ^ 714462538461674 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1428925076923349) ^ 46094357320108 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1428925076923349) ^ 38619596673604 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1428925076923349) ^ 3410322379292 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1428925076923349) ^ 89999689924 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1428925076923349) ^ 30521500244 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_1474759419059263 : Nat.Prime 1474759419059263 := by
  apply lucas_primality 1474759419059263 (3 : ZMod 1474759419059263)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (131, 1), (268040606881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (131, 1), (268040606881, 1)] : List FactorBlock).map factorBlockValue).prod) = 1474759419059263 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_131
      · exact prime_thirtyNineAK_268040606881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1474759419059263) ^ 737379709529631 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1474759419059263) ^ 491586473019754 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1474759419059263) ^ 210679917008466 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1474759419059263) ^ 11257705489002 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1474759419059263) ^ 5502 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_1667237541899513 : Nat.Prime 1667237541899513 := by
  apply lucas_primality 1667237541899513 (3 : ZMod 1667237541899513)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) = 1667237541899513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_11
      · exact prime_thirtyNineAK_41
      · exact prime_thirtyNineAK_462094662389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1667237541899513) ^ 833618770949756 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 151567049263592 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 40664330290232 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 3608 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_1697883027291527 : Nat.Prime 1697883027291527 := by
  apply lucas_primality 1697883027291527 (5 : ZMod 1697883027291527)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13837177, 1), (61352219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13837177, 1), (61352219, 1)] : List FactorBlock).map factorBlockValue).prod) = 1697883027291527 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_13837177
      · exact prime_thirtyNineAK_61352219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1697883027291527) ^ 848941513645763 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1697883027291527) ^ 122704438 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1697883027291527) ^ 27674354 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_1796213371168499 : Nat.Prime 1796213371168499 := by
  apply lucas_primality 1796213371168499 (2 : ZMod 1796213371168499)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (898106685584249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (898106685584249, 1)] : List FactorBlock).map factorBlockValue).prod) = 1796213371168499 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_898106685584249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1796213371168499) ^ 898106685584249 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1796213371168499) ^ 2 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_3080389673224709 : Nat.Prime 3080389673224709 := by
  apply lucas_primality 3080389673224709 (2 : ZMod 3080389673224709)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 2), (967, 1), (28229, 1), (166931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 2), (967, 1), (28229, 1), (166931, 1)] : List FactorBlock).map factorBlockValue).prod) = 3080389673224709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_13
      · exact prime_thirtyNineAK_967
      · exact prime_thirtyNineAK_28229
      · exact prime_thirtyNineAK_166931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3080389673224709) ^ 1540194836612354 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3080389673224709) ^ 236953051786516 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3080389673224709) ^ 3185511554524 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3080389673224709) ^ 109121459252 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3080389673224709) ^ 18453071468 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_3279727414308767 : Nat.Prime 3279727414308767 := by
  apply lucas_primality 3279727414308767 (5 : ZMod 3279727414308767)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83, 1), (89, 1), (24953, 1), (8896453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83, 1), (89, 1), (24953, 1), (8896453, 1)] : List FactorBlock).map factorBlockValue).prod) = 3279727414308767 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_83
      · exact prime_thirtyNineAK_89
      · exact prime_thirtyNineAK_24953
      · exact prime_thirtyNineAK_8896453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3279727414308767) ^ 1639863707154383 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 3279727414308767) ^ 39514788124202 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 3279727414308767) ^ 36850869823694 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 3279727414308767) ^ 131436196622 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 3279727414308767) ^ 368655622 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_3529887272639347 : Nat.Prime 3529887272639347 := by
  apply lucas_primality 3529887272639347 (2 : ZMod 3529887272639347)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4001, 1), (147041875891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4001, 1), (147041875891, 1)] : List FactorBlock).map factorBlockValue).prod) = 3529887272639347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_4001
      · exact prime_thirtyNineAK_147041875891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3529887272639347) ^ 1764943636319673 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3529887272639347) ^ 1176629090879782 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3529887272639347) ^ 882251255346 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3529887272639347) ^ 24006 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_11655978276633277 : Nat.Prime 11655978276633277 := by
  apply lucas_primality 11655978276633277 (2 : ZMod 11655978276633277)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (47, 1), (81047, 1), (14999741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (47, 1), (81047, 1), (14999741, 1)] : List FactorBlock).map factorBlockValue).prod) = 11655978276633277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_17
      · exact prime_thirtyNineAK_47
      · exact prime_thirtyNineAK_81047
      · exact prime_thirtyNineAK_14999741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11655978276633277) ^ 5827989138316638 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 3885326092211092 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 685645780978428 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 247999537800708 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 143817516708 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 777078636 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_11895479753831941 : Nat.Prime 11895479753831941 := by
  apply lucas_primality 11895479753831941 (2 : ZMod 11895479753831941)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (28322570842457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (28322570842457, 1)] : List FactorBlock).map factorBlockValue).prod) = 11895479753831941 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_28322570842457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11895479753831941) ^ 5947739876915970 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 11895479753831941) ^ 3965159917943980 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 11895479753831941) ^ 2379095950766388 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 11895479753831941) ^ 1699354250547420 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 11895479753831941) ^ 420 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_13087761833364721 : Nat.Prime 13087761833364721 := by
  apply lucas_primality 13087761833364721 (11 : ZMod 13087761833364721)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (1123, 1), (48559520011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (1123, 1), (48559520011, 1)] : List FactorBlock).map factorBlockValue).prod) = 13087761833364721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_1123
      · exact prime_thirtyNineAK_48559520011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 13087761833364721) ^ 6543880916682360 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (11 : ZMod 13087761833364721) ^ 4362587277788240 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (11 : ZMod 13087761833364721) ^ 2617552366672944 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (11 : ZMod 13087761833364721) ^ 11654284802640 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (11 : ZMod 13087761833364721) ^ 269520 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_17274080639688469 : Nat.Prime 17274080639688469 := by
  apply lucas_primality 17274080639688469 (2 : ZMod 17274080639688469)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (75763511577581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (75763511577581, 1)] : List FactorBlock).map factorBlockValue).prod) = 17274080639688469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_19
      · exact prime_thirtyNineAK_75763511577581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17274080639688469) ^ 8637040319844234 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 17274080639688469) ^ 5758026879896156 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 17274080639688469) ^ 909162138930972 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 17274080639688469) ^ 228 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_18536322812665897 : Nat.Prime 18536322812665897 := by
  apply lucas_primality 18536322812665897 (10 : ZMod 18536322812665897)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 2), (5254059754157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 2), (5254059754157, 1)] : List FactorBlock).map factorBlockValue).prod) = 18536322812665897 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_5254059754157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 18536322812665897) ^ 9268161406332948 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (10 : ZMod 18536322812665897) ^ 6178774270888632 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (10 : ZMod 18536322812665897) ^ 2648046116095128 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (10 : ZMod 18536322812665897) ^ 3528 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_20372010569611529 : Nat.Prime 20372010569611529 := by
  apply lucas_primality 20372010569611529 (3 : ZMod 20372010569611529)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1996289, 1), (1275617569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1996289, 1), (1275617569, 1)] : List FactorBlock).map factorBlockValue).prod) = 20372010569611529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_1996289
      · exact prime_thirtyNineAK_1275617569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 20372010569611529) ^ 10186005284805764 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 20372010569611529) ^ 10204940552 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 20372010569611529) ^ 15970312 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_23273239678327147 : Nat.Prime 23273239678327147 := by
  apply lucas_primality 23273239678327147 (5 : ZMod 23273239678327147)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (197, 1), (269, 1), (3011, 1), (24309517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (197, 1), (269, 1), (3011, 1), (24309517, 1)] : List FactorBlock).map factorBlockValue).prod) = 23273239678327147 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_197
      · exact prime_thirtyNineAK_269
      · exact prime_thirtyNineAK_3011
      · exact prime_thirtyNineAK_24309517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 23273239678327147) ^ 11636619839163573 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 23273239678327147) ^ 7757746559442382 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 23273239678327147) ^ 118138272478818 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 23273239678327147) ^ 86517619622034 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 23273239678327147) ^ 7729405406286 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 23273239678327147) ^ 957371538 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_25024350819790243 : Nat.Prime 25024350819790243 := by
  apply lucas_primality 25024350819790243 (2 : ZMod 25024350819790243)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (47149, 1), (29486133581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (47149, 1), (29486133581, 1)] : List FactorBlock).map factorBlockValue).prod) = 25024350819790243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_47149
      · exact prime_thirtyNineAK_29486133581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 25024350819790243) ^ 12512175409895121 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 25024350819790243) ^ 8341450273263414 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 25024350819790243) ^ 530750404458 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 25024350819790243) ^ 848682 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_30133561870930829 : Nat.Prime 30133561870930829 := by
  apply lucas_primality 30133561870930829 (2 : ZMod 30133561870930829)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (160284903568781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (160284903568781, 1)] : List FactorBlock).map factorBlockValue).prod) = 30133561870930829 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_47
      · exact prime_thirtyNineAK_160284903568781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30133561870930829) ^ 15066780935465414 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 30133561870930829) ^ 641139614275124 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 30133561870930829) ^ 188 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_78526571000188327 : Nat.Prime 78526571000188327 := by
  apply lucas_primality 78526571000188327 (3 : ZMod 78526571000188327)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13087761833364721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13087761833364721, 1)] : List FactorBlock).map factorBlockValue).prod) = 78526571000188327 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_13087761833364721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 78526571000188327) ^ 39263285500094163 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 78526571000188327) ^ 26175523666729442 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 78526571000188327) ^ 6 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_116559782766332771 : Nat.Prime 116559782766332771 := by
  apply lucas_primality 116559782766332771 (2 : ZMod 116559782766332771)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11655978276633277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11655978276633277, 1)] : List FactorBlock).map factorBlockValue).prod) = 116559782766332771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_11655978276633277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 116559782766332771) ^ 58279891383166385 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 116559782766332771) ^ 23311956553266554 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 116559782766332771) ^ 10 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_239766403692867703 : Nat.Prime 239766403692867703 := by
  apply lucas_primality 239766403692867703 (3 : ZMod 239766403692867703)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (89, 1), (1753, 1), (16097, 1), (2273119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (89, 1), (1753, 1), (16097, 1), (2273119, 1)] : List FactorBlock).map factorBlockValue).prod) = 239766403692867703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_89
      · exact prime_thirtyNineAK_1753
      · exact prime_thirtyNineAK_16097
      · exact prime_thirtyNineAK_2273119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 239766403692867703) ^ 119883201846433851 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 239766403692867703) ^ 79922134564289234 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 239766403692867703) ^ 34252343384695386 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 239766403692867703) ^ 2694004535874918 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 239766403692867703) ^ 136774902277734 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 239766403692867703) ^ 14895098694966 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 239766403692867703) ^ 105479037258 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_259360801617151183 : Nat.Prime 259360801617151183 := by
  apply lucas_primality 259360801617151183 (3 : ZMod 259360801617151183)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (43, 1), (2273, 1), (34020590371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (43, 1), (2273, 1), (34020590371, 1)] : List FactorBlock).map factorBlockValue).prod) = 259360801617151183 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_13
      · exact prime_thirtyNineAK_43
      · exact prime_thirtyNineAK_2273
      · exact prime_thirtyNineAK_34020590371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 259360801617151183) ^ 129680400808575591 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 259360801617151183) ^ 86453600539050394 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 259360801617151183) ^ 19950830893627014 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 259360801617151183) ^ 6031646549236074 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 259360801617151183) ^ 114105060104334 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 259360801617151183) ^ 7623642 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_426950491054489151 : Nat.Prime 426950491054489151 := by
  apply lucas_primality 426950491054489151 (7 : ZMod 426950491054489151)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (23, 1), (2767, 1), (19167809209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (23, 1), (2767, 1), (19167809209, 1)] : List FactorBlock).map factorBlockValue).prod) = 426950491054489151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_23
      · exact prime_thirtyNineAK_2767
      · exact prime_thirtyNineAK_19167809209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 426950491054489151) ^ 213475245527244575 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 426950491054489151) ^ 85390098210897830 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 426950491054489151) ^ 60992927293498450 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 426950491054489151) ^ 18563064828456050 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 426950491054489151) ^ 154300864132450 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 426950491054489151) ^ 22274350 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_483498887150858771 : Nat.Prime 483498887150858771 := by
  apply lucas_primality 483498887150858771 (2 : ZMod 483498887150858771)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) = 483498887150858771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_29
      · exact prime_thirtyNineAK_1667237541899513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 483498887150858771) ^ 241749443575429385 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 96699777430171754 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 16672375418995130 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 290 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_61717
      · exact prime_thirtyNineAK_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_699851181472581709 : Nat.Prime 699851181472581709 := by
  apply lucas_primality 699851181472581709 (6 : ZMod 699851181472581709)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (31, 1), (627106793434213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (31, 1), (627106793434213, 1)] : List FactorBlock).map factorBlockValue).prod) = 699851181472581709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_31
      · exact prime_thirtyNineAK_627106793434213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 699851181472581709) ^ 349925590736290854 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (6 : ZMod 699851181472581709) ^ 233283727157527236 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (6 : ZMod 699851181472581709) ^ 22575844563631668 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (6 : ZMod 699851181472581709) ^ 1116 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_949956622275315539 : Nat.Prime 949956622275315539 := by
  apply lucas_primality 949956622275315539 (2 : ZMod 949956622275315539)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 2), (43, 1), (65360989560707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 2), (43, 1), (65360989560707, 1)] : List FactorBlock).map factorBlockValue).prod) = 949956622275315539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_13
      · exact prime_thirtyNineAK_43
      · exact prime_thirtyNineAK_65360989560707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 949956622275315539) ^ 474978311137657769 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 949956622275315539) ^ 73073586328870426 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 949956622275315539) ^ 22092014471518966 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 949956622275315539) ^ 14534 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_1561827409733979467 : Nat.Prime 1561827409733979467 := by
  apply lucas_primality 1561827409733979467 (2 : ZMod 1561827409733979467)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (2767, 1), (955337, 1), (22724479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (2767, 1), (955337, 1), (22724479, 1)] : List FactorBlock).map factorBlockValue).prod) = 1561827409733979467 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_13
      · exact prime_thirtyNineAK_2767
      · exact prime_thirtyNineAK_955337
      · exact prime_thirtyNineAK_22724479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1561827409733979467) ^ 780913704866989733 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1561827409733979467) ^ 120140569979536882 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1561827409733979467) ^ 564447925454998 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1561827409733979467) ^ 1634844468218 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1561827409733979467) ^ 68728854454 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_1603952514074243401 : Nat.Prime 1603952514074243401 := by
  apply lucas_primality 1603952514074243401 (7 : ZMod 1603952514074243401)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (17, 1), (19, 1), (47, 1), (67819, 1), (2596501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (17, 1), (19, 1), (47, 1), (67819, 1), (2596501, 1)] : List FactorBlock).map factorBlockValue).prod) = 1603952514074243401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_17
      · exact prime_thirtyNineAK_19
      · exact prime_thirtyNineAK_47
      · exact prime_thirtyNineAK_67819
      · exact prime_thirtyNineAK_2596501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1603952514074243401) ^ 801976257037121700 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 1603952514074243401) ^ 534650838024747800 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 1603952514074243401) ^ 320790502814848680 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 1603952514074243401) ^ 94350147886720200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 1603952514074243401) ^ 84418553372328600 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 1603952514074243401) ^ 34126649235622200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 1603952514074243401) ^ 23650489008600 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 1603952514074243401) ^ 617736143400 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_2009831726809906421 : Nat.Prime 2009831726809906421 := by
  apply lucas_primality 2009831726809906421 (2 : ZMod 2009831726809906421)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (557, 1), (409901, 1), (440144753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (557, 1), (409901, 1), (440144753, 1)] : List FactorBlock).map factorBlockValue).prod) = 2009831726809906421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_557
      · exact prime_thirtyNineAK_409901
      · exact prime_thirtyNineAK_440144753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2009831726809906421) ^ 1004915863404953210 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2009831726809906421) ^ 401966345361981284 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2009831726809906421) ^ 3608315487989060 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2009831726809906421) ^ 4903212548420 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2009831726809906421) ^ 4566297140 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_3077167559992740997 : Nat.Prime 3077167559992740997 := by
  apply lucas_primality 3077167559992740997 (2 : ZMod 3077167559992740997)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (21569, 1), (11888851128907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (21569, 1), (11888851128907, 1)] : List FactorBlock).map factorBlockValue).prod) = 3077167559992740997 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_21569
      · exact prime_thirtyNineAK_11888851128907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3077167559992740997) ^ 1538583779996370498 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3077167559992740997) ^ 1025722519997580332 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3077167559992740997) ^ 142666213546884 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3077167559992740997) ^ 258828 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_3388781283930634511 : Nat.Prime 3388781283930634511 := by
  apply lucas_primality 3388781283930634511 (23 : ZMod 3388781283930634511)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (83, 1), (547, 1), (563, 1), (7547, 1), (1756691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (83, 1), (547, 1), (563, 1), (7547, 1), (1756691, 1)] : List FactorBlock).map factorBlockValue).prod) = 3388781283930634511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_83
      · exact prime_thirtyNineAK_547
      · exact prime_thirtyNineAK_563
      · exact prime_thirtyNineAK_7547
      · exact prime_thirtyNineAK_1756691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 3388781283930634511) ^ 1694390641965317255 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (23 : ZMod 3388781283930634511) ^ 677756256786126902 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (23 : ZMod 3388781283930634511) ^ 40828690167838970 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (23 : ZMod 3388781283930634511) ^ 6195212584882330 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (23 : ZMod 3388781283930634511) ^ 6019149705027770 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (23 : ZMod 3388781283930634511) ^ 449023623152330 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (23 : ZMod 3388781283930634511) ^ 1929070783610 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_4018378747686678983 : Nat.Prime 4018378747686678983 := by
  apply lucas_primality 4018378747686678983 (5 : ZMod 4018378747686678983)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (157, 1), (193, 1), (14419, 1), (4598633189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (157, 1), (193, 1), (14419, 1), (4598633189, 1)] : List FactorBlock).map factorBlockValue).prod) = 4018378747686678983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_157
      · exact prime_thirtyNineAK_193
      · exact prime_thirtyNineAK_14419
      · exact prime_thirtyNineAK_4598633189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4018378747686678983) ^ 2009189373843339491 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 4018378747686678983) ^ 25594769093545726 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 4018378747686678983) ^ 20820615272987974 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 4018378747686678983) ^ 278686368519778 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 4018378747686678983) ^ 873820238 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_6276586759550679409 : Nat.Prime 6276586759550679409 := by
  apply lucas_primality 6276586759550679409 (7 : ZMod 6276586759550679409)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (43, 1), (254927, 1), (11928834361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (43, 1), (254927, 1), (11928834361, 1)] : List FactorBlock).map factorBlockValue).prod) = 6276586759550679409 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_43
      · exact prime_thirtyNineAK_254927
      · exact prime_thirtyNineAK_11928834361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6276586759550679409) ^ 3138293379775339704 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 6276586759550679409) ^ 2092195586516893136 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 6276586759550679409) ^ 145967133943039056 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 6276586759550679409) ^ 24621114121104 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 6276586759550679409) ^ 526169328 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_7542770108201126977 : Nat.Prime 7542770108201126977 := by
  apply lucas_primality 7542770108201126977 (7 : ZMod 7542770108201126977)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (81540863, 1), (481786181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (81540863, 1), (481786181, 1)] : List FactorBlock).map factorBlockValue).prod) = 7542770108201126977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_81540863
      · exact prime_thirtyNineAK_481786181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 7542770108201126977) ^ 3771385054100563488 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 7542770108201126977) ^ 2514256702733708992 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 7542770108201126977) ^ 92502946752 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (7 : ZMod 7542770108201126977) ^ 15655845696 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_7777367187437459221 : Nat.Prime 7777367187437459221 := by
  apply lucas_primality 7777367187437459221 (6 : ZMod 7777367187437459221)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (367, 1), (50456514775123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (367, 1), (50456514775123, 1)] : List FactorBlock).map factorBlockValue).prod) = 7777367187437459221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_367
      · exact prime_thirtyNineAK_50456514775123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 7777367187437459221) ^ 3888683593718729610 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (6 : ZMod 7777367187437459221) ^ 2592455729145819740 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (6 : ZMod 7777367187437459221) ^ 1555473437487491844 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (6 : ZMod 7777367187437459221) ^ 1111052455348208460 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (6 : ZMod 7777367187437459221) ^ 21191736205551660 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (6 : ZMod 7777367187437459221) ^ 154140 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_8003431466359176569 : Nat.Prime 8003431466359176569 := by
  apply lucas_primality 8003431466359176569 (3 : ZMod 8003431466359176569)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (9320287, 1), (15334122119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (9320287, 1), (15334122119, 1)] : List FactorBlock).map factorBlockValue).prod) = 8003431466359176569 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_9320287
      · exact prime_thirtyNineAK_15334122119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8003431466359176569) ^ 4001715733179588284 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 8003431466359176569) ^ 1143347352337025224 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 8003431466359176569) ^ 858710838664 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 8003431466359176569) ^ 521936072 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_11222777554155983047 : Nat.Prime 11222777554155983047 := by
  apply lucas_primality 11222777554155983047 (3 : ZMod 11222777554155983047)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (17, 1), (1428925076923349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (17, 1), (1428925076923349, 1)] : List FactorBlock).map factorBlockValue).prod) = 11222777554155983047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_11
      · exact prime_thirtyNineAK_17
      · exact prime_thirtyNineAK_1428925076923349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11222777554155983047) ^ 5611388777077991523 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 11222777554155983047) ^ 3740925851385327682 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 11222777554155983047) ^ 1603253936307997578 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 11222777554155983047) ^ 1020252504923271186 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 11222777554155983047) ^ 660163385538587238 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 11222777554155983047) ^ 7854 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_13145780685211854149 : Nat.Prime 13145780685211854149 := by
  apply lucas_primality 13145780685211854149 (2 : ZMod 13145780685211854149)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (31, 1), (67, 1), (226043412291283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (31, 1), (67, 1), (226043412291283, 1)] : List FactorBlock).map factorBlockValue).prod) = 13145780685211854149 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_31
      · exact prime_thirtyNineAK_67
      · exact prime_thirtyNineAK_226043412291283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13145780685211854149) ^ 6572890342605927074 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 13145780685211854149) ^ 1877968669315979164 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 13145780685211854149) ^ 424057441458446908 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 13145780685211854149) ^ 196205681868833644 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 13145780685211854149) ^ 58156 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_28189030666041590231 : Nat.Prime 28189030666041590231 := by
  apply lucas_primality 28189030666041590231 (19 : ZMod 28189030666041590231)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (6449, 1), (82487, 1), (230395727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (6449, 1), (82487, 1), (230395727, 1)] : List FactorBlock).map factorBlockValue).prod) = 28189030666041590231 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_23
      · exact prime_thirtyNineAK_6449
      · exact prime_thirtyNineAK_82487
      · exact prime_thirtyNineAK_230395727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 28189030666041590231) ^ 14094515333020795115 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (19 : ZMod 28189030666041590231) ^ 5637806133208318046 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (19 : ZMod 28189030666041590231) ^ 1225610028958330010 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (19 : ZMod 28189030666041590231) ^ 4371070036601270 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (19 : ZMod 28189030666041590231) ^ 341739069987290 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (19 : ZMod 28189030666041590231) ^ 122350492490 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_46854822292019384011 : Nat.Prime 46854822292019384011 := by
  apply lucas_primality 46854822292019384011 (2 : ZMod 46854822292019384011)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1561827409733979467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1561827409733979467, 1)] : List FactorBlock).map factorBlockValue).prod) = 46854822292019384011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_1561827409733979467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 46854822292019384011) ^ 23427411146009692005 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 46854822292019384011) ^ 15618274097339794670 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 46854822292019384011) ^ 9370964458403876802 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 46854822292019384011) ^ 30 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_67337590816601618489 : Nat.Prime 67337590816601618489 := by
  apply lucas_primality 67337590816601618489 (6 : ZMod 67337590816601618489)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (71, 1), (9269333, 1), (752335981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (71, 1), (9269333, 1), (752335981, 1)] : List FactorBlock).map factorBlockValue).prod) = 67337590816601618489 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_17
      · exact prime_thirtyNineAK_71
      · exact prime_thirtyNineAK_9269333
      · exact prime_thirtyNineAK_752335981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 67337590816601618489) ^ 33668795408300809244 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (6 : ZMod 67337590816601618489) ^ 3961034753917742264 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (6 : ZMod 67337590816601618489) ^ 948416772064811528 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (6 : ZMod 67337590816601618489) ^ 7264556232536 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (6 : ZMod 67337590816601618489) ^ 89504679448 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_71526384117836592751 : Nat.Prime 71526384117836592751 := by
  apply lucas_primality 71526384117836592751 (3 : ZMod 71526384117836592751)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 3), (13, 1), (17, 1), (79, 1), (1820808984041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 3), (13, 1), (17, 1), (79, 1), (1820808984041, 1)] : List FactorBlock).map factorBlockValue).prod) = 71526384117836592751 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_13
      · exact prime_thirtyNineAK_17
      · exact prime_thirtyNineAK_79
      · exact prime_thirtyNineAK_1820808984041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 71526384117836592751) ^ 35763192058918296375 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 71526384117836592751) ^ 23842128039278864250 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 71526384117836592751) ^ 14305276823567318550 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 71526384117836592751) ^ 5502029547525891750 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 71526384117836592751) ^ 4207434359872740750 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 71526384117836592751) ^ 905397267314387250 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 71526384117836592751) ^ 39282750 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_114496238890998451481 : Nat.Prime 114496238890998451481 := by
  apply lucas_primality 114496238890998451481 (3 : ZMod 114496238890998451481)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (359, 1), (1249, 1), (65981, 1), (13821571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (359, 1), (1249, 1), (65981, 1), (13821571, 1)] : List FactorBlock).map factorBlockValue).prod) = 114496238890998451481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_359
      · exact prime_thirtyNineAK_1249
      · exact prime_thirtyNineAK_65981
      · exact prime_thirtyNineAK_13821571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 114496238890998451481) ^ 57248119445499225740 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 114496238890998451481) ^ 22899247778199690296 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 114496238890998451481) ^ 16356605555856921640 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 114496238890998451481) ^ 318931027551527720 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 114496238890998451481) ^ 91670327374698520 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 114496238890998451481) ^ 1735291051833080 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 114496238890998451481) ^ 8283880239880 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_130004395631094960253 : Nat.Prime 130004395631094960253 := by
  apply lucas_primality 130004395631094960253 (2 : ZMod 130004395631094960253)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (146173, 1), (24705200084659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (146173, 1), (24705200084659, 1)] : List FactorBlock).map factorBlockValue).prod) = 130004395631094960253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_146173
      · exact prime_thirtyNineAK_24705200084659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 130004395631094960253) ^ 65002197815547480126 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 130004395631094960253) ^ 43334798543698320084 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 130004395631094960253) ^ 889387203047724 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 130004395631094960253) ^ 5262228 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_162746309405080074029 : Nat.Prime 162746309405080074029 := by
  apply lucas_primality 162746309405080074029 (2 : ZMod 162746309405080074029)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (108179, 1), (376104210163433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (108179, 1), (376104210163433, 1)] : List FactorBlock).map factorBlockValue).prod) = 162746309405080074029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_108179
      · exact prime_thirtyNineAK_376104210163433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 162746309405080074029) ^ 81373154702540037014 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 162746309405080074029) ^ 1504416840653732 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 162746309405080074029) ^ 432716 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_187165791806578980991 : Nat.Prime 187165791806578980991 := by
  apply lucas_primality 187165791806578980991 (3 : ZMod 187165791806578980991)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (359, 1), (130664957523739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (359, 1), (130664957523739, 1)] : List FactorBlock).map factorBlockValue).prod) = 187165791806578980991 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_19
      · exact prime_thirtyNineAK_359
      · exact prime_thirtyNineAK_130664957523739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 187165791806578980991) ^ 93582895903289490495 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 187165791806578980991) ^ 62388597268859660330 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 187165791806578980991) ^ 37433158361315796198 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 187165791806578980991) ^ 26737970258082711570 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 187165791806578980991) ^ 9850831147714683210 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 187165791806578980991) ^ 521353180519718610 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 187165791806578980991) ^ 1432410 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_749677156672310144177 : Nat.Prime 749677156672310144177 := by
  apply lucas_primality 749677156672310144177 (3 : ZMod 749677156672310144177)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (46854822292019384011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (46854822292019384011, 1)] : List FactorBlock).map factorBlockValue).prod) = 749677156672310144177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_46854822292019384011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 749677156672310144177) ^ 374838578336155072088 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 749677156672310144177) ^ 16 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_806893521413797442557 : Nat.Prime 806893521413797442557 := by
  apply lucas_primality 806893521413797442557 (2 : ZMod 806893521413797442557)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (137, 1), (10949, 1), (1390841, 1), (3581129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (137, 1), (10949, 1), (1390841, 1), (3581129, 1)] : List FactorBlock).map factorBlockValue).prod) = 806893521413797442557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_137
      · exact prime_thirtyNineAK_10949
      · exact prime_thirtyNineAK_1390841
      · exact prime_thirtyNineAK_3581129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 806893521413797442557) ^ 403446760706898721278 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 806893521413797442557) ^ 268964507137932480852 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 806893521413797442557) ^ 5889733732947426588 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 806893521413797442557) ^ 73695636260279244 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 806893521413797442557) ^ 580147925905116 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 806893521413797442557) ^ 225318194740764 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_874046408329300880587 : Nat.Prime 874046408329300880587 := by
  apply lucas_primality 874046408329300880587 (3 : ZMod 874046408329300880587)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (708899, 1), (1618531, 1), (11542109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (708899, 1), (1618531, 1), (11542109, 1)] : List FactorBlock).map factorBlockValue).prod) = 874046408329300880587 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_11
      · exact prime_thirtyNineAK_708899
      · exact prime_thirtyNineAK_1618531
      · exact prime_thirtyNineAK_11542109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 874046408329300880587) ^ 437023204164650440293 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 874046408329300880587) ^ 291348802776433626862 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 874046408329300880587) ^ 79458764393572807326 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 874046408329300880587) ^ 1232963240644014 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 874046408329300880587) ^ 540024508847406 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 874046408329300880587) ^ 75726750486354 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_924096500249201382167 : Nat.Prime 924096500249201382167 := by
  apply lucas_primality 924096500249201382167 (5 : ZMod 924096500249201382167)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1223, 1), (168197789, 1), (320879927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1223, 1), (168197789, 1), (320879927, 1)] : List FactorBlock).map factorBlockValue).prod) = 924096500249201382167 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_1223
      · exact prime_thirtyNineAK_168197789
      · exact prime_thirtyNineAK_320879927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 924096500249201382167) ^ 462048250124600691083 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 924096500249201382167) ^ 132013785749885911738 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 924096500249201382167) ^ 755598119582339642 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 924096500249201382167) ^ 5494106110094 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 924096500249201382167) ^ 2879882543258 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_2013582894636896829899 : Nat.Prime 2013582894636896829899 := by
  apply lucas_primality 2013582894636896829899 (2 : ZMod 2013582894636896829899)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (191, 1), (395891, 1), (187530612799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (191, 1), (395891, 1), (187530612799, 1)] : List FactorBlock).map factorBlockValue).prod) = 2013582894636896829899 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_71
      · exact prime_thirtyNineAK_191
      · exact prime_thirtyNineAK_395891
      · exact prime_thirtyNineAK_187530612799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2013582894636896829899) ^ 1006791447318448414949 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2013582894636896829899) ^ 28360322459674603238 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2013582894636896829899) ^ 10542318820088465078 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2013582894636896829899) ^ 5086205280334478 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2013582894636896829899) ^ 10737355702 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_2124561888099414885917 : Nat.Prime 2124561888099414885917 := by
  apply lucas_primality 2124561888099414885917 (2 : ZMod 2124561888099414885917)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (131, 1), (10801067, 1), (375380267527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (131, 1), (10801067, 1), (375380267527, 1)] : List FactorBlock).map factorBlockValue).prod) = 2124561888099414885917 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_131
      · exact prime_thirtyNineAK_10801067
      · exact prime_thirtyNineAK_375380267527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2124561888099414885917) ^ 1062280944049707442958 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2124561888099414885917) ^ 16218029680148205236 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2124561888099414885917) ^ 196699260184148 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2124561888099414885917) ^ 5659759108 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_19
      · exact prime_thirtyNineAK_107
      · exact prime_thirtyNineAK_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_3720151109024930829341 : Nat.Prime 3720151109024930829341 := by
  apply lucas_primality 3720151109024930829341 (10 : ZMod 3720151109024930829341)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (13, 1), (1873, 1), (1091318243936369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (13, 1), (1873, 1), (1091318243936369, 1)] : List FactorBlock).map factorBlockValue).prod) = 3720151109024930829341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_13
      · exact prime_thirtyNineAK_1873
      · exact prime_thirtyNineAK_1091318243936369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 3720151109024930829341) ^ 1860075554512465414670 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (10 : ZMod 3720151109024930829341) ^ 744030221804986165868 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (10 : ZMod 3720151109024930829341) ^ 531450158432132975620 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (10 : ZMod 3720151109024930829341) ^ 286165469924994679180 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (10 : ZMod 3720151109024930829341) ^ 1986199203964191580 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (10 : ZMod 3720151109024930829341) ^ 3408860 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_8788300707874323997567 : Nat.Prime 8788300707874323997567 := by
  apply lucas_primality 8788300707874323997567 (5 : ZMod 8788300707874323997567)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (162746309405080074029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (162746309405080074029, 1)] : List FactorBlock).map factorBlockValue).prod) = 8788300707874323997567 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_162746309405080074029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 8788300707874323997567) ^ 4394150353937161998783 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 8788300707874323997567) ^ 2929433569291441332522 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 8788300707874323997567) ^ 54 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_9731304261388365557833 : Nat.Prime 9731304261388365557833 := by
  apply lucas_primality 9731304261388365557833 (11 : ZMod 9731304261388365557833)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 2), (17, 1), (2011, 1), (9341, 1), (8637501007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 2), (17, 1), (2011, 1), (9341, 1), (8637501007, 1)] : List FactorBlock).map factorBlockValue).prod) = 9731304261388365557833 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_17
      · exact prime_thirtyNineAK_2011
      · exact prime_thirtyNineAK_9341
      · exact prime_thirtyNineAK_8637501007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 9731304261388365557833) ^ 4865652130694182778916 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (11 : ZMod 9731304261388365557833) ^ 3243768087129455185944 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (11 : ZMod 9731304261388365557833) ^ 1390186323055480793976 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (11 : ZMod 9731304261388365557833) ^ 572429662434609738696 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (11 : ZMod 9731304261388365557833) ^ 4839037424857466712 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (11 : ZMod 9731304261388365557833) ^ 1041783991156018152 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (11 : ZMod 9731304261388365557833) ^ 1126634225976 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_16764676135348824717077 : Nat.Prime 16764676135348824717077 := by
  apply lucas_primality 16764676135348824717077 (2 : ZMod 16764676135348824717077)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (149, 1), (4018378747686678983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (149, 1), (4018378747686678983, 1)] : List FactorBlock).map factorBlockValue).prod) = 16764676135348824717077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_149
      · exact prime_thirtyNineAK_4018378747686678983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 16764676135348824717077) ^ 8382338067674412358538 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 16764676135348824717077) ^ 2394953733621260673868 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 16764676135348824717077) ^ 112514604935227011524 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 16764676135348824717077) ^ 4172 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_19932599670765751418347 : Nat.Prime 19932599670765751418347 := by
  apply lucas_primality 19932599670765751418347 (2 : ZMod 19932599670765751418347)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19430861, 1), (56990096752577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19430861, 1), (56990096752577, 1)] : List FactorBlock).map factorBlockValue).prod) = 19932599670765751418347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_19430861
      · exact prime_thirtyNineAK_56990096752577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 19932599670765751418347) ^ 9966299835382875709173 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 19932599670765751418347) ^ 6644199890255250472782 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 19932599670765751418347) ^ 1025821741546386 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 19932599670765751418347) ^ 349755498 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_24026509006479235936343 : Nat.Prime 24026509006479235936343 := by
  apply lucas_primality 24026509006479235936343 (5 : ZMod 24026509006479235936343)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (924096500249201382167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (924096500249201382167, 1)] : List FactorBlock).map factorBlockValue).prod) = 24026509006479235936343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_13
      · exact prime_thirtyNineAK_924096500249201382167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 24026509006479235936343) ^ 12013254503239617968171 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 24026509006479235936343) ^ 1848193000498402764334 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 24026509006479235936343) ^ 26 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_48053018012958471872687 : Nat.Prime 48053018012958471872687 := by
  apply lucas_primality 48053018012958471872687 (5 : ZMod 48053018012958471872687)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (24026509006479235936343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (24026509006479235936343, 1)] : List FactorBlock).map factorBlockValue).prod) = 48053018012958471872687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_24026509006479235936343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 48053018012958471872687) ^ 24026509006479235936343 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 48053018012958471872687) ^ 2 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_83275072748569715133691 : Nat.Prime 83275072748569715133691 := by
  apply lucas_primality 83275072748569715133691 (3 : ZMod 83275072748569715133691)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (11783, 1), (78526571000188327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (11783, 1), (78526571000188327, 1)] : List FactorBlock).map factorBlockValue).prod) = 83275072748569715133691 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_11783
      · exact prime_thirtyNineAK_78526571000188327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 83275072748569715133691) ^ 41637536374284857566845 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 83275072748569715133691) ^ 27758357582856571711230 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 83275072748569715133691) ^ 16655014549713943026738 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 83275072748569715133691) ^ 7067391390016949430 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 83275072748569715133691) ^ 1060470 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_93537377657792856412721 : Nat.Prime 93537377657792856412721 := by
  apply lucas_primality 93537377657792856412721 (3 : ZMod 93537377657792856412721)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (61, 1), (104009, 1), (184286892688891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (61, 1), (104009, 1), (184286892688891, 1)] : List FactorBlock).map factorBlockValue).prod) = 93537377657792856412721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_61
      · exact prime_thirtyNineAK_104009
      · exact prime_thirtyNineAK_184286892688891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 93537377657792856412721) ^ 46768688828896428206360 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 93537377657792856412721) ^ 18707475531558571282544 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 93537377657792856412721) ^ 1533399633734309121520 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 93537377657792856412721) ^ 899320036321788080 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 93537377657792856412721) ^ 507563920 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_139027313372561641588853 : Nat.Prime 139027313372561641588853 := by
  apply lucas_primality 139027313372561641588853 (2 : ZMod 139027313372561641588853)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (107, 1), (6203, 1), (3080389673224709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (107, 1), (6203, 1), (3080389673224709, 1)] : List FactorBlock).map factorBlockValue).prod) = 139027313372561641588853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_17
      · exact prime_thirtyNineAK_107
      · exact prime_thirtyNineAK_6203
      · exact prime_thirtyNineAK_3080389673224709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 139027313372561641588853) ^ 69513656686280820794426 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 139027313372561641588853) ^ 8178077257209508328756 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 139027313372561641588853) ^ 1299320685724875155036 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 139027313372561641588853) ^ 22412915262382982684 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 139027313372561641588853) ^ 45133028 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_156290153414402065070413 : Nat.Prime 156290153414402065070413 := by
  apply lucas_primality 156290153414402065070413 (13 : ZMod 156290153414402065070413)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (61343, 1), (113167, 1), (625380452107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (61343, 1), (113167, 1), (625380452107, 1)] : List FactorBlock).map factorBlockValue).prod) = 156290153414402065070413 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_61343
      · exact prime_thirtyNineAK_113167
      · exact prime_thirtyNineAK_625380452107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 156290153414402065070413) ^ 78145076707201032535206 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (13 : ZMod 156290153414402065070413) ^ 52096717804800688356804 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (13 : ZMod 156290153414402065070413) ^ 2547807466449343284 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (13 : ZMod 156290153414402065070413) ^ 1381057670649589236 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (13 : ZMod 156290153414402065070413) ^ 249912118116 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_179444362855213906281521 : Nat.Prime 179444362855213906281521 := by
  apply lucas_primality 179444362855213906281521 (3 : ZMod 179444362855213906281521)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (13, 2), (19, 2), (1883989, 1), (19514955419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (13, 2), (19, 2), (1883989, 1), (19514955419, 1)] : List FactorBlock).map factorBlockValue).prod) = 179444362855213906281521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_13
      · exact prime_thirtyNineAK_19
      · exact prime_thirtyNineAK_1883989
      · exact prime_thirtyNineAK_19514955419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 179444362855213906281521) ^ 89722181427606953140760 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 179444362855213906281521) ^ 35888872571042781256304 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 179444362855213906281521) ^ 13803412527324146637040 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 179444362855213906281521) ^ 9444440150274416120080 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 179444362855213906281521) ^ 95247033212621680 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 179444362855213906281521) ^ 9195222792080 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_358786794073783525530247 : Nat.Prime 358786794073783525530247 := by
  apply lucas_primality 358786794073783525530247 (5 : ZMod 358786794073783525530247)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19932599670765751418347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19932599670765751418347, 1)] : List FactorBlock).map factorBlockValue).prod) = 358786794073783525530247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_19932599670765751418347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 358786794073783525530247) ^ 179393397036891762765123 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 358786794073783525530247) ^ 119595598024594508510082 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 358786794073783525530247) ^ 18 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_720252565412469632018731 : Nat.Prime 720252565412469632018731 := by
  apply lucas_primality 720252565412469632018731 (2 : ZMod 720252565412469632018731)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (661, 1), (2220277, 1), (5452977238001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (661, 1), (2220277, 1), (5452977238001, 1)] : List FactorBlock).map factorBlockValue).prod) = 720252565412469632018731 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_661
      · exact prime_thirtyNineAK_2220277
      · exact prime_thirtyNineAK_5452977238001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 720252565412469632018731) ^ 360126282706234816009365 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 720252565412469632018731) ^ 240084188470823210672910 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 720252565412469632018731) ^ 144050513082493926403746 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 720252565412469632018731) ^ 1089640794875143164930 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 720252565412469632018731) ^ 324397615888679490 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 720252565412469632018731) ^ 132084278730 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_1121040809141990479770073 : Nat.Prime 1121040809141990479770073 := by
  apply lucas_primality 1121040809141990479770073 (5 : ZMod 1121040809141990479770073)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (1733, 1), (1801, 1), (39581, 1), (19900204619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (1733, 1), (1801, 1), (39581, 1), (19900204619, 1)] : List FactorBlock).map factorBlockValue).prod) = 1121040809141990479770073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_19
      · exact prime_thirtyNineAK_1733
      · exact prime_thirtyNineAK_1801
      · exact prime_thirtyNineAK_39581
      · exact prime_thirtyNineAK_19900204619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1121040809141990479770073) ^ 560520404570995239885036 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1121040809141990479770073) ^ 373680269713996826590024 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1121040809141990479770073) ^ 59002147849578446303688 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1121040809141990479770073) ^ 646878712718978926584 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1121040809141990479770073) ^ 622454641389222920472 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1121040809141990479770073) ^ 28322700516459677112 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1121040809141990479770073) ^ 56333129764488 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_3542712906646951089738233 : Nat.Prime 3542712906646951089738233 := by
  apply lucas_primality 3542712906646951089738233 (3 : ZMod 3542712906646951089738233)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (7307, 1), (8933, 1), (586723, 1), (680185699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (7307, 1), (8933, 1), (586723, 1), (680185699, 1)] : List FactorBlock).map factorBlockValue).prod) = 3542712906646951089738233 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_17
      · exact prime_thirtyNineAK_7307
      · exact prime_thirtyNineAK_8933
      · exact prime_thirtyNineAK_586723
      · exact prime_thirtyNineAK_680185699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3542712906646951089738233) ^ 1771356453323475544869116 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3542712906646951089738233) ^ 208394876861585358219896 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3542712906646951089738233) ^ 484838224530854124776 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3542712906646951089738233) ^ 396587138323849892504 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3542712906646951089738233) ^ 6038135383557404584 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3542712906646951089738233) ^ 5208449562899368 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_9175802682589068344864299 : Nat.Prime 9175802682589068344864299 := by
  apply lucas_primality 9175802682589068344864299 (3 : ZMod 9175802682589068344864299)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (139027313372561641588853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (139027313372561641588853, 1)] : List FactorBlock).map factorBlockValue).prod) = 9175802682589068344864299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_11
      · exact prime_thirtyNineAK_139027313372561641588853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9175802682589068344864299) ^ 4587901341294534172432149 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 9175802682589068344864299) ^ 3058600894196356114954766 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 9175802682589068344864299) ^ 834163880235369849533118 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (3 : ZMod 9175802682589068344864299) ^ 66 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_16976586332846122397990833 : Nat.Prime 16976586332846122397990833 := by
  apply lucas_primality 16976586332846122397990833 (5 : ZMod 16976586332846122397990833)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (3089, 1), (114496238890998451481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (3089, 1), (114496238890998451481, 1)] : List FactorBlock).map factorBlockValue).prod) = 16976586332846122397990833 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_3089
      · exact prime_thirtyNineAK_114496238890998451481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 16976586332846122397990833) ^ 8488293166423061198995416 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 16976586332846122397990833) ^ 5658862110948707465996944 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 16976586332846122397990833) ^ 5495819466767925671088 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 16976586332846122397990833) ^ 148272 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_26979759204218881470417263 : Nat.Prime 26979759204218881470417263 := by
  apply lucas_primality 26979759204218881470417263 (5 : ZMod 26979759204218881470417263)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4113109993, 1), (3279727414308767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4113109993, 1), (3279727414308767, 1)] : List FactorBlock).map factorBlockValue).prod) = 26979759204218881470417263 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_4113109993
      · exact prime_thirtyNineAK_3279727414308767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 26979759204218881470417263) ^ 13489879602109440735208631 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 26979759204218881470417263) ^ 6559454828617534 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (5 : ZMod 26979759204218881470417263) ^ 8226219986 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_44377678999047226595710397 : Nat.Prime 44377678999047226595710397 := by
  apply lucas_primality 44377678999047226595710397 (2 : ZMod 44377678999047226595710397)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (751, 1), (1459, 1), (1607, 1), (15733, 1), (252869, 1), (1583749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (751, 1), (1459, 1), (1607, 1), (15733, 1), (252869, 1), (1583749, 1)] : List FactorBlock).map factorBlockValue).prod) = 44377678999047226595710397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_751
      · exact prime_thirtyNineAK_1459
      · exact prime_thirtyNineAK_1607
      · exact prime_thirtyNineAK_15733
      · exact prime_thirtyNineAK_252869
      · exact prime_thirtyNineAK_1583749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 44377678999047226595710397) ^ 22188839499523613297855198 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 44377678999047226595710397) ^ 59091450065309223163396 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 44377678999047226595710397) ^ 30416503769052245781844 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 44377678999047226595710397) ^ 27615232731205492592228 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 44377678999047226595710397) ^ 2820674950679922875212 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 44377678999047226595710397) ^ 175496715686965292684 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (2 : ZMod 44377678999047226595710397) ^ 28020651630433374604 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_536144284651279865499338401 : Nat.Prime 536144284651279865499338401 := by
  apply lucas_primality 536144284651279865499338401 (73 : ZMod 536144284651279865499338401)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 4), (5, 2), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 4), (5, 2), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 536144284651279865499338401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_11
      · exact prime_thirtyNineAK_13
      · exact prime_thirtyNineAK_17
      · exact prime_thirtyNineAK_19
      · exact prime_thirtyNineAK_23
      · exact prime_thirtyNineAK_29
      · exact prime_thirtyNineAK_31
      · exact prime_thirtyNineAK_37
      · exact prime_thirtyNineAK_41
      · exact prime_thirtyNineAK_47
      · exact prime_thirtyNineAK_53
      · exact prime_thirtyNineAK_59
      · exact prime_thirtyNineAK_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (73 : ZMod 536144284651279865499338401) ^ 268072142325639932749669200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (73 : ZMod 536144284651279865499338401) ^ 178714761550426621833112800 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (73 : ZMod 536144284651279865499338401) ^ 107228856930255973099867680 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (73 : ZMod 536144284651279865499338401) ^ 76592040664468552214191200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (73 : ZMod 536144284651279865499338401) ^ 48740389513752715045394400 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (73 : ZMod 536144284651279865499338401) ^ 41241868050098451192256800 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (73 : ZMod 536144284651279865499338401) ^ 31537899097134109735255200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (73 : ZMod 536144284651279865499338401) ^ 28218120244804203447333600 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (73 : ZMod 536144284651279865499338401) ^ 23310621071794776760840800 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (73 : ZMod 536144284651279865499338401) ^ 18487733953492409155149600 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (73 : ZMod 536144284651279865499338401) ^ 17294976924234834370946400 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (73 : ZMod 536144284651279865499338401) ^ 14490386071656212581063200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (73 : ZMod 536144284651279865499338401) ^ 13076689869543411353642400 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (73 : ZMod 536144284651279865499338401) ^ 11407325205346380117007200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (73 : ZMod 536144284651279865499338401) ^ 10115929899080752179232800 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (73 : ZMod 536144284651279865499338401) ^ 9087191265275929923717600 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (73 : ZMod 536144284651279865499338401) ^ 8789250568053768286874400 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_606689585263290374117672401 : Nat.Prime 606689585263290374117672401 := by
  apply lucas_primality 606689585263290374117672401 (101 : ZMod 606689585263290374117672401)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (5, 2), (7, 2), (11, 1), (13, 2), (17, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (5, 2), (7, 2), (11, 1), (13, 2), (17, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 606689585263290374117672401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_11
      · exact prime_thirtyNineAK_13
      · exact prime_thirtyNineAK_17
      · exact prime_thirtyNineAK_23
      · exact prime_thirtyNineAK_29
      · exact prime_thirtyNineAK_31
      · exact prime_thirtyNineAK_37
      · exact prime_thirtyNineAK_41
      · exact prime_thirtyNineAK_43
      · exact prime_thirtyNineAK_47
      · exact prime_thirtyNineAK_53
      · exact prime_thirtyNineAK_59
      · exact prime_thirtyNineAK_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (101 : ZMod 606689585263290374117672401) ^ 303344792631645187058836200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (101 : ZMod 606689585263290374117672401) ^ 202229861754430124705890800 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (101 : ZMod 606689585263290374117672401) ^ 121337917052658074823534480 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (101 : ZMod 606689585263290374117672401) ^ 86669940751898624873953200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (101 : ZMod 606689585263290374117672401) ^ 55153598660299124919788400 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (101 : ZMod 606689585263290374117672401) ^ 46668429635637721085974800 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (101 : ZMod 606689585263290374117672401) ^ 35687622662546492595157200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (101 : ZMod 606689585263290374117672401) ^ 26377808054925668439898800 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (101 : ZMod 606689585263290374117672401) ^ 20920330526320357728195600 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (101 : ZMod 606689585263290374117672401) ^ 19570631782686786261860400 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (101 : ZMod 606689585263290374117672401) ^ 16397015817926766868045200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (101 : ZMod 606689585263290374117672401) ^ 14797306957641228637016400 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (101 : ZMod 606689585263290374117672401) ^ 14109060122402101723666800 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (101 : ZMod 606689585263290374117672401) ^ 12908289048155114342929200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (101 : ZMod 606689585263290374117672401) ^ 11446973306854535360710800 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (101 : ZMod 606689585263290374117672401) ^ 10282874326496447018943600 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (101 : ZMod 606689585263290374117672401) ^ 9945730905955579903568400 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_678064830588383359307986801 : Nat.Prime 678064830588383359307986801 := by
  apply lucas_primality 678064830588383359307986801 (278 : ZMod 678064830588383359307986801)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (5, 2), (7, 2), (11, 1), (13, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (5, 2), (7, 2), (11, 1), (13, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 678064830588383359307986801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_11
      · exact prime_thirtyNineAK_13
      · exact prime_thirtyNineAK_19
      · exact prime_thirtyNineAK_23
      · exact prime_thirtyNineAK_29
      · exact prime_thirtyNineAK_31
      · exact prime_thirtyNineAK_37
      · exact prime_thirtyNineAK_41
      · exact prime_thirtyNineAK_43
      · exact prime_thirtyNineAK_47
      · exact prime_thirtyNineAK_53
      · exact prime_thirtyNineAK_59
      · exact prime_thirtyNineAK_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (278 : ZMod 678064830588383359307986801) ^ 339032415294191679653993400 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (278 : ZMod 678064830588383359307986801) ^ 226021610196127786435995600 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (278 : ZMod 678064830588383359307986801) ^ 135612966117676671861597360 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (278 : ZMod 678064830588383359307986801) ^ 96866404369769051329712400 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (278 : ZMod 678064830588383359307986801) ^ 61642257326216669027998800 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (278 : ZMod 678064830588383359307986801) ^ 52158833122183335331383600 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (278 : ZMod 678064830588383359307986801) ^ 35687622662546492595157200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (278 : ZMod 678064830588383359307986801) ^ 29481079590799276491651600 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (278 : ZMod 678064830588383359307986801) ^ 23381545882358046872689200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (278 : ZMod 678064830588383359307986801) ^ 21873059051238172880902800 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (278 : ZMod 678064830588383359307986801) ^ 18326076502388739440756400 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (278 : ZMod 678064830588383359307986801) ^ 16538166599716667300194800 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (278 : ZMod 678064830588383359307986801) ^ 15768949548567054867627600 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (278 : ZMod 678064830588383359307986801) ^ 14426911289114539559744400 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (278 : ZMod 678064830588383359307986801) ^ 12793676048837421873735600 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (278 : ZMod 678064830588383359307986801) ^ 11492624247260734903525200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (278 : ZMod 678064830588383359307986801) ^ 11115816894891530480458800 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_823364437143036936302555401 : Nat.Prime 823364437143036936302555401 := by
  apply lucas_primality 823364437143036936302555401 (113 : ZMod 823364437143036936302555401)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (5, 2), (7, 1), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (5, 2), (7, 1), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 823364437143036936302555401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_11
      · exact prime_thirtyNineAK_13
      · exact prime_thirtyNineAK_17
      · exact prime_thirtyNineAK_19
      · exact prime_thirtyNineAK_23
      · exact prime_thirtyNineAK_29
      · exact prime_thirtyNineAK_31
      · exact prime_thirtyNineAK_37
      · exact prime_thirtyNineAK_41
      · exact prime_thirtyNineAK_43
      · exact prime_thirtyNineAK_47
      · exact prime_thirtyNineAK_53
      · exact prime_thirtyNineAK_59
      · exact prime_thirtyNineAK_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (113 : ZMod 823364437143036936302555401) ^ 411682218571518468151277700 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (113 : ZMod 823364437143036936302555401) ^ 274454812381012312100851800 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (113 : ZMod 823364437143036936302555401) ^ 164672887428607387260511080 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (113 : ZMod 823364437143036936302555401) ^ 117623491020433848043222200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (113 : ZMod 823364437143036936302555401) ^ 74851312467548812391141400 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (113 : ZMod 823364437143036936302555401) ^ 63335725934079764330965800 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (113 : ZMod 823364437143036936302555401) ^ 48433202184884525664856200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (113 : ZMod 823364437143036936302555401) ^ 43334970375949312436976600 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (113 : ZMod 823364437143036936302555401) ^ 35798453788827692882719800 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (113 : ZMod 823364437143036936302555401) ^ 28391877142863342631122600 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (113 : ZMod 823364437143036936302555401) ^ 26560143133646352783953400 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (113 : ZMod 823364437143036936302555401) ^ 22253092895757755035204200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (113 : ZMod 823364437143036936302555401) ^ 20082059442513096007379400 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (113 : ZMod 823364437143036936302555401) ^ 19148010166117138053547800 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (113 : ZMod 823364437143036936302555401) ^ 17518392279639083751118200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (113 : ZMod 823364437143036936302555401) ^ 15535178059302583703821800 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (113 : ZMod 823364437143036936302555401) ^ 13955329443102320954280600 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (113 : ZMod 823364437143036936302555401) ^ 13497777658082572726271400 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_838334699636546698780783681 : Nat.Prime 838334699636546698780783681 := by
  apply lucas_primality 838334699636546698780783681 (83 : ZMod 838334699636546698780783681)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 4), (5, 1), (7, 2), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 4), (5, 1), (7, 2), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 838334699636546698780783681 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_13
      · exact prime_thirtyNineAK_17
      · exact prime_thirtyNineAK_19
      · exact prime_thirtyNineAK_23
      · exact prime_thirtyNineAK_29
      · exact prime_thirtyNineAK_31
      · exact prime_thirtyNineAK_37
      · exact prime_thirtyNineAK_41
      · exact prime_thirtyNineAK_43
      · exact prime_thirtyNineAK_47
      · exact prime_thirtyNineAK_53
      · exact prime_thirtyNineAK_59
      · exact prime_thirtyNineAK_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (83 : ZMod 838334699636546698780783681) ^ 419167349818273349390391840 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (83 : ZMod 838334699636546698780783681) ^ 279444899878848899593594560 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (83 : ZMod 838334699636546698780783681) ^ 167666939927309339756156736 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (83 : ZMod 838334699636546698780783681) ^ 119762099948078099825826240 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (83 : ZMod 838334699636546698780783681) ^ 64487284587426669136983360 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (83 : ZMod 838334699636546698780783681) ^ 49313805860973335222399040 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (83 : ZMod 838334699636546698780783681) ^ 44122878928239299935830720 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (83 : ZMod 838334699636546698780783681) ^ 36449334766806378207860160 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (83 : ZMod 838334699636546698780783681) ^ 28908093090915403406233920 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (83 : ZMod 838334699636546698780783681) ^ 27043054826985377380025280 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (83 : ZMod 838334699636546698780783681) ^ 22657694584771532399480640 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (83 : ZMod 838334699636546698780783681) ^ 20447187796013334116604480 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (83 : ZMod 838334699636546698780783681) ^ 19496155805501086018157760 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (83 : ZMod 838334699636546698780783681) ^ 17836908502905248910229440 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (83 : ZMod 838334699636546698780783681) ^ 15817635842198994316618560 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (83 : ZMod 838334699636546698780783681) ^ 14209062705704181335267520 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (83 : ZMod 838334699636546698780783681) ^ 13743191797320437684930880 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_869969971320944687414020801 : Nat.Prime 869969971320944687414020801 := by
  apply lucas_primality 869969971320944687414020801 (53 : ZMod 869969971320944687414020801)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 4), (5, 2), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 4), (5, 2), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 869969971320944687414020801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_11
      · exact prime_thirtyNineAK_13
      · exact prime_thirtyNineAK_17
      · exact prime_thirtyNineAK_19
      · exact prime_thirtyNineAK_23
      · exact prime_thirtyNineAK_29
      · exact prime_thirtyNineAK_31
      · exact prime_thirtyNineAK_37
      · exact prime_thirtyNineAK_41
      · exact prime_thirtyNineAK_43
      · exact prime_thirtyNineAK_47
      · exact prime_thirtyNineAK_59
      · exact prime_thirtyNineAK_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (53 : ZMod 869969971320944687414020801) ^ 434984985660472343707010400 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (53 : ZMod 869969971320944687414020801) ^ 289989990440314895804673600 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (53 : ZMod 869969971320944687414020801) ^ 173993994264188937482804160 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (53 : ZMod 869969971320944687414020801) ^ 124281424474420669630574400 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (53 : ZMod 869969971320944687414020801) ^ 79088179210994971583092800 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (53 : ZMod 869969971320944687414020801) ^ 66920767024688052878001600 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (53 : ZMod 869969971320944687414020801) ^ 51174704195349687494942400 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (53 : ZMod 869969971320944687414020801) ^ 45787893227418141442843200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (53 : ZMod 869969971320944687414020801) ^ 37824781361780203800609600 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (53 : ZMod 869969971320944687414020801) ^ 29998964528308437497035200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (53 : ZMod 869969971320944687414020801) ^ 28063547461965957658516800 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (53 : ZMod 869969971320944687414020801) ^ 23512701927593099659838400 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (53 : ZMod 869969971320944687414020801) ^ 21218779788315724083268800 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (53 : ZMod 869969971320944687414020801) ^ 20231859798161504358465600 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (53 : ZMod 869969971320944687414020801) ^ 18509999389807333774766400 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (53 : ZMod 869969971320944687414020801) ^ 14745253751202452329051200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (53 : ZMod 869969971320944687414020801) ^ 14261802808540076842852800 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_1002356706087175400716154401 : Nat.Prime 1002356706087175400716154401 := by
  apply lucas_primality 1002356706087175400716154401 (69 : ZMod 1002356706087175400716154401)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 4), (5, 2), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 4), (5, 2), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1002356706087175400716154401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_11
      · exact prime_thirtyNineAK_13
      · exact prime_thirtyNineAK_17
      · exact prime_thirtyNineAK_19
      · exact prime_thirtyNineAK_29
      · exact prime_thirtyNineAK_31
      · exact prime_thirtyNineAK_37
      · exact prime_thirtyNineAK_41
      · exact prime_thirtyNineAK_43
      · exact prime_thirtyNineAK_47
      · exact prime_thirtyNineAK_53
      · exact prime_thirtyNineAK_59
      · exact prime_thirtyNineAK_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (69 : ZMod 1002356706087175400716154401) ^ 501178353043587700358077200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (69 : ZMod 1002356706087175400716154401) ^ 334118902029058466905384800 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (69 : ZMod 1002356706087175400716154401) ^ 200471341217435080143230880 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (69 : ZMod 1002356706087175400716154401) ^ 143193815155310771530879200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (69 : ZMod 1002356706087175400716154401) ^ 91123336917015945519650400 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (69 : ZMod 1002356706087175400716154401) ^ 77104362006705800055088800 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (69 : ZMod 1002356706087175400716154401) ^ 58962159181598552983303200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (69 : ZMod 1002356706087175400716154401) ^ 52755616109851336879797600 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (69 : ZMod 1002356706087175400716154401) ^ 34564024347833634507453600 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (69 : ZMod 1002356706087175400716154401) ^ 32334087293134690345682400 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (69 : ZMod 1002356706087175400716154401) ^ 27090721786139875695031200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (69 : ZMod 1002356706087175400716154401) ^ 24447724538711595139418400 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (69 : ZMod 1002356706087175400716154401) ^ 23310621071794776760840800 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (69 : ZMod 1002356706087175400716154401) ^ 21326738427386710653535200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (69 : ZMod 1002356706087175400716154401) ^ 18912390680890101900304800 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (69 : ZMod 1002356706087175400716154401) ^ 16989096713341955944341600 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (69 : ZMod 1002356706087175400716154401) ^ 16432077148970088536330400 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_1024631299555779298509846721 : Nat.Prime 1024631299555779298509846721 := by
  apply lucas_primality 1024631299555779298509846721 (67 : ZMod 1024631299555779298509846721)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 1), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 1), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1024631299555779298509846721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_11
      · exact prime_thirtyNineAK_13
      · exact prime_thirtyNineAK_17
      · exact prime_thirtyNineAK_19
      · exact prime_thirtyNineAK_23
      · exact prime_thirtyNineAK_29
      · exact prime_thirtyNineAK_31
      · exact prime_thirtyNineAK_37
      · exact prime_thirtyNineAK_41
      · exact prime_thirtyNineAK_43
      · exact prime_thirtyNineAK_47
      · exact prime_thirtyNineAK_53
      · exact prime_thirtyNineAK_59
      · exact prime_thirtyNineAK_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 1024631299555779298509846721) ^ 512315649777889649254923360 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 341543766518593099503282240 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 204926259911155859701969344 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 146375899936539899787120960 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 93148299959616299864531520 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 78817792273521484500757440 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 60272429385634076382932160 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 53927963134514699921570880 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 44549186937207795587384640 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 35332113777785493052063680 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 33052622566315461242253120 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 27692737825831872932698560 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 24991007306238519475849920 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 23828634873390216244415040 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 21800665947995304223613760 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 19332666029354326386978240 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 17366632195860666076438080 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 16797234418947201614915520 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_3293457748572147745210221601 : Nat.Prime 3293457748572147745210221601 := by
  apply lucas_primality 3293457748572147745210221601 (149 : ZMod 3293457748572147745210221601)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 4), (5, 2), (7, 1), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 4), (5, 2), (7, 1), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 3293457748572147745210221601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_11
      · exact prime_thirtyNineAK_13
      · exact prime_thirtyNineAK_17
      · exact prime_thirtyNineAK_19
      · exact prime_thirtyNineAK_23
      · exact prime_thirtyNineAK_29
      · exact prime_thirtyNineAK_31
      · exact prime_thirtyNineAK_37
      · exact prime_thirtyNineAK_41
      · exact prime_thirtyNineAK_43
      · exact prime_thirtyNineAK_47
      · exact prime_thirtyNineAK_53
      · exact prime_thirtyNineAK_59
      · exact prime_thirtyNineAK_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (149 : ZMod 3293457748572147745210221601) ^ 1646728874286073872605110800 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (149 : ZMod 3293457748572147745210221601) ^ 1097819249524049248403407200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (149 : ZMod 3293457748572147745210221601) ^ 658691549714429549042044320 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (149 : ZMod 3293457748572147745210221601) ^ 470493964081735392172888800 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (149 : ZMod 3293457748572147745210221601) ^ 299405249870195249564565600 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (149 : ZMod 3293457748572147745210221601) ^ 253342903736319057323863200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (149 : ZMod 3293457748572147745210221601) ^ 193732808739538102659424800 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (149 : ZMod 3293457748572147745210221601) ^ 173339881503797249747906400 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (149 : ZMod 3293457748572147745210221601) ^ 143193815155310771530879200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (149 : ZMod 3293457748572147745210221601) ^ 113567508571453370524490400 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (149 : ZMod 3293457748572147745210221601) ^ 106240572534585411135813600 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (149 : ZMod 3293457748572147745210221601) ^ 89012371583031020140816800 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (149 : ZMod 3293457748572147745210221601) ^ 80328237770052384029517600 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (149 : ZMod 3293457748572147745210221601) ^ 76592040664468552214191200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (149 : ZMod 3293457748572147745210221601) ^ 70073569118556335004472800 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (149 : ZMod 3293457748572147745210221601) ^ 62140712237210334815287200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (149 : ZMod 3293457748572147745210221601) ^ 55821317772409283817122400 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (149 : ZMod 3293457748572147745210221601) ^ 53991110632330290905085600 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem prime_thirtyNineAK_23054204240005034216471551201 : Nat.Prime 23054204240005034216471551201 := by
  apply lucas_primality 23054204240005034216471551201 (142 : ZMod 23054204240005034216471551201)
  · rw [← thirtyNineAKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 4), (5, 2), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 4), (5, 2), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 23054204240005034216471551201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyNineAK_2
      · exact prime_thirtyNineAK_3
      · exact prime_thirtyNineAK_5
      · exact prime_thirtyNineAK_7
      · exact prime_thirtyNineAK_11
      · exact prime_thirtyNineAK_13
      · exact prime_thirtyNineAK_17
      · exact prime_thirtyNineAK_19
      · exact prime_thirtyNineAK_23
      · exact prime_thirtyNineAK_29
      · exact prime_thirtyNineAK_31
      · exact prime_thirtyNineAK_37
      · exact prime_thirtyNineAK_41
      · exact prime_thirtyNineAK_43
      · exact prime_thirtyNineAK_47
      · exact prime_thirtyNineAK_53
      · exact prime_thirtyNineAK_59
      · exact prime_thirtyNineAK_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (142 : ZMod 23054204240005034216471551201) ^ 11527102120002517108235775600 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (142 : ZMod 23054204240005034216471551201) ^ 7684734746668344738823850400 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (142 : ZMod 23054204240005034216471551201) ^ 4610840848001006843294310240 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (142 : ZMod 23054204240005034216471551201) ^ 3293457748572147745210221600 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (142 : ZMod 23054204240005034216471551201) ^ 2095836749091366746951959200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (142 : ZMod 23054204240005034216471551201) ^ 1773400326154233401267042400 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (142 : ZMod 23054204240005034216471551201) ^ 1356129661176766718615973600 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (142 : ZMod 23054204240005034216471551201) ^ 1213379170526580748235344800 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (142 : ZMod 23054204240005034216471551201) ^ 1002356706087175400716154400 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (142 : ZMod 23054204240005034216471551201) ^ 794972560000173593671432800 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (142 : ZMod 23054204240005034216471551201) ^ 743684007742097877950695200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (142 : ZMod 23054204240005034216471551201) ^ 623086601081217140985717600 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (142 : ZMod 23054204240005034216471551201) ^ 562297664390366688206623200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (142 : ZMod 23054204240005034216471551201) ^ 536144284651279865499338400 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (142 : ZMod 23054204240005034216471551201) ^ 490514983829894345031309600 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (142 : ZMod 23054204240005034216471551201) ^ 434984985660472343707010400 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (142 : ZMod 23054204240005034216471551201) ^ 390749224406864986719856800 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide
    · change (142 : ZMod 23054204240005034216471551201) ^ 377937774426312036335599200 ≠ 1
      rw [← thirtyNineAKFastPow_eq_pow]
      decide

private theorem phi_thirtyNineAK_46108408480010068432943102400 : Nat.totient 46108408480010068432943102400 = 6067283369915064936038400000 := by
  rw [← show ((([(2, 6), (3, 4), (5, 2), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102400 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_3, prime_thirtyNineAK_5, prime_thirtyNineAK_7, prime_thirtyNineAK_11, prime_thirtyNineAK_13, prime_thirtyNineAK_17, prime_thirtyNineAK_19, prime_thirtyNineAK_23, prime_thirtyNineAK_29, prime_thirtyNineAK_31, prime_thirtyNineAK_37, prime_thirtyNineAK_41, prime_thirtyNineAK_43, prime_thirtyNineAK_47, prime_thirtyNineAK_53, prime_thirtyNineAK_59, prime_thirtyNineAK_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102401 : Nat.totient 46108408480010068432943102401 = 46100034361125112842714105840 := by
  rw [← show ((([(5507, 1), (32282021, 1), (259360801617151183, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102401 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_5507, prime_thirtyNineAK_32282021, prime_thirtyNineAK_259360801617151183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102402 : Nat.totient 46108408480010068432943102402 = 23054204240005034216471551200 := by
  rw [← show ((([(2, 1), (23054204240005034216471551201, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102402 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_23054204240005034216471551201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102403 : Nat.totient 46108408480010068432943102403 = 30707629550436305478170016000 := by
  rw [← show ((([(3, 1), (1021, 1), (25951, 1), (1582963, 1), (366444555641737, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102403 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_3, prime_thirtyNineAK_1021, prime_thirtyNineAK_25951, prime_thirtyNineAK_1582963, prime_thirtyNineAK_366444555641737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102404 : Nat.totient 46108408480010068432943102404 = 23054145761131879181242271040 := by
  rw [← show ((([(2, 2), (774811, 1), (802603, 1), (18536322812665897, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102404 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_774811, prime_thirtyNineAK_802603, prime_thirtyNineAK_18536322812665897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102405 : Nat.totient 46108408480010068432943102405 = 36886723287822421429108757328 := by
  rw [← show ((([(5, 1), (10550563, 1), (874046408329300880587, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102405 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_5, prime_thirtyNineAK_10550563, prime_thirtyNineAK_874046408329300880587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102406 : Nat.totient 46108408480010068432943102406 = 15365941854818408187346172160 := by
  rw [← show ((([(2, 1), (3, 1), (4357, 1), (148272073, 1), (11895479753831941, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102406 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_3, prime_thirtyNineAK_4357, prime_thirtyNineAK_148272073, prime_thirtyNineAK_11895479753831941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102407 : Nat.totient 46108408480010068432943102407 = 39521442655521306212338673568 := by
  rw [← show ((([(7, 1), (999007, 1), (3670757, 1), (1796213371168499, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102407 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_7, prime_thirtyNineAK_999007, prime_thirtyNineAK_3670757, prime_thirtyNineAK_1796213371168499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102408 : Nat.totient 46108408480010068432943102408 = 22688127020202321748743573120 := by
  rw [← show ((([(2, 3), (67, 1), (1033, 1), (83275072748569715133691, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102408 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_67, prime_thirtyNineAK_1033, prime_thirtyNineAK_83275072748569715133691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102409 : Nat.totient 46108408480010068432943102409 = 30737933189147929194211380192 := by
  rw [← show ((([(3, 2), (32029, 1), (667123, 1), (239766403692867703, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102409 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_3, prime_thirtyNineAK_32029, prime_thirtyNineAK_667123, prime_thirtyNineAK_239766403692867703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102410 : Nat.totient 46108408480010068432943102410 = 18443363391997224978503872528 := by
  rw [← show ((([(2, 1), (5, 1), (2715641050583, 1), (1697883027291527, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102410 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_5, prime_thirtyNineAK_2715641050583, prime_thirtyNineAK_1697883027291527]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102411 : Nat.totient 46108408480010068432943102411 = 41700013054877565733216445280 := by
  rw [← show ((([(11, 1), (197, 1), (10567, 1), (2013582894636896829899, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102411 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_11, prime_thirtyNineAK_197, prime_thirtyNineAK_10567, prime_thirtyNineAK_2013582894636896829899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102412 : Nat.totient 46108408480010068432943102412 = 15282684364083763761154944000 := by
  rw [← show ((([(2, 2), (3, 1), (199, 1), (2311, 1), (5209, 1), (1603952514074243401, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102412 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_3, prime_thirtyNineAK_199, prime_thirtyNineAK_2311, prime_thirtyNineAK_5209, prime_thirtyNineAK_1603952514074243401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102413 : Nat.totient 46108408480010068432943102413 = 42561607826302883872064713200 := by
  rw [← show ((([(13, 1), (30429025931, 1), (116559782766332771, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102413 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_13, prime_thirtyNineAK_30429025931, prime_thirtyNineAK_116559782766332771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102414 : Nat.totient 46108408480010068432943102414 = 19760746491432886471261329600 := by
  rw [← show ((([(2, 1), (7, 1), (3293457748572147745210221601, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102414 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_7, prime_thirtyNineAK_3293457748572147745210221601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102415 : Nat.totient 46108408480010068432943102415 = 24584937619510218369731659776 := by
  rw [← show ((([(3, 1), (5, 1), (4093, 1), (119653, 1), (6276586759550679409, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102415 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_3, prime_thirtyNineAK_5, prime_thirtyNineAK_4093, prime_thirtyNineAK_119653, prime_thirtyNineAK_6276586759550679409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102416 : Nat.totient 46108408480010068432943102416 = 23033663835544285936370319360 := by
  rw [← show ((([(2, 4), (1933, 1), (3041, 1), (22229, 1), (148364669, 1), (148648817, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102416 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_1933, prime_thirtyNineAK_3041, prime_thirtyNineAK_22229, prime_thirtyNineAK_148364669, prime_thirtyNineAK_148648817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102417 : Nat.totient 46108408480010068432943102417 = 43171023082311609646865891328 := by
  rw [← show ((([(17, 1), (193, 1), (159779, 1), (8042669, 1), (10935886832407, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102417 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_17, prime_thirtyNineAK_193, prime_thirtyNineAK_159779, prime_thirtyNineAK_8042669, prime_thirtyNineAK_10935886832407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102418 : Nat.totient 46108408480010068432943102418 = 15354238095835820078293468800 := by
  rw [← show ((([(2, 1), (3, 2), (1093, 1), (21611, 1), (39791, 1), (209623, 1), (13001360959, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102418 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_3, prime_thirtyNineAK_1093, prime_thirtyNineAK_21611, prime_thirtyNineAK_39791, prime_thirtyNineAK_209623, prime_thirtyNineAK_13001360959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102419 : Nat.totient 46108408480010068432943102419 = 43681641253644098690887680000 := by
  rw [← show ((([(19, 1), (4921601, 1), (4644344281, 1), (106168510121, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102419 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_19, prime_thirtyNineAK_4921601, prime_thirtyNineAK_4644344281, prime_thirtyNineAK_106168510121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102420 : Nat.totient 46108408480010068432943102420 = 18330213923290621334510663040 := by
  rw [← show ((([(2, 2), (5, 1), (163, 1), (364181272591, 1), (38836932723637, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102420 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_5, prime_thirtyNineAK_163, prime_thirtyNineAK_364181272591, prime_thirtyNineAK_38836932723637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102421 : Nat.totient 46108408480010068432943102421 = 26347661988215578344867920448 := by
  rw [← show ((([(3, 1), (7, 1), (72863556869, 1), (30133561870930829, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102421 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_3, prime_thirtyNineAK_7, prime_thirtyNineAK_72863556869, prime_thirtyNineAK_30133561870930829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102422 : Nat.totient 46108408480010068432943102422 = 20685310706529995695141667200 := by
  rw [← show ((([(2, 1), (11, 1), (107, 1), (269, 1), (106019267, 1), (686809978352741, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102422 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_11, prime_thirtyNineAK_107, prime_thirtyNineAK_269, prime_thirtyNineAK_106019267, prime_thirtyNineAK_686809978352741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102423 : Nat.totient 46108408480010068432943102423 = 44032423376936444388521394240 := by
  rw [← show ((([(23, 1), (619, 2), (2692367, 1), (8411981, 1), (231014083, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102423 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_23, prime_thirtyNineAK_619, prime_thirtyNineAK_2692367, prime_thirtyNineAK_8411981, prime_thirtyNineAK_231014083]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102424 : Nat.totient 46108408480010068432943102424 = 15369469489921085513213540000 := by
  rw [← show ((([(2, 3), (3, 1), (4499780951, 1), (426950491054489151, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102424 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_3, prime_thirtyNineAK_4499780951, prime_thirtyNineAK_426950491054489151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102425 : Nat.totient 46108408480010068432943102425 = 36766568765765356823285585280 := by
  rw [← show ((([(5, 2), (307, 1), (6324089, 1), (949956622275315539, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102425 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_5, prime_thirtyNineAK_307, prime_thirtyNineAK_6324089, prime_thirtyNineAK_949956622275315539]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102426 : Nat.totient 46108408480010068432943102426 = 21277989704366903307463050240 := by
  rw [← show ((([(2, 1), (13, 1), (8233, 1), (93811, 1), (8274073, 1), (277508030299, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102426 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_13, prime_thirtyNineAK_8233, prime_thirtyNineAK_93811, prime_thirtyNineAK_8274073, prime_thirtyNineAK_277508030299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102427 : Nat.totient 46108408480010068432943102427 = 30725974440495954501919021800 := by
  rw [← show ((([(3, 3), (2371, 1), (720252565412469632018731, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102427 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_3, prime_thirtyNineAK_2371, prime_thirtyNineAK_720252565412469632018731]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102428 : Nat.totient 46108408480010068432943102428 = 19557027455438733002485438464 := by
  rw [← show ((([(2, 2), (7, 1), (97, 1), (16976586332846122397990833, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102428 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_7, prime_thirtyNineAK_97, prime_thirtyNineAK_16976586332846122397990833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102429 : Nat.totient 46108408480010068432943102429 = 43891427062579684905065293440 := by
  rw [← show ((([(29, 1), (71, 1), (2797999, 1), (8003431466359176569, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102429 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_29, prime_thirtyNineAK_71, prime_thirtyNineAK_2797999, prime_thirtyNineAK_8003431466359176569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102430 : Nat.totient 46108408480010068432943102430 = 12295545833460479382668220800 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (413141, 1), (3720151109024930829341, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102430 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_3, prime_thirtyNineAK_5, prime_thirtyNineAK_413141, prime_thirtyNineAK_3720151109024930829341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102431 : Nat.totient 46108408480010068432943102431 = 44595610294291116575664600000 := by
  rw [← show ((([(31, 1), (1871, 1), (28201, 1), (28189030666041590231, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102431 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_31, prime_thirtyNineAK_1871, prime_thirtyNineAK_28201, prime_thirtyNineAK_28189030666041590231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102432 : Nat.totient 46108408480010068432943102432 = 22771871648177783306757120000 := by
  rw [← show ((([(2, 5), (113, 1), (523, 1), (659, 1), (1543501, 1), (23969429172811, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102432 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_113, prime_thirtyNineAK_523, prime_thirtyNineAK_659, prime_thirtyNineAK_1543501, prime_thirtyNineAK_23969429172811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102433 : Nat.totient 46108408480010068432943102433 = 27944447496647127971048584640 := by
  rw [← show ((([(3, 1), (11, 1), (657653, 1), (2124561888099414885917, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102433 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_3, prime_thirtyNineAK_11, prime_thirtyNineAK_657653, prime_thirtyNineAK_2124561888099414885917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102434 : Nat.totient 46108408480010068432943102434 = 21695573936373637064814312192 := by
  rw [← show ((([(2, 1), (17, 1), (8677, 1), (156290153414402065070413, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102434 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_17, prime_thirtyNineAK_8677, prime_thirtyNineAK_156290153414402065070413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102435 : Nat.totient 46108408480010068432943102435 = 31617193105405360629460500480 := by
  rw [← show ((([(5, 1), (7, 1), (26146481, 1), (442966529, 1), (113743851409, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102435 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_5, prime_thirtyNineAK_7, prime_thirtyNineAK_26146481, prime_thirtyNineAK_442966529, prime_thirtyNineAK_113743851409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102436 : Nat.totient 46108408480010068432943102436 = 15369469400008283226422011200 := by
  rw [← show ((([(2, 2), (3, 2), (164681581, 1), (7777367187437459221, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102436 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_3, prime_thirtyNineAK_164681581, prime_thirtyNineAK_7777367187437459221]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102437 : Nat.totient 46108408480010068432943102437 = 44670611553711093968366780928 := by
  rw [← show ((([(37, 1), (347, 1), (809, 1), (6343, 1), (699851181472581709, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102437 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_37, prime_thirtyNineAK_347, prime_thirtyNineAK_809, prime_thirtyNineAK_6343, prime_thirtyNineAK_699851181472581709]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102438 : Nat.totient 46108408480010068432943102438 = 21541393118098868669594130240 := by
  rw [← show ((([(2, 1), (19, 1), (73, 1), (88807, 1), (187165791806578980991, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102438 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_19, prime_thirtyNineAK_73, prime_thirtyNineAK_88807, prime_thirtyNineAK_187165791806578980991]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102439 : Nat.totient 46108408480010068432943102439 = 28093315868479095348023428608 := by
  rw [← show ((([(3, 1), (13, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102439 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_3, prime_thirtyNineAK_13, prime_thirtyNineAK_103, prime_thirtyNineAK_5009, prime_thirtyNineAK_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102440 : Nat.totient 46108408480010068432943102440 = 18440360162657746010015305728 := by
  rw [← show ((([(2, 3), (5, 1), (11027, 1), (13859, 1), (7542770108201126977, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102440 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_5, prime_thirtyNineAK_11027, prime_thirtyNineAK_13859, prime_thirtyNineAK_7542770108201126977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102441 : Nat.totient 46108408480010068432943102441 = 44982467968629171675174923520 := by
  rw [← show ((([(41, 1), (34147, 1), (1616627, 1), (20372010569611529, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102441 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_41, prime_thirtyNineAK_34147, prime_thirtyNineAK_1616627, prime_thirtyNineAK_20372010569611529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102442 : Nat.totient 46108408480010068432943102442 = 13173830836539222757296502848 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (83511149, 1), (13145780685211854149, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102442 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_3, prime_thirtyNineAK_7, prime_thirtyNineAK_83511149, prime_thirtyNineAK_13145780685211854149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102443 : Nat.totient 46108408480010068432943102443 = 45036119618111344842206793216 := by
  rw [← show ((([(43, 1), (225885797, 1), (509536337, 1), (9316388509, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102443 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_43, prime_thirtyNineAK_225885797, prime_thirtyNineAK_509536337, prime_thirtyNineAK_9316388509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102444 : Nat.totient 46108408480010068432943102444 = 20688397741681351610729486400 := by
  rw [← show ((([(2, 2), (11, 1), (79, 1), (4591, 1), (124147, 1), (23273239678327147, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102444 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_11, prime_thirtyNineAK_79, prime_thirtyNineAK_4591, prime_thirtyNineAK_124147, prime_thirtyNineAK_23273239678327147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102445 : Nat.totient 46108408480010068432943102445 = 24591151189338703164236321280 := by
  rw [← show ((([(3, 2), (5, 1), (1024631299555779298509846721, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102445 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_3, prime_thirtyNineAK_5, prime_thirtyNineAK_1024631299555779298509846721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102446 : Nat.totient 46108408480010068432943102446 = 22051847533917858815755396800 := by
  rw [← show ((([(2, 1), (23, 1), (1002356706087175400716154401, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102446 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_23, prime_thirtyNineAK_1002356706087175400716154401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102447 : Nat.totient 46108408480010068432943102447 = 45127179820977828954898539168 := by
  rw [← show ((([(47, 1), (244567, 1), (3184277, 1), (1259718704296139, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102447 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_47, prime_thirtyNineAK_244567, prime_thirtyNineAK_3184277, prime_thirtyNineAK_1259718704296139]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102448 : Nat.totient 46108408480010068432943102448 = 15366085210369260435385626624 := by
  rw [← show ((([(2, 4), (3, 1), (7057, 1), (15373, 1), (74323, 1), (119134327776067, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102448 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_3, prime_thirtyNineAK_7057, prime_thirtyNineAK_15373, prime_thirtyNineAK_74323, prime_thirtyNineAK_119134327776067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102449 : Nat.totient 46108408480010068432943102449 = 39521084268086794631165169024 := by
  rw [← show ((([(7, 2), (96697, 1), (9731304261388365557833, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102449 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_7, prime_thirtyNineAK_96697, prime_thirtyNineAK_9731304261388365557833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102450 : Nat.totient 46108408480010068432943102450 = 18274091098205645907666612480 := by
  rw [← show ((([(2, 1), (5, 2), (109, 1), (272269, 1), (3810125287, 1), (8155417087, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102450 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_5, prime_thirtyNineAK_109, prime_thirtyNineAK_272269, prime_thirtyNineAK_3810125287, prime_thirtyNineAK_8155417087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102451 : Nat.totient 46108408480010068432943102451 = 28925638429639155373696665600 := by
  rw [← show ((([(3, 1), (17, 1), (9437, 1), (20023, 1), (46861, 1), (102102247358591, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102451 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_3, prime_thirtyNineAK_17, prime_thirtyNineAK_9437, prime_thirtyNineAK_20023, prime_thirtyNineAK_46861, prime_thirtyNineAK_102102247358591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102452 : Nat.totient 46108408480010068432943102452 = 21240739924839212415211929600 := by
  rw [← show ((([(2, 2), (13, 1), (769, 1), (2143, 1), (8597, 1), (9792301, 1), (6391408799, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102452 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_13, prime_thirtyNineAK_769, prime_thirtyNineAK_2143, prime_thirtyNineAK_8597, prime_thirtyNineAK_9792301, prime_thirtyNineAK_6391408799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102453 : Nat.totient 46108408480010068432943102453 = 45238438508689123745529081600 := by
  rw [← show ((([(53, 1), (869969971320944687414020801, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102453 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_53, prime_thirtyNineAK_869969971320944687414020801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102454 : Nat.totient 46108408480010068432943102454 = 15368251530660129115487241120 := by
  rw [← show ((([(2, 1), (3, 3), (12619, 1), (212140652989, 1), (318960960511, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102454 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_3, prime_thirtyNineAK_12619, prime_thirtyNineAK_212140652989, prime_thirtyNineAK_318960960511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102455 : Nat.totient 46108408480010068432943102455 = 33533387985461867951231347200 := by
  rw [← show ((([(5, 1), (11, 1), (838334699636546698780783681, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102455 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_5, prime_thirtyNineAK_11, prime_thirtyNineAK_838334699636546698780783681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102456 : Nat.totient 46108408480010068432943102456 = 19760746491432886471261329600 := by
  rw [← show ((([(2, 3), (7, 1), (823364437143036936302555401, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102456 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_7, prime_thirtyNineAK_823364437143036936302555401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102457 : Nat.totient 46108408480010068432943102457 = 29112267051024473456475192000 := by
  rw [← show ((([(3, 1), (19, 1), (3391, 1), (118691, 1), (2009831726809906421, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102457 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_3, prime_thirtyNineAK_19, prime_thirtyNineAK_3391, prime_thirtyNineAK_118691, prime_thirtyNineAK_2009831726809906421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102458 : Nat.totient 46108408480010068432943102458 = 22258908923976473044756320000 := by
  rw [← show ((([(2, 1), (29, 1), (77101, 1), (660659, 1), (104981389, 1), (148662851, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102458 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_29, prime_thirtyNineAK_77101, prime_thirtyNineAK_660659, prime_thirtyNineAK_104981389, prime_thirtyNineAK_148662851]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102459 : Nat.totient 46108408480010068432943102459 = 45321489109746476478266400000 := by
  rw [← show ((([(59, 1), (8521, 1), (452671, 1), (33371411, 1), (6071280701, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102459 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_59, prime_thirtyNineAK_8521, prime_thirtyNineAK_452671, prime_thirtyNineAK_33371411, prime_thirtyNineAK_6071280701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102460 : Nat.totient 46108408480010068432943102460 = 12294933615168744834505728000 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (19387, 1), (1584001, 1), (25024350819790243, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102460 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_3, prime_thirtyNineAK_5, prime_thirtyNineAK_19387, prime_thirtyNineAK_1584001, prime_thirtyNineAK_25024350819790243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102461 : Nat.totient 46108408480010068432943102461 = 45346920688497976788886656000 := by
  rw [← show ((([(61, 1), (8081, 1), (93537377657792856412721, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102461 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_61, prime_thirtyNineAK_8081, prime_thirtyNineAK_93537377657792856412721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102462 : Nat.totient 46108408480010068432943102462 = 22309020110329558010235048960 := by
  rw [← show ((([(2, 1), (31, 1), (14879, 1), (33891713, 1), (1474759419059263, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102462 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_31, prime_thirtyNineAK_14879, prime_thirtyNineAK_33891713, prime_thirtyNineAK_1474759419059263]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102463 : Nat.totient 46108408480010068432943102463 = 26214842820823810147519822080 := by
  rw [← show ((([(3, 2), (7, 1), (211, 1), (3299, 1), (1160494157, 1), (906007626637, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102463 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_3, prime_thirtyNineAK_7, prime_thirtyNineAK_211, prime_thirtyNineAK_3299, prime_thirtyNineAK_1160494157, prime_thirtyNineAK_906007626637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102464 : Nat.totient 46108408480010068432943102464 = 22962354820722145633935744000 := by
  rw [← show ((([(2, 9), (251, 1), (358786794073783525530247, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102464 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_251, prime_thirtyNineAK_358786794073783525530247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102465 : Nat.totient 46108408480010068432943102465 = 33882203570364765988230942720 := by
  rw [← show ((([(5, 1), (13, 1), (281, 1), (739, 1), (3540386347, 1), (964862349257, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102465 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_5, prime_thirtyNineAK_13, prime_thirtyNineAK_281, prime_thirtyNineAK_739, prime_thirtyNineAK_3540386347, prime_thirtyNineAK_964862349257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102466 : Nat.totient 46108408480010068432943102466 = 13813552207742565162094848000 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (89, 1), (12301, 1), (24019, 1), (4553573, 1), (5834431507, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102466 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_3, prime_thirtyNineAK_11, prime_thirtyNineAK_89, prime_thirtyNineAK_12301, prime_thirtyNineAK_24019, prime_thirtyNineAK_4553573, prime_thirtyNineAK_5834431507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102467 : Nat.totient 46108408480010068432943102467 = 46081428720805849551472683496 := by
  rw [← show ((([(1709, 1), (26979759204218881470417263, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102467 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_1709, prime_thirtyNineAK_26979759204218881470417263]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102468 : Nat.totient 46108408480010068432943102468 = 21698074578828267497855577600 := by
  rw [← show ((([(2, 2), (17, 1), (678064830588383359307986801, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102468 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_17, prime_thirtyNineAK_678064830588383359307986801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102469 : Nat.totient 46108408480010068432943102469 = 29402457658363737319269446208 := by
  rw [← show ((([(3, 1), (23, 1), (5140117, 1), (130004395631094960253, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102469 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_3, prime_thirtyNineAK_23, prime_thirtyNineAK_5140117, prime_thirtyNineAK_130004395631094960253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102470 : Nat.totient 46108408480010068432943102470 = 15796458879655975835652000000 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (1721, 1), (5351, 1), (71526384117836592751, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102470 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_5, prime_thirtyNineAK_7, prime_thirtyNineAK_1721, prime_thirtyNineAK_5351, prime_thirtyNineAK_71526384117836592751]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102471 : Nat.totient 46108408480010068432943102471 = 45886076914432458403060042240 := by
  rw [← show ((([(263, 1), (977, 1), (179444362855213906281521, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102471 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_263, prime_thirtyNineAK_977, prime_thirtyNineAK_179444362855213906281521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102472 : Nat.totient 46108408480010068432943102472 = 15358329701012717438469748992 := by
  rw [← show ((([(2, 3), (3, 2), (1907, 1), (4987, 1), (67337590816601618489, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102472 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_3, prime_thirtyNineAK_1907, prime_thirtyNineAK_4987, prime_thirtyNineAK_67337590816601618489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102473 : Nat.totient 46108408480010068432943102473 = 45841885887032914439698328784 := by
  rw [← show ((([(173, 1), (75504561983, 1), (3529887272639347, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102473 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_173, prime_thirtyNineAK_75504561983, prime_thirtyNineAK_3529887272639347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102474 : Nat.totient 46108408480010068432943102474 = 22431079712642982858842355072 := by
  rw [← show ((([(2, 1), (37, 1), (597803, 1), (55565339, 1), (18757992323353, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102474 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_37, prime_thirtyNineAK_597803, prime_thirtyNineAK_55565339, prime_thirtyNineAK_18757992323353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102475 : Nat.totient 46108408480010068432943102475 = 24224119082035140430441746720 := by
  rw [← show ((([(3, 1), (5, 2), (67, 1), (9175802682589068344864299, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102475 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_3, prime_thirtyNineAK_5, prime_thirtyNineAK_67, prime_thirtyNineAK_9175802682589068344864299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102476 : Nat.totient 46108408480010068432943102476 = 21840825069478453468236206400 := by
  rw [← show ((([(2, 2), (19, 1), (606689585263290374117672401, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102476 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_19, prime_thirtyNineAK_606689585263290374117672401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102477 : Nat.totient 46108408480010068432943102477 = 35910699197118270485213642400 := by
  rw [← show ((([(7, 1), (11, 2), (3919, 1), (4099, 1), (3388781283930634511, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102477 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_7, prime_thirtyNineAK_11, prime_thirtyNineAK_3919, prime_thirtyNineAK_4099, prime_thirtyNineAK_3388781283930634511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102478 : Nat.totient 46108408480010068432943102478 = 14187202597629893889172946400 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102478 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_3, prime_thirtyNineAK_13, prime_thirtyNineAK_1222615931, prime_thirtyNineAK_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102479 : Nat.totient 46108408480010068432943102479 = 45552881220166419777979156800 := by
  rw [← show ((([(83, 1), (10747391, 1), (1747878553, 1), (29572479331, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102479 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_83, prime_thirtyNineAK_10747391, prime_thirtyNineAK_1747878553, prime_thirtyNineAK_29572479331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102480 : Nat.totient 46108408480010068432943102480 = 18443363392002472776412416000 := by
  rw [← show ((([(2, 4), (5, 1), (20592344991601, 1), (27988803909181, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102480 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_5, prime_thirtyNineAK_20592344991601, prime_thirtyNineAK_27988803909181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102481 : Nat.totient 46108408480010068432943102481 = 30738898504106918650506613248 := by
  rw [← show ((([(3, 4), (759313, 1), (749677156672310144177, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102481 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_3, prime_thirtyNineAK_759313, prime_thirtyNineAK_749677156672310144177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102482 : Nat.totient 46108408480010068432943102482 = 22443744032517480336751825920 := by
  rw [← show ((([(2, 1), (41, 1), (467, 1), (9975615259, 1), (120700677594017, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102482 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_41, prime_thirtyNineAK_467, prime_thirtyNineAK_9975615259, prime_thirtyNineAK_120700677594017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102483 : Nat.totient 46108408480010068432943102483 = 46064030801011021206347391048 := by
  rw [← show ((([(1039, 1), (44377678999047226595710397, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102483 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_1039, prime_thirtyNineAK_44377678999047226595710397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102484 : Nat.totient 46108408480010068432943102484 = 13172677721856279977515667808 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (11423, 1), (48053018012958471872687, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102484 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_3, prime_thirtyNineAK_7, prime_thirtyNineAK_11423, prime_thirtyNineAK_48053018012958471872687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102485 : Nat.totient 46108408480010068432943102485 = 34716918607867464527492575488 := by
  rw [← show ((([(5, 1), (17, 1), (48334903, 1), (11222777554155983047, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102485 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_5, prime_thirtyNineAK_17, prime_thirtyNineAK_48334903, prime_thirtyNineAK_11222777554155983047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102486 : Nat.totient 46108408480010068432943102486 = 22518059955353754350972212800 := by
  rw [← show ((([(2, 1), (43, 1), (536144284651279865499338401, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102486 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_43, prime_thirtyNineAK_536144284651279865499338401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102487 : Nat.totient 46108408480010068432943102487 = 29291242143681466545675187200 := by
  rw [← show ((([(3, 1), (29, 1), (101, 1), (313, 1), (16764676135348824717077, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102487 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_3, prime_thirtyNineAK_29, prime_thirtyNineAK_101, prime_thirtyNineAK_313, prime_thirtyNineAK_16764676135348824717077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102488 : Nat.totient 46108408480010068432943102488 = 20739252471047042311213148160 := by
  rw [← show ((([(2, 3), (11, 1), (127, 1), (397, 1), (13399, 1), (145037, 1), (1255519, 1), (4259207, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102488 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_11, prime_thirtyNineAK_127, prime_thirtyNineAK_397, prime_thirtyNineAK_13399, prime_thirtyNineAK_145037, prime_thirtyNineAK_1255519, prime_thirtyNineAK_4259207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102489 : Nat.totient 46108408480010068432943102489 = 46108399691709360558613858356 := by
  rw [← show ((([(5246567, 1), (8788300707874323997567, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102489 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_5246567, prime_thirtyNineAK_8788300707874323997567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102490 : Nat.totient 46108408480010068432943102490 = 12268670615249943810603667968 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (457, 1), (1121040809141990479770073, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102490 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_3, prime_thirtyNineAK_5, prime_thirtyNineAK_457, prime_thirtyNineAK_1121040809141990479770073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102491 : Nat.totient 46108408480010068432943102491 = 36431196522372142628361434496 := by
  rw [← show ((([(7, 1), (13, 1), (727, 1), (40346827, 1), (17274080639688469, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102491 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_7, prime_thirtyNineAK_13, prime_thirtyNineAK_727, prime_thirtyNineAK_40346827, prime_thirtyNineAK_17274080639688469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102492 : Nat.totient 46108408480010068432943102492 = 22042284409526416430743687680 := by
  rw [← show ((([(2, 2), (23, 1), (2719, 1), (15173, 1), (1307287211, 1), (9292672393, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102492 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_23, prime_thirtyNineAK_2719, prime_thirtyNineAK_15173, prime_thirtyNineAK_1307287211, prime_thirtyNineAK_9292672393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102493 : Nat.totient 46108408480010068432943102493 = 29741076795069761131101672000 := by
  rw [← show ((([(3, 1), (31, 1), (5683, 1), (28351, 1), (3077167559992740997, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102493 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_3, prime_thirtyNineAK_31, prime_thirtyNineAK_5683, prime_thirtyNineAK_28351, prime_thirtyNineAK_3077167559992740997]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102494 : Nat.totient 46108408480010068432943102494 = 22561349486084778828324902400 := by
  rw [← show ((([(2, 1), (47, 1), (9887, 1), (452857, 1), (2895439, 1), (37836611801, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102494 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_47, prime_thirtyNineAK_9887, prime_thirtyNineAK_452857, prime_thirtyNineAK_2895439, prime_thirtyNineAK_37836611801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102495 : Nat.totient 46108408480010068432943102495 = 34690244781886945070716767744 := by
  rw [← show ((([(5, 1), (19, 1), (137, 1), (3542712906646951089738233, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102495 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_5, prime_thirtyNineAK_19, prime_thirtyNineAK_137, prime_thirtyNineAK_3542712906646951089738233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102496 : Nat.totient 46108408480010068432943102496 = 15277436740264002174838615296 := by
  rw [← show ((([(2, 5), (3, 1), (167, 1), (9456603047, 1), (304128603975499, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102496 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_3, prime_thirtyNineAK_167, prime_thirtyNineAK_9456603047, prime_thirtyNineAK_304128603975499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102497 : Nat.totient 46108408480010068432943102497 = 45931647695431800430156089600 := by
  rw [← show ((([(337, 1), (1151, 1), (2531601659, 1), (46954750354909, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102497 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_337, prime_thirtyNineAK_1151, prime_thirtyNineAK_2531601659, prime_thirtyNineAK_46954750354909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102498 : Nat.totient 46108408480010068432943102498 = 19760509264737590814788728272 := by
  rw [← show ((([(2, 1), (7, 3), (83299, 1), (806893521413797442557, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102498 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_7, prime_thirtyNineAK_83299, prime_thirtyNineAK_806893521413797442557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102499 : Nat.totient 46108408480010068432943102499 = 27944480337148001632901575680 := by
  rw [← show ((([(3, 2), (11, 1), (3089857, 1), (46053307, 1), (3272997965299, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102499 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_3, prime_thirtyNineAK_11, prime_thirtyNineAK_3089857, prime_thirtyNineAK_46053307, prime_thirtyNineAK_3272997965299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyNineAK_46108408480010068432943102500 : Nat.totient 46108408480010068432943102500 = 18183597691773814153707840000 := by
  rw [← show ((([(2, 2), (5, 4), (71, 1), (974854703, 1), (266466049533457, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010068432943102500 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyNineAK_2, prime_thirtyNineAK_5, prime_thirtyNineAK_71, prime_thirtyNineAK_974854703, prime_thirtyNineAK_266466049533457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64ThirtyNineAK : certifiedKill 1 46108408480010068432943102399 100 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_thirtyNineAK_46108408480010068432943102400, phi_thirtyNineAK_46108408480010068432943102401, phi_thirtyNineAK_46108408480010068432943102402,
    phi_thirtyNineAK_46108408480010068432943102403, phi_thirtyNineAK_46108408480010068432943102404, phi_thirtyNineAK_46108408480010068432943102405,
    phi_thirtyNineAK_46108408480010068432943102406, phi_thirtyNineAK_46108408480010068432943102407, phi_thirtyNineAK_46108408480010068432943102408,
    phi_thirtyNineAK_46108408480010068432943102409, phi_thirtyNineAK_46108408480010068432943102410, phi_thirtyNineAK_46108408480010068432943102411,
    phi_thirtyNineAK_46108408480010068432943102412, phi_thirtyNineAK_46108408480010068432943102413, phi_thirtyNineAK_46108408480010068432943102414,
    phi_thirtyNineAK_46108408480010068432943102415, phi_thirtyNineAK_46108408480010068432943102416, phi_thirtyNineAK_46108408480010068432943102417,
    phi_thirtyNineAK_46108408480010068432943102418, phi_thirtyNineAK_46108408480010068432943102419, phi_thirtyNineAK_46108408480010068432943102420,
    phi_thirtyNineAK_46108408480010068432943102421, phi_thirtyNineAK_46108408480010068432943102422, phi_thirtyNineAK_46108408480010068432943102423,
    phi_thirtyNineAK_46108408480010068432943102424, phi_thirtyNineAK_46108408480010068432943102425, phi_thirtyNineAK_46108408480010068432943102426,
    phi_thirtyNineAK_46108408480010068432943102427, phi_thirtyNineAK_46108408480010068432943102428, phi_thirtyNineAK_46108408480010068432943102429,
    phi_thirtyNineAK_46108408480010068432943102430, phi_thirtyNineAK_46108408480010068432943102431, phi_thirtyNineAK_46108408480010068432943102432,
    phi_thirtyNineAK_46108408480010068432943102433, phi_thirtyNineAK_46108408480010068432943102434, phi_thirtyNineAK_46108408480010068432943102435,
    phi_thirtyNineAK_46108408480010068432943102436, phi_thirtyNineAK_46108408480010068432943102437, phi_thirtyNineAK_46108408480010068432943102438,
    phi_thirtyNineAK_46108408480010068432943102439, phi_thirtyNineAK_46108408480010068432943102440, phi_thirtyNineAK_46108408480010068432943102441,
    phi_thirtyNineAK_46108408480010068432943102442, phi_thirtyNineAK_46108408480010068432943102443, phi_thirtyNineAK_46108408480010068432943102444,
    phi_thirtyNineAK_46108408480010068432943102445, phi_thirtyNineAK_46108408480010068432943102446, phi_thirtyNineAK_46108408480010068432943102447,
    phi_thirtyNineAK_46108408480010068432943102448, phi_thirtyNineAK_46108408480010068432943102449, phi_thirtyNineAK_46108408480010068432943102450,
    phi_thirtyNineAK_46108408480010068432943102451, phi_thirtyNineAK_46108408480010068432943102452, phi_thirtyNineAK_46108408480010068432943102453,
    phi_thirtyNineAK_46108408480010068432943102454, phi_thirtyNineAK_46108408480010068432943102455, phi_thirtyNineAK_46108408480010068432943102456,
    phi_thirtyNineAK_46108408480010068432943102457, phi_thirtyNineAK_46108408480010068432943102458, phi_thirtyNineAK_46108408480010068432943102459,
    phi_thirtyNineAK_46108408480010068432943102460, phi_thirtyNineAK_46108408480010068432943102461, phi_thirtyNineAK_46108408480010068432943102462,
    phi_thirtyNineAK_46108408480010068432943102463, phi_thirtyNineAK_46108408480010068432943102464, phi_thirtyNineAK_46108408480010068432943102465,
    phi_thirtyNineAK_46108408480010068432943102466, phi_thirtyNineAK_46108408480010068432943102467, phi_thirtyNineAK_46108408480010068432943102468,
    phi_thirtyNineAK_46108408480010068432943102469, phi_thirtyNineAK_46108408480010068432943102470, phi_thirtyNineAK_46108408480010068432943102471,
    phi_thirtyNineAK_46108408480010068432943102472, phi_thirtyNineAK_46108408480010068432943102473, phi_thirtyNineAK_46108408480010068432943102474,
    phi_thirtyNineAK_46108408480010068432943102475, phi_thirtyNineAK_46108408480010068432943102476, phi_thirtyNineAK_46108408480010068432943102477,
    phi_thirtyNineAK_46108408480010068432943102478, phi_thirtyNineAK_46108408480010068432943102479, phi_thirtyNineAK_46108408480010068432943102480,
    phi_thirtyNineAK_46108408480010068432943102481, phi_thirtyNineAK_46108408480010068432943102482, phi_thirtyNineAK_46108408480010068432943102483,
    phi_thirtyNineAK_46108408480010068432943102484, phi_thirtyNineAK_46108408480010068432943102485, phi_thirtyNineAK_46108408480010068432943102486,
    phi_thirtyNineAK_46108408480010068432943102487, phi_thirtyNineAK_46108408480010068432943102488, phi_thirtyNineAK_46108408480010068432943102489,
    phi_thirtyNineAK_46108408480010068432943102490, phi_thirtyNineAK_46108408480010068432943102491, phi_thirtyNineAK_46108408480010068432943102492,
    phi_thirtyNineAK_46108408480010068432943102493, phi_thirtyNineAK_46108408480010068432943102494, phi_thirtyNineAK_46108408480010068432943102495,
    phi_thirtyNineAK_46108408480010068432943102496, phi_thirtyNineAK_46108408480010068432943102497, phi_thirtyNineAK_46108408480010068432943102498,
    phi_thirtyNineAK_46108408480010068432943102499, phi_thirtyNineAK_46108408480010068432943102500
  ]

end TotientTailPeriodKiller
end Erdos249257
