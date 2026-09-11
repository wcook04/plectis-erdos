import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def seventyOneBQFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem seventyOneBQFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : seventyOneBQFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [seventyOneBQFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [seventyOneBQFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then seventyOneBQFastPow a n * seventyOneBQFastPow a n * a else seventyOneBQFastPow a n * seventyOneBQFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_seventyOneBQ_2 : Nat.Prime 2 := by norm_num
private theorem prime_seventyOneBQ_3 : Nat.Prime 3 := by norm_num
private theorem prime_seventyOneBQ_5 : Nat.Prime 5 := by norm_num
private theorem prime_seventyOneBQ_7 : Nat.Prime 7 := by norm_num
private theorem prime_seventyOneBQ_11 : Nat.Prime 11 := by norm_num
private theorem prime_seventyOneBQ_13 : Nat.Prime 13 := by norm_num
private theorem prime_seventyOneBQ_17 : Nat.Prime 17 := by norm_num
private theorem prime_seventyOneBQ_19 : Nat.Prime 19 := by norm_num
private theorem prime_seventyOneBQ_23 : Nat.Prime 23 := by norm_num
private theorem prime_seventyOneBQ_29 : Nat.Prime 29 := by norm_num
private theorem prime_seventyOneBQ_31 : Nat.Prime 31 := by norm_num
private theorem prime_seventyOneBQ_37 : Nat.Prime 37 := by norm_num
private theorem prime_seventyOneBQ_41 : Nat.Prime 41 := by norm_num
private theorem prime_seventyOneBQ_43 : Nat.Prime 43 := by norm_num
private theorem prime_seventyOneBQ_47 : Nat.Prime 47 := by norm_num
private theorem prime_seventyOneBQ_53 : Nat.Prime 53 := by norm_num
private theorem prime_seventyOneBQ_59 : Nat.Prime 59 := by norm_num
private theorem prime_seventyOneBQ_61 : Nat.Prime 61 := by norm_num
private theorem prime_seventyOneBQ_67 : Nat.Prime 67 := by norm_num
private theorem prime_seventyOneBQ_71 : Nat.Prime 71 := by norm_num
private theorem prime_seventyOneBQ_73 : Nat.Prime 73 := by norm_num
private theorem prime_seventyOneBQ_79 : Nat.Prime 79 := by norm_num
private theorem prime_seventyOneBQ_83 : Nat.Prime 83 := by norm_num
private theorem prime_seventyOneBQ_89 : Nat.Prime 89 := by norm_num
private theorem prime_seventyOneBQ_97 : Nat.Prime 97 := by norm_num
private theorem prime_seventyOneBQ_101 : Nat.Prime 101 := by norm_num
private theorem prime_seventyOneBQ_103 : Nat.Prime 103 := by norm_num
private theorem prime_seventyOneBQ_107 : Nat.Prime 107 := by norm_num
private theorem prime_seventyOneBQ_109 : Nat.Prime 109 := by norm_num
private theorem prime_seventyOneBQ_113 : Nat.Prime 113 := by norm_num
private theorem prime_seventyOneBQ_127 : Nat.Prime 127 := by norm_num
private theorem prime_seventyOneBQ_131 : Nat.Prime 131 := by norm_num
private theorem prime_seventyOneBQ_137 : Nat.Prime 137 := by norm_num
private theorem prime_seventyOneBQ_139 : Nat.Prime 139 := by norm_num
private theorem prime_seventyOneBQ_149 : Nat.Prime 149 := by norm_num
private theorem prime_seventyOneBQ_151 : Nat.Prime 151 := by norm_num
private theorem prime_seventyOneBQ_157 : Nat.Prime 157 := by norm_num
private theorem prime_seventyOneBQ_163 : Nat.Prime 163 := by norm_num
private theorem prime_seventyOneBQ_167 : Nat.Prime 167 := by norm_num
private theorem prime_seventyOneBQ_173 : Nat.Prime 173 := by norm_num
private theorem prime_seventyOneBQ_179 : Nat.Prime 179 := by norm_num
private theorem prime_seventyOneBQ_181 : Nat.Prime 181 := by norm_num
private theorem prime_seventyOneBQ_191 : Nat.Prime 191 := by norm_num
private theorem prime_seventyOneBQ_193 : Nat.Prime 193 := by norm_num
private theorem prime_seventyOneBQ_197 : Nat.Prime 197 := by norm_num
private theorem prime_seventyOneBQ_199 : Nat.Prime 199 := by norm_num
private theorem prime_seventyOneBQ_223 : Nat.Prime 223 := by norm_num
private theorem prime_seventyOneBQ_229 : Nat.Prime 229 := by norm_num
private theorem prime_seventyOneBQ_239 : Nat.Prime 239 := by norm_num
private theorem prime_seventyOneBQ_241 : Nat.Prime 241 := by norm_num
private theorem prime_seventyOneBQ_251 : Nat.Prime 251 := by norm_num
private theorem prime_seventyOneBQ_263 : Nat.Prime 263 := by norm_num
private theorem prime_seventyOneBQ_269 : Nat.Prime 269 := by norm_num
private theorem prime_seventyOneBQ_271 : Nat.Prime 271 := by norm_num
private theorem prime_seventyOneBQ_277 : Nat.Prime 277 := by norm_num
private theorem prime_seventyOneBQ_281 : Nat.Prime 281 := by norm_num
private theorem prime_seventyOneBQ_307 : Nat.Prime 307 := by norm_num
private theorem prime_seventyOneBQ_331 : Nat.Prime 331 := by norm_num
private theorem prime_seventyOneBQ_337 : Nat.Prime 337 := by norm_num
private theorem prime_seventyOneBQ_347 : Nat.Prime 347 := by norm_num
private theorem prime_seventyOneBQ_353 : Nat.Prime 353 := by norm_num
private theorem prime_seventyOneBQ_359 : Nat.Prime 359 := by norm_num
private theorem prime_seventyOneBQ_367 : Nat.Prime 367 := by norm_num
private theorem prime_seventyOneBQ_383 : Nat.Prime 383 := by norm_num
private theorem prime_seventyOneBQ_389 : Nat.Prime 389 := by norm_num
private theorem prime_seventyOneBQ_401 : Nat.Prime 401 := by norm_num
private theorem prime_seventyOneBQ_409 : Nat.Prime 409 := by norm_num
private theorem prime_seventyOneBQ_419 : Nat.Prime 419 := by norm_num
private theorem prime_seventyOneBQ_431 : Nat.Prime 431 := by norm_num
private theorem prime_seventyOneBQ_439 : Nat.Prime 439 := by norm_num
private theorem prime_seventyOneBQ_443 : Nat.Prime 443 := by norm_num
private theorem prime_seventyOneBQ_449 : Nat.Prime 449 := by norm_num
private theorem prime_seventyOneBQ_457 : Nat.Prime 457 := by norm_num
private theorem prime_seventyOneBQ_461 : Nat.Prime 461 := by norm_num
private theorem prime_seventyOneBQ_463 : Nat.Prime 463 := by norm_num
private theorem prime_seventyOneBQ_467 : Nat.Prime 467 := by norm_num
private theorem prime_seventyOneBQ_487 : Nat.Prime 487 := by norm_num
private theorem prime_seventyOneBQ_491 : Nat.Prime 491 := by norm_num
private theorem prime_seventyOneBQ_503 : Nat.Prime 503 := by norm_num
private theorem prime_seventyOneBQ_521 : Nat.Prime 521 := by norm_num
private theorem prime_seventyOneBQ_541 : Nat.Prime 541 := by norm_num
private theorem prime_seventyOneBQ_547 : Nat.Prime 547 := by norm_num
private theorem prime_seventyOneBQ_569 : Nat.Prime 569 := by norm_num
private theorem prime_seventyOneBQ_571 : Nat.Prime 571 := by norm_num
private theorem prime_seventyOneBQ_587 : Nat.Prime 587 := by norm_num
private theorem prime_seventyOneBQ_631 : Nat.Prime 631 := by norm_num
private theorem prime_seventyOneBQ_643 : Nat.Prime 643 := by norm_num
private theorem prime_seventyOneBQ_653 : Nat.Prime 653 := by norm_num
private theorem prime_seventyOneBQ_659 : Nat.Prime 659 := by norm_num
private theorem prime_seventyOneBQ_673 : Nat.Prime 673 := by norm_num
private theorem prime_seventyOneBQ_691 : Nat.Prime 691 := by norm_num
private theorem prime_seventyOneBQ_709 : Nat.Prime 709 := by norm_num
private theorem prime_seventyOneBQ_719 : Nat.Prime 719 := by norm_num
private theorem prime_seventyOneBQ_743 : Nat.Prime 743 := by norm_num
private theorem prime_seventyOneBQ_757 : Nat.Prime 757 := by norm_num
private theorem prime_seventyOneBQ_797 : Nat.Prime 797 := by norm_num
private theorem prime_seventyOneBQ_811 : Nat.Prime 811 := by norm_num
private theorem prime_seventyOneBQ_823 : Nat.Prime 823 := by norm_num
private theorem prime_seventyOneBQ_827 : Nat.Prime 827 := by norm_num
private theorem prime_seventyOneBQ_829 : Nat.Prime 829 := by norm_num
private theorem prime_seventyOneBQ_839 : Nat.Prime 839 := by norm_num
private theorem prime_seventyOneBQ_853 : Nat.Prime 853 := by norm_num
private theorem prime_seventyOneBQ_859 : Nat.Prime 859 := by norm_num
private theorem prime_seventyOneBQ_877 : Nat.Prime 877 := by norm_num
private theorem prime_seventyOneBQ_911 : Nat.Prime 911 := by norm_num
private theorem prime_seventyOneBQ_937 : Nat.Prime 937 := by norm_num
private theorem prime_seventyOneBQ_967 : Nat.Prime 967 := by norm_num
private theorem prime_seventyOneBQ_971 : Nat.Prime 971 := by norm_num
private theorem prime_seventyOneBQ_997 : Nat.Prime 997 := by norm_num
private theorem prime_seventyOneBQ_1009 : Nat.Prime 1009 := by norm_num
private theorem prime_seventyOneBQ_1013 : Nat.Prime 1013 := by norm_num
private theorem prime_seventyOneBQ_1021 : Nat.Prime 1021 := by norm_num
private theorem prime_seventyOneBQ_1061 : Nat.Prime 1061 := by norm_num
private theorem prime_seventyOneBQ_1091 : Nat.Prime 1091 := by norm_num
private theorem prime_seventyOneBQ_1103 : Nat.Prime 1103 := by norm_num
private theorem prime_seventyOneBQ_1109 : Nat.Prime 1109 := by norm_num
private theorem prime_seventyOneBQ_1151 : Nat.Prime 1151 := by norm_num
private theorem prime_seventyOneBQ_1163 : Nat.Prime 1163 := by norm_num
private theorem prime_seventyOneBQ_1171 : Nat.Prime 1171 := by norm_num
private theorem prime_seventyOneBQ_1213 : Nat.Prime 1213 := by norm_num
private theorem prime_seventyOneBQ_1229 : Nat.Prime 1229 := by norm_num
private theorem prime_seventyOneBQ_1231 : Nat.Prime 1231 := by norm_num
private theorem prime_seventyOneBQ_1289 : Nat.Prime 1289 := by norm_num
private theorem prime_seventyOneBQ_1307 : Nat.Prime 1307 := by norm_num
private theorem prime_seventyOneBQ_1367 : Nat.Prime 1367 := by norm_num
private theorem prime_seventyOneBQ_1381 : Nat.Prime 1381 := by norm_num
private theorem prime_seventyOneBQ_1451 : Nat.Prime 1451 := by norm_num
private theorem prime_seventyOneBQ_1489 : Nat.Prime 1489 := by norm_num
private theorem prime_seventyOneBQ_1493 : Nat.Prime 1493 := by norm_num
private theorem prime_seventyOneBQ_1499 : Nat.Prime 1499 := by norm_num
private theorem prime_seventyOneBQ_1511 : Nat.Prime 1511 := by norm_num
private theorem prime_seventyOneBQ_1543 : Nat.Prime 1543 := by norm_num
private theorem prime_seventyOneBQ_1549 : Nat.Prime 1549 := by norm_num
private theorem prime_seventyOneBQ_1553 : Nat.Prime 1553 := by norm_num
private theorem prime_seventyOneBQ_1559 : Nat.Prime 1559 := by norm_num
private theorem prime_seventyOneBQ_1567 : Nat.Prime 1567 := by norm_num
private theorem prime_seventyOneBQ_1571 : Nat.Prime 1571 := by norm_num
private theorem prime_seventyOneBQ_1601 : Nat.Prime 1601 := by norm_num
private theorem prime_seventyOneBQ_1693 : Nat.Prime 1693 := by norm_num
private theorem prime_seventyOneBQ_1759 : Nat.Prime 1759 := by norm_num
private theorem prime_seventyOneBQ_1777 : Nat.Prime 1777 := by norm_num
private theorem prime_seventyOneBQ_1801 : Nat.Prime 1801 := by norm_num
private theorem prime_seventyOneBQ_1867 : Nat.Prime 1867 := by norm_num
private theorem prime_seventyOneBQ_1871 : Nat.Prime 1871 := by norm_num
private theorem prime_seventyOneBQ_1889 : Nat.Prime 1889 := by norm_num
private theorem prime_seventyOneBQ_1907 : Nat.Prime 1907 := by norm_num
private theorem prime_seventyOneBQ_1993 : Nat.Prime 1993 := by norm_num
private theorem prime_seventyOneBQ_2027 : Nat.Prime 2027 := by norm_num
private theorem prime_seventyOneBQ_2063 : Nat.Prime 2063 := by norm_num
private theorem prime_seventyOneBQ_2069 : Nat.Prime 2069 := by norm_num
private theorem prime_seventyOneBQ_2179 : Nat.Prime 2179 := by norm_num
private theorem prime_seventyOneBQ_2213 : Nat.Prime 2213 := by norm_num
private theorem prime_seventyOneBQ_2267 : Nat.Prime 2267 := by norm_num
private theorem prime_seventyOneBQ_2473 : Nat.Prime 2473 := by norm_num
private theorem prime_seventyOneBQ_2647 : Nat.Prime 2647 := by norm_num
private theorem prime_seventyOneBQ_2719 : Nat.Prime 2719 := by norm_num
private theorem prime_seventyOneBQ_2777 : Nat.Prime 2777 := by norm_num
private theorem prime_seventyOneBQ_2819 : Nat.Prime 2819 := by norm_num
private theorem prime_seventyOneBQ_2833 : Nat.Prime 2833 := by norm_num
private theorem prime_seventyOneBQ_2897 : Nat.Prime 2897 := by norm_num
private theorem prime_seventyOneBQ_2999 : Nat.Prime 2999 := by norm_num
private theorem prime_seventyOneBQ_3109 : Nat.Prime 3109 := by norm_num
private theorem prime_seventyOneBQ_3121 : Nat.Prime 3121 := by norm_num
private theorem prime_seventyOneBQ_3167 : Nat.Prime 3167 := by norm_num
private theorem prime_seventyOneBQ_3217 : Nat.Prime 3217 := by norm_num
private theorem prime_seventyOneBQ_3221 : Nat.Prime 3221 := by norm_num
private theorem prime_seventyOneBQ_3407 : Nat.Prime 3407 := by norm_num
private theorem prime_seventyOneBQ_3469 : Nat.Prime 3469 := by norm_num
private theorem prime_seventyOneBQ_3529 : Nat.Prime 3529 := by norm_num
private theorem prime_seventyOneBQ_3533 : Nat.Prime 3533 := by norm_num
private theorem prime_seventyOneBQ_3631 : Nat.Prime 3631 := by norm_num
private theorem prime_seventyOneBQ_3709 : Nat.Prime 3709 := by norm_num
private theorem prime_seventyOneBQ_3719 : Nat.Prime 3719 := by norm_num
private theorem prime_seventyOneBQ_3779 : Nat.Prime 3779 := by norm_num
private theorem prime_seventyOneBQ_3833 : Nat.Prime 3833 := by norm_num
private theorem prime_seventyOneBQ_3929 : Nat.Prime 3929 := by norm_num
private theorem prime_seventyOneBQ_4027 : Nat.Prime 4027 := by norm_num
private theorem prime_seventyOneBQ_4049 : Nat.Prime 4049 := by norm_num
private theorem prime_seventyOneBQ_4099 : Nat.Prime 4099 := by norm_num
private theorem prime_seventyOneBQ_4111 : Nat.Prime 4111 := by norm_num
private theorem prime_seventyOneBQ_4133 : Nat.Prime 4133 := by norm_num
private theorem prime_seventyOneBQ_4139 : Nat.Prime 4139 := by norm_num
private theorem prime_seventyOneBQ_4261 : Nat.Prime 4261 := by norm_num
private theorem prime_seventyOneBQ_4283 : Nat.Prime 4283 := by norm_num
private theorem prime_seventyOneBQ_4289 : Nat.Prime 4289 := by norm_num
private theorem prime_seventyOneBQ_4397 : Nat.Prime 4397 := by norm_num
private theorem prime_seventyOneBQ_4561 : Nat.Prime 4561 := by norm_num
private theorem prime_seventyOneBQ_4679 : Nat.Prime 4679 := by norm_num
private theorem prime_seventyOneBQ_4733 : Nat.Prime 4733 := by norm_num
private theorem prime_seventyOneBQ_4801 : Nat.Prime 4801 := by norm_num
private theorem prime_seventyOneBQ_4903 : Nat.Prime 4903 := by norm_num
private theorem prime_seventyOneBQ_5839 : Nat.Prime 5839 := by norm_num
private theorem prime_seventyOneBQ_6691 : Nat.Prime 6691 := by norm_num
private theorem prime_seventyOneBQ_7129 : Nat.Prime 7129 := by norm_num
private theorem prime_seventyOneBQ_8329 : Nat.Prime 8329 := by norm_num
private theorem prime_seventyOneBQ_8369 : Nat.Prime 8369 := by norm_num
private theorem prime_seventyOneBQ_8761 : Nat.Prime 8761 := by norm_num
private theorem prime_seventyOneBQ_8821 : Nat.Prime 8821 := by norm_num
private theorem prime_seventyOneBQ_9059 : Nat.Prime 9059 := by norm_num
private theorem prime_seventyOneBQ_9137 : Nat.Prime 9137 := by norm_num
private theorem prime_seventyOneBQ_9209 : Nat.Prime 9209 := by norm_num
private theorem prime_seventyOneBQ_9377 : Nat.Prime 9377 := by norm_num
private theorem prime_seventyOneBQ_9397 : Nat.Prime 9397 := by norm_num
private theorem prime_seventyOneBQ_9661 : Nat.Prime 9661 := by norm_num
private theorem prime_seventyOneBQ_9721 : Nat.Prime 9721 := by norm_num
private theorem prime_seventyOneBQ_11321 : Nat.Prime 11321 := by norm_num
private theorem prime_seventyOneBQ_12487 : Nat.Prime 12487 := by norm_num
private theorem prime_seventyOneBQ_12611 : Nat.Prime 12611 := by norm_num
private theorem prime_seventyOneBQ_13049 : Nat.Prime 13049 := by norm_num
private theorem prime_seventyOneBQ_13649 : Nat.Prime 13649 := by norm_num
private theorem prime_seventyOneBQ_13901 : Nat.Prime 13901 := by norm_num
private theorem prime_seventyOneBQ_14153 : Nat.Prime 14153 := by norm_num
private theorem prime_seventyOneBQ_14543 : Nat.Prime 14543 := by norm_num
private theorem prime_seventyOneBQ_14759 : Nat.Prime 14759 := by norm_num
private theorem prime_seventyOneBQ_15919 : Nat.Prime 15919 := by norm_num
private theorem prime_seventyOneBQ_16487 : Nat.Prime 16487 := by norm_num
private theorem prime_seventyOneBQ_17137 : Nat.Prime 17137 := by norm_num
private theorem prime_seventyOneBQ_17477 : Nat.Prime 17477 := by norm_num
private theorem prime_seventyOneBQ_18517 : Nat.Prime 18517 := by norm_num
private theorem prime_seventyOneBQ_19231 : Nat.Prime 19231 := by norm_num
private theorem prime_seventyOneBQ_19403 : Nat.Prime 19403 := by norm_num
private theorem prime_seventyOneBQ_19753 : Nat.Prime 19753 := by norm_num
private theorem prime_seventyOneBQ_20183 : Nat.Prime 20183 := by norm_num
private theorem prime_seventyOneBQ_20897 : Nat.Prime 20897 := by norm_num
private theorem prime_seventyOneBQ_21017 : Nat.Prime 21017 := by norm_num
private theorem prime_seventyOneBQ_21397 : Nat.Prime 21397 := by norm_num
private theorem prime_seventyOneBQ_22637 : Nat.Prime 22637 := by norm_num
private theorem prime_seventyOneBQ_22973 : Nat.Prime 22973 := by norm_num
private theorem prime_seventyOneBQ_23609 : Nat.Prime 23609 := by norm_num
private theorem prime_seventyOneBQ_24677 : Nat.Prime 24677 := by norm_num
private theorem prime_seventyOneBQ_24793 : Nat.Prime 24793 := by norm_num
private theorem prime_seventyOneBQ_24809 : Nat.Prime 24809 := by norm_num
private theorem prime_seventyOneBQ_26317 : Nat.Prime 26317 := by norm_num
private theorem prime_seventyOneBQ_27239 : Nat.Prime 27239 := by norm_num
private theorem prime_seventyOneBQ_27631 : Nat.Prime 27631 := by norm_num
private theorem prime_seventyOneBQ_29863 : Nat.Prime 29863 := by norm_num
private theorem prime_seventyOneBQ_30829 : Nat.Prime 30829 := by norm_num
private theorem prime_seventyOneBQ_31751 : Nat.Prime 31751 := by norm_num
private theorem prime_seventyOneBQ_33487 : Nat.Prime 33487 := by norm_num
private theorem prime_seventyOneBQ_33629 : Nat.Prime 33629 := by norm_num
private theorem prime_seventyOneBQ_34019 : Nat.Prime 34019 := by norm_num
private theorem prime_seventyOneBQ_35531 : Nat.Prime 35531 := by norm_num
private theorem prime_seventyOneBQ_36341 : Nat.Prime 36341 := by norm_num
private theorem prime_seventyOneBQ_36637 : Nat.Prime 36637 := by norm_num
private theorem prime_seventyOneBQ_36809 : Nat.Prime 36809 := by norm_num
private theorem prime_seventyOneBQ_37897 : Nat.Prime 37897 := by norm_num
private theorem prime_seventyOneBQ_38069 : Nat.Prime 38069 := by norm_num
private theorem prime_seventyOneBQ_38317 : Nat.Prime 38317 := by norm_num
private theorem prime_seventyOneBQ_39217 : Nat.Prime 39217 := by norm_num
private theorem prime_seventyOneBQ_41227 : Nat.Prime 41227 := by norm_num
private theorem prime_seventyOneBQ_41849 : Nat.Prime 41849 := by norm_num
private theorem prime_seventyOneBQ_41927 : Nat.Prime 41927 := by norm_num
private theorem prime_seventyOneBQ_41983 : Nat.Prime 41983 := by norm_num
private theorem prime_seventyOneBQ_42139 : Nat.Prime 42139 := by norm_num
private theorem prime_seventyOneBQ_42703 : Nat.Prime 42703 := by norm_num
private theorem prime_seventyOneBQ_44909 : Nat.Prime 44909 := by norm_num
private theorem prime_seventyOneBQ_45691 : Nat.Prime 45691 := by norm_num
private theorem prime_seventyOneBQ_45767 : Nat.Prime 45767 := by norm_num
private theorem prime_seventyOneBQ_46747 : Nat.Prime 46747 := by norm_num
private theorem prime_seventyOneBQ_46853 : Nat.Prime 46853 := by norm_num
private theorem prime_seventyOneBQ_49747 : Nat.Prime 49747 := by norm_num
private theorem prime_seventyOneBQ_52697 : Nat.Prime 52697 := by norm_num
private theorem prime_seventyOneBQ_55817 : Nat.Prime 55817 := by norm_num
private theorem prime_seventyOneBQ_56857 : Nat.Prime 56857 := by norm_num
private theorem prime_seventyOneBQ_59273 : Nat.Prime 59273 := by norm_num
private theorem prime_seventyOneBQ_59659 : Nat.Prime 59659 := by norm_num
private theorem prime_seventyOneBQ_60793 : Nat.Prime 60793 := by norm_num
private theorem prime_seventyOneBQ_66749 : Nat.Prime 66749 := by norm_num
private theorem prime_seventyOneBQ_67993 : Nat.Prime 67993 := by norm_num
private theorem prime_seventyOneBQ_70937 : Nat.Prime 70937 := by norm_num
private theorem prime_seventyOneBQ_70957 : Nat.Prime 70957 := by norm_num
private theorem prime_seventyOneBQ_72073 : Nat.Prime 72073 := by norm_num
private theorem prime_seventyOneBQ_72493 : Nat.Prime 72493 := by norm_num
private theorem prime_seventyOneBQ_75511 : Nat.Prime 75511 := by norm_num
private theorem prime_seventyOneBQ_77731 : Nat.Prime 77731 := by norm_num
private theorem prime_seventyOneBQ_79379 : Nat.Prime 79379 := by norm_num
private theorem prime_seventyOneBQ_80761 : Nat.Prime 80761 := by norm_num
private theorem prime_seventyOneBQ_86291 : Nat.Prime 86291 := by norm_num
private theorem prime_seventyOneBQ_92003 : Nat.Prime 92003 := by norm_num
private theorem prime_seventyOneBQ_92177 : Nat.Prime 92177 := by norm_num
private theorem prime_seventyOneBQ_95747 : Nat.Prime 95747 := by norm_num
private theorem prime_seventyOneBQ_96847 : Nat.Prime 96847 := by norm_num
private theorem prime_seventyOneBQ_100313 : Nat.Prime 100313 := by norm_num
private theorem prime_seventyOneBQ_100957 : Nat.Prime 100957 := by norm_num
private theorem prime_seventyOneBQ_109883 : Nat.Prime 109883 := by norm_num
private theorem prime_seventyOneBQ_120103 : Nat.Prime 120103 := by norm_num
private theorem prime_seventyOneBQ_133481 : Nat.Prime 133481 := by norm_num
private theorem prime_seventyOneBQ_138829 : Nat.Prime 138829 := by norm_num
private theorem prime_seventyOneBQ_140111 : Nat.Prime 140111 := by norm_num
private theorem prime_seventyOneBQ_141833 : Nat.Prime 141833 := by norm_num
private theorem prime_seventyOneBQ_161911 : Nat.Prime 161911 := by norm_num
private theorem prime_seventyOneBQ_167437 : Nat.Prime 167437 := by norm_num
private theorem prime_seventyOneBQ_179917 : Nat.Prime 179917 := by norm_num
private theorem prime_seventyOneBQ_187069 : Nat.Prime 187069 := by norm_num
private theorem prime_seventyOneBQ_193873 : Nat.Prime 193873 := by norm_num
private theorem prime_seventyOneBQ_201329 : Nat.Prime 201329 := by norm_num
private theorem prime_seventyOneBQ_204151 : Nat.Prime 204151 := by norm_num
private theorem prime_seventyOneBQ_209597 : Nat.Prime 209597 := by norm_num
private theorem prime_seventyOneBQ_215051 : Nat.Prime 215051 := by norm_num
private theorem prime_seventyOneBQ_215279 : Nat.Prime 215279 := by norm_num
private theorem prime_seventyOneBQ_221653 : Nat.Prime 221653 := by norm_num
private theorem prime_seventyOneBQ_231529 : Nat.Prime 231529 := by norm_num
private theorem prime_seventyOneBQ_236891 : Nat.Prime 236891 := by norm_num
private theorem prime_seventyOneBQ_239831 : Nat.Prime 239831 := by norm_num
private theorem prime_seventyOneBQ_249671 : Nat.Prime 249671 := by norm_num
private theorem prime_seventyOneBQ_256471 : Nat.Prime 256471 := by norm_num
private theorem prime_seventyOneBQ_259627 : Nat.Prime 259627 := by norm_num
private theorem prime_seventyOneBQ_270601 : Nat.Prime 270601 := by norm_num
private theorem prime_seventyOneBQ_274187 : Nat.Prime 274187 := by norm_num
private theorem prime_seventyOneBQ_298303 : Nat.Prime 298303 := by norm_num
private theorem prime_seventyOneBQ_299359 : Nat.Prime 299359 := by norm_num
private theorem prime_seventyOneBQ_303917 : Nat.Prime 303917 := by norm_num
private theorem prime_seventyOneBQ_310697 : Nat.Prime 310697 := by norm_num
private theorem prime_seventyOneBQ_315961 : Nat.Prime 315961 := by norm_num
private theorem prime_seventyOneBQ_318911 : Nat.Prime 318911 := by norm_num
private theorem prime_seventyOneBQ_348241 : Nat.Prime 348241 := by norm_num
private theorem prime_seventyOneBQ_371299 : Nat.Prime 371299 := by norm_num
private theorem prime_seventyOneBQ_373073 : Nat.Prime 373073 := by norm_num
private theorem prime_seventyOneBQ_378401 : Nat.Prime 378401 := by norm_num
private theorem prime_seventyOneBQ_380777 : Nat.Prime 380777 := by norm_num
private theorem prime_seventyOneBQ_380971 : Nat.Prime 380971 := by norm_num
private theorem prime_seventyOneBQ_382331 : Nat.Prime 382331 := by norm_num
private theorem prime_seventyOneBQ_395261 : Nat.Prime 395261 := by norm_num
private theorem prime_seventyOneBQ_420037 : Nat.Prime 420037 := by norm_num
private theorem prime_seventyOneBQ_423989 : Nat.Prime 423989 := by norm_num
private theorem prime_seventyOneBQ_426469 : Nat.Prime 426469 := by norm_num
private theorem prime_seventyOneBQ_431693 : Nat.Prime 431693 := by norm_num
private theorem prime_seventyOneBQ_451441 : Nat.Prime 451441 := by norm_num
private theorem prime_seventyOneBQ_466079 : Nat.Prime 466079 := by norm_num
private theorem prime_seventyOneBQ_473311 : Nat.Prime 473311 := by norm_num
private theorem prime_seventyOneBQ_487177 : Nat.Prime 487177 := by norm_num
private theorem prime_seventyOneBQ_487183 : Nat.Prime 487183 := by norm_num
private theorem prime_seventyOneBQ_505979 : Nat.Prime 505979 := by norm_num
private theorem prime_seventyOneBQ_523637 : Nat.Prime 523637 := by norm_num
private theorem prime_seventyOneBQ_530989 : Nat.Prime 530989 := by norm_num
private theorem prime_seventyOneBQ_534697 : Nat.Prime 534697 := by norm_num
private theorem prime_seventyOneBQ_541267 : Nat.Prime 541267 := by norm_num
private theorem prime_seventyOneBQ_544963 : Nat.Prime 544963 := by norm_num
private theorem prime_seventyOneBQ_562613 : Nat.Prime 562613 := by norm_num
private theorem prime_seventyOneBQ_630871 : Nat.Prime 630871 := by norm_num
private theorem prime_seventyOneBQ_657131 : Nat.Prime 657131 := by norm_num
private theorem prime_seventyOneBQ_683477 : Nat.Prime 683477 := by norm_num
private theorem prime_seventyOneBQ_704897 : Nat.Prime 704897 := by norm_num
private theorem prime_seventyOneBQ_712507 : Nat.Prime 712507 := by norm_num
private theorem prime_seventyOneBQ_778927 : Nat.Prime 778927 := by norm_num
private theorem prime_seventyOneBQ_788933 : Nat.Prime 788933 := by norm_num
private theorem prime_seventyOneBQ_799817 : Nat.Prime 799817 := by norm_num
private theorem prime_seventyOneBQ_895553 : Nat.Prime 895553 := by norm_num
private theorem prime_seventyOneBQ_927569 : Nat.Prime 927569 := by norm_num
private theorem prime_seventyOneBQ_942827 : Nat.Prime 942827 := by norm_num
private theorem prime_seventyOneBQ_1083253 : Nat.Prime 1083253 := by norm_num
private theorem prime_seventyOneBQ_1101509 : Nat.Prime 1101509 := by norm_num
private theorem prime_seventyOneBQ_1136741 : Nat.Prime 1136741 := by norm_num
private theorem prime_seventyOneBQ_1261069 : Nat.Prime 1261069 := by norm_num
private theorem prime_seventyOneBQ_1283969 : Nat.Prime 1283969 := by norm_num
private theorem prime_seventyOneBQ_1336547 : Nat.Prime 1336547 := by norm_num
private theorem prime_seventyOneBQ_1337701 : Nat.Prime 1337701 := by norm_num
private theorem prime_seventyOneBQ_1396607 : Nat.Prime 1396607 := by norm_num
private theorem prime_seventyOneBQ_1414297 : Nat.Prime 1414297 := by norm_num
private theorem prime_seventyOneBQ_1434451 : Nat.Prime 1434451 := by norm_num
private theorem prime_seventyOneBQ_1519883 : Nat.Prime 1519883 := by norm_num
private theorem prime_seventyOneBQ_1542703 : Nat.Prime 1542703 := by norm_num
private theorem prime_seventyOneBQ_1745897 : Nat.Prime 1745897 := by norm_num
private theorem prime_seventyOneBQ_1993507 : Nat.Prime 1993507 := by norm_num
private theorem prime_seventyOneBQ_2019047 : Nat.Prime 2019047 := by norm_num
private theorem prime_seventyOneBQ_2043269 : Nat.Prime 2043269 := by norm_num
private theorem prime_seventyOneBQ_2066681 : Nat.Prime 2066681 := by norm_num
private theorem prime_seventyOneBQ_2088871 : Nat.Prime 2088871 := by norm_num
private theorem prime_seventyOneBQ_2140543 : Nat.Prime 2140543 := by norm_num
private theorem prime_seventyOneBQ_2167063 : Nat.Prime 2167063 := by norm_num
private theorem prime_seventyOneBQ_2183507 : Nat.Prime 2183507 := by norm_num
private theorem prime_seventyOneBQ_2322401 : Nat.Prime 2322401 := by norm_num
private theorem prime_seventyOneBQ_2415409 : Nat.Prime 2415409 := by norm_num
private theorem prime_seventyOneBQ_2465081 : Nat.Prime 2465081 := by norm_num
private theorem prime_seventyOneBQ_2540173 : Nat.Prime 2540173 := by norm_num
private theorem prime_seventyOneBQ_2748037 : Nat.Prime 2748037 := by norm_num
private theorem prime_seventyOneBQ_2804189 : Nat.Prime 2804189 := by norm_num
private theorem prime_seventyOneBQ_3105527 : Nat.Prime 3105527 := by norm_num
private theorem prime_seventyOneBQ_3239419 : Nat.Prime 3239419 := by norm_num
private theorem prime_seventyOneBQ_3591793 : Nat.Prime 3591793 := by norm_num
private theorem prime_seventyOneBQ_3649153 : Nat.Prime 3649153 := by norm_num
private theorem prime_seventyOneBQ_3688453 : Nat.Prime 3688453 := by norm_num
private theorem prime_seventyOneBQ_3810173 : Nat.Prime 3810173 := by norm_num
private theorem prime_seventyOneBQ_3994553 : Nat.Prime 3994553 := by norm_num
private theorem prime_seventyOneBQ_4075609 : Nat.Prime 4075609 := by norm_num
private theorem prime_seventyOneBQ_4491887 : Nat.Prime 4491887 := by norm_num
private theorem prime_seventyOneBQ_4523297 : Nat.Prime 4523297 := by norm_num
private theorem prime_seventyOneBQ_4827257 : Nat.Prime 4827257 := by norm_num
private theorem prime_seventyOneBQ_4834421 : Nat.Prime 4834421 := by norm_num
private theorem prime_seventyOneBQ_5107381 : Nat.Prime 5107381 := by norm_num
private theorem prime_seventyOneBQ_5128063 : Nat.Prime 5128063 := by norm_num
private theorem prime_seventyOneBQ_5133127 : Nat.Prime 5133127 := by norm_num
private theorem prime_seventyOneBQ_5288177 : Nat.Prime 5288177 := by norm_num
private theorem prime_seventyOneBQ_5453977 : Nat.Prime 5453977 := by norm_num
private theorem prime_seventyOneBQ_6088139 : Nat.Prime 6088139 := by norm_num
private theorem prime_seventyOneBQ_6154649 : Nat.Prime 6154649 := by norm_num
private theorem prime_seventyOneBQ_6583813 : Nat.Prime 6583813 := by norm_num
private theorem prime_seventyOneBQ_6604231 : Nat.Prime 6604231 := by norm_num
private theorem prime_seventyOneBQ_6632519 : Nat.Prime 6632519 := by norm_num
private theorem prime_seventyOneBQ_7273639 : Nat.Prime 7273639 := by norm_num
private theorem prime_seventyOneBQ_7340527 : Nat.Prime 7340527 := by norm_num
private theorem prime_seventyOneBQ_7433011 : Nat.Prime 7433011 := by norm_num
private theorem prime_seventyOneBQ_7914479 : Nat.Prime 7914479 := by norm_num
private theorem prime_seventyOneBQ_8375491 : Nat.Prime 8375491 := by norm_num
private theorem prime_seventyOneBQ_8845861 : Nat.Prime 8845861 := by norm_num
private theorem prime_seventyOneBQ_8876083 : Nat.Prime 8876083 := by norm_num
private theorem prime_seventyOneBQ_9154309 : Nat.Prime 9154309 := by norm_num
private theorem prime_seventyOneBQ_9176861 : Nat.Prime 9176861 := by norm_num
private theorem prime_seventyOneBQ_9259267 : Nat.Prime 9259267 := by norm_num
private theorem prime_seventyOneBQ_9467327 : Nat.Prime 9467327 := by norm_num
private theorem prime_seventyOneBQ_10073983 : Nat.Prime 10073983 := by norm_num
private theorem prime_seventyOneBQ_10576259 : Nat.Prime 10576259 := by norm_num
private theorem prime_seventyOneBQ_11066563 : Nat.Prime 11066563 := by norm_num
private theorem prime_seventyOneBQ_13395617 : Nat.Prime 13395617 := by norm_num
private theorem prime_seventyOneBQ_15572573 : Nat.Prime 15572573 := by norm_num
private theorem prime_seventyOneBQ_16023107 : Nat.Prime 16023107 := by norm_num
private theorem prime_seventyOneBQ_17048561 : Nat.Prime 17048561 := by norm_num
private theorem prime_seventyOneBQ_17261357 : Nat.Prime 17261357 := by norm_num
private theorem prime_seventyOneBQ_17311913 : Nat.Prime 17311913 := by norm_num
private theorem prime_seventyOneBQ_19747891 : Nat.Prime 19747891 := by norm_num
private theorem prime_seventyOneBQ_19806181 : Nat.Prime 19806181 := by norm_num
private theorem prime_seventyOneBQ_20028629 : Nat.Prime 20028629 := by norm_num
private theorem prime_seventyOneBQ_22959263 : Nat.Prime 22959263 := by norm_num
private theorem prime_seventyOneBQ_23552471 : Nat.Prime 23552471 := by norm_num
private theorem prime_seventyOneBQ_26779033 : Nat.Prime 26779033 := by norm_num
private theorem prime_seventyOneBQ_29150809 : Nat.Prime 29150809 := by norm_num
private theorem prime_seventyOneBQ_33650269 : Nat.Prime 33650269 := by
  apply lucas_primality 33650269 (2 : ZMod 33650269)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2804189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2804189, 1)] : List FactorBlock).map factorBlockValue).prod) = 33650269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_2804189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 33650269) ^ 16825134 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 33650269) ^ 11216756 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 33650269) ^ 12 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_33941773 : Nat.Prime 33941773 := by
  apply lucas_primality 33941773 (6 : ZMod 33941773)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (942827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (942827, 1)] : List FactorBlock).map factorBlockValue).prod) = 33941773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_942827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 33941773) ^ 16970886 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 33941773) ^ 11313924 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 33941773) ^ 36 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_34753837 : Nat.Prime 34753837 := by
  apply lucas_primality 34753837 (6 : ZMod 34753837)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 2), (17137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 2), (17137, 1)] : List FactorBlock).map factorBlockValue).prod) = 34753837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_13
      · exact prime_seventyOneBQ_17137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 34753837) ^ 17376918 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 34753837) ^ 11584612 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 34753837) ^ 2673372 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 34753837) ^ 2028 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_37095059 : Nat.Prime 37095059 := by
  apply lucas_primality 37095059 (6 : ZMod 37095059)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (11, 1), (13, 1), (2647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (11, 1), (13, 1), (2647, 1)] : List FactorBlock).map factorBlockValue).prod) = 37095059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_11
      · exact prime_seventyOneBQ_13
      · exact prime_seventyOneBQ_2647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 37095059) ^ 18547529 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 37095059) ^ 5299294 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 37095059) ^ 3372278 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 37095059) ^ 2853466 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 37095059) ^ 14014 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_39090587 : Nat.Prime 39090587 := by
  apply lucas_primality 39090587 (2 : ZMod 39090587)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1381, 1), (14153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1381, 1), (14153, 1)] : List FactorBlock).map factorBlockValue).prod) = 39090587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_1381
      · exact prime_seventyOneBQ_14153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 39090587) ^ 19545293 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 39090587) ^ 28306 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 39090587) ^ 2762 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_40742123 : Nat.Prime 40742123 := by
  apply lucas_primality 40742123 (2 : ZMod 40742123)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (657131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (657131, 1)] : List FactorBlock).map factorBlockValue).prod) = 40742123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_31
      · exact prime_seventyOneBQ_657131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 40742123) ^ 20371061 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 40742123) ^ 1314262 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 40742123) ^ 62 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_41144869 : Nat.Prime 41144869 := by
  apply lucas_primality 41144869 (2 : ZMod 41144869)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (380971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (380971, 1)] : List FactorBlock).map factorBlockValue).prod) = 41144869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_380971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 41144869) ^ 20572434 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 41144869) ^ 13714956 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 41144869) ^ 108 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_53060153 : Nat.Prime 53060153 := by
  apply lucas_primality 53060153 (3 : ZMod 53060153)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (6632519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (6632519, 1)] : List FactorBlock).map factorBlockValue).prod) = 53060153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_6632519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 53060153) ^ 26530076 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 53060153) ^ 8 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_53545747 : Nat.Prime 53545747 := by
  apply lucas_primality 53545747 (2 : ZMod 53545747)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (97, 1), (92003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (97, 1), (92003, 1)] : List FactorBlock).map factorBlockValue).prod) = 53545747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_97
      · exact prime_seventyOneBQ_92003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 53545747) ^ 26772873 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 53545747) ^ 17848582 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 53545747) ^ 552018 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 53545747) ^ 582 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_55064879 : Nat.Prime 55064879 := by
  apply lucas_primality 55064879 (7 : ZMod 55064879)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (653, 1), (3833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (653, 1), (3833, 1)] : List FactorBlock).map factorBlockValue).prod) = 55064879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_11
      · exact prime_seventyOneBQ_653
      · exact prime_seventyOneBQ_3833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 55064879) ^ 27532439 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 55064879) ^ 5005898 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 55064879) ^ 84326 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 55064879) ^ 14366 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_61298071 : Nat.Prime 61298071 := by
  apply lucas_primality 61298071 (3 : ZMod 61298071)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (2043269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (2043269, 1)] : List FactorBlock).map factorBlockValue).prod) = 61298071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_2043269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 61298071) ^ 30649035 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 61298071) ^ 20432690 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 61298071) ^ 12259614 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 61298071) ^ 30 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_61476887 : Nat.Prime 61476887 := by
  apply lucas_primality 61476887 (5 : ZMod 61476887)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (839, 1), (36637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (839, 1), (36637, 1)] : List FactorBlock).map factorBlockValue).prod) = 61476887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_839
      · exact prime_seventyOneBQ_36637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 61476887) ^ 30738443 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 61476887) ^ 73274 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 61476887) ^ 1678 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_61779701 : Nat.Prime 61779701 := by
  apply lucas_primality 61779701 (2 : ZMod 61779701)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (17, 1), (36341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (17, 1), (36341, 1)] : List FactorBlock).map factorBlockValue).prod) = 61779701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_17
      · exact prime_seventyOneBQ_36341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 61779701) ^ 30889850 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 61779701) ^ 12355940 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 61779701) ^ 3634100 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 61779701) ^ 1700 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_65952889 : Nat.Prime 65952889 := by
  apply lucas_primality 65952889 (13 : ZMod 65952889)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2748037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2748037, 1)] : List FactorBlock).map factorBlockValue).prod) = 65952889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_2748037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 65952889) ^ 32976444 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (13 : ZMod 65952889) ^ 21984296 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (13 : ZMod 65952889) ^ 24 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_66042311 : Nat.Prime 66042311 := by
  apply lucas_primality 66042311 (11 : ZMod 66042311)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (6604231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (6604231, 1)] : List FactorBlock).map factorBlockValue).prod) = 66042311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_6604231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 66042311) ^ 33021155 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 66042311) ^ 13208462 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 66042311) ^ 10 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_67175557 : Nat.Prime 67175557 := by
  apply lucas_primality 67175557 (2 : ZMod 67175557)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (827, 1), (967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (827, 1), (967, 1)] : List FactorBlock).map factorBlockValue).prod) = 67175557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_827
      · exact prime_seventyOneBQ_967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 67175557) ^ 33587778 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 67175557) ^ 22391852 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 67175557) ^ 9596508 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 67175557) ^ 81228 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 67175557) ^ 69468 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_75893381 : Nat.Prime 75893381 := by
  apply lucas_primality 75893381 (2 : ZMod 75893381)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (811, 1), (4679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (811, 1), (4679, 1)] : List FactorBlock).map factorBlockValue).prod) = 75893381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_811
      · exact prime_seventyOneBQ_4679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 75893381) ^ 37946690 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 75893381) ^ 15178676 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 75893381) ^ 93580 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 75893381) ^ 16220 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_75994151 : Nat.Prime 75994151 := by
  apply lucas_primality 75994151 (7 : ZMod 75994151)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (1519883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (1519883, 1)] : List FactorBlock).map factorBlockValue).prod) = 75994151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_1519883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 75994151) ^ 37997075 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 75994151) ^ 15198830 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 75994151) ^ 50 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_82123907 : Nat.Prime 82123907 := by
  apply lucas_primality 82123907 (2 : ZMod 82123907)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (2415409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (2415409, 1)] : List FactorBlock).map factorBlockValue).prod) = 82123907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_17
      · exact prime_seventyOneBQ_2415409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 82123907) ^ 41061953 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 82123907) ^ 4830818 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 82123907) ^ 34 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_84610073 : Nat.Prime 84610073 := by
  apply lucas_primality 84610073 (3 : ZMod 84610073)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (10576259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (10576259, 1)] : List FactorBlock).map factorBlockValue).prod) = 84610073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_10576259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 84610073) ^ 42305036 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 84610073) ^ 8 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_90188977 : Nat.Prime 90188977 := by
  apply lucas_primality 90188977 (5 : ZMod 90188977)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (1213, 1), (1549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (1213, 1), (1549, 1)] : List FactorBlock).map factorBlockValue).prod) = 90188977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_1213
      · exact prime_seventyOneBQ_1549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 90188977) ^ 45094488 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 90188977) ^ 30062992 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 90188977) ^ 74352 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 90188977) ^ 58224 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_95187187 : Nat.Prime 95187187 := by
  apply lucas_primality 95187187 (2 : ZMod 95187187)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5288177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5288177, 1)] : List FactorBlock).map factorBlockValue).prod) = 95187187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_5288177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 95187187) ^ 47593593 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 95187187) ^ 31729062 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 95187187) ^ 18 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_97244171 : Nat.Prime 97244171 := by
  apply lucas_primality 97244171 (6 : ZMod 97244171)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (163, 1), (59659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (163, 1), (59659, 1)] : List FactorBlock).map factorBlockValue).prod) = 97244171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_163
      · exact prime_seventyOneBQ_59659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 97244171) ^ 48622085 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 97244171) ^ 19448834 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 97244171) ^ 596590 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 97244171) ^ 1630 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_101872609 : Nat.Prime 101872609 := by
  apply lucas_primality 101872609 (7 : ZMod 101872609)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (487, 1), (2179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (487, 1), (2179, 1)] : List FactorBlock).map factorBlockValue).prod) = 101872609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_487
      · exact prime_seventyOneBQ_2179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 101872609) ^ 50936304 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 101872609) ^ 33957536 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 101872609) ^ 209184 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 101872609) ^ 46752 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_106150333 : Nat.Prime 106150333 := by
  apply lucas_primality 106150333 (2 : ZMod 106150333)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (8845861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (8845861, 1)] : List FactorBlock).map factorBlockValue).prod) = 106150333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_8845861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 106150333) ^ 53075166 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 106150333) ^ 35383444 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 106150333) ^ 12 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_109683463 : Nat.Prime 109683463 := by
  apply lucas_primality 109683463 (5 : ZMod 109683463)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (373073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (373073, 1)] : List FactorBlock).map factorBlockValue).prod) = 109683463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_373073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 109683463) ^ 54841731 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 109683463) ^ 36561154 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 109683463) ^ 15669066 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 109683463) ^ 294 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_110129759 : Nat.Prime 110129759 := by
  apply lucas_primality 110129759 (11 : ZMod 110129759)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (55064879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (55064879, 1)] : List FactorBlock).map factorBlockValue).prod) = 110129759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_55064879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 110129759) ^ 55064879 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 110129759) ^ 2 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_116120051 : Nat.Prime 116120051 := by
  apply lucas_primality 116120051 (6 : ZMod 116120051)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (2322401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (2322401, 1)] : List FactorBlock).map factorBlockValue).prod) = 116120051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_2322401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 116120051) ^ 58060025 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 116120051) ^ 23224010 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 116120051) ^ 50 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_117191507 : Nat.Prime 117191507 := by
  apply lucas_primality 117191507 (2 : ZMod 117191507)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (19, 1), (37, 1), (4903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (19, 1), (37, 1), (4903, 1)] : List FactorBlock).map factorBlockValue).prod) = 117191507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_17
      · exact prime_seventyOneBQ_19
      · exact prime_seventyOneBQ_37
      · exact prime_seventyOneBQ_4903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 117191507) ^ 58595753 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 117191507) ^ 6893618 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 117191507) ^ 6167974 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 117191507) ^ 3167338 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 117191507) ^ 23902 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_121484777 : Nat.Prime 121484777 := by
  apply lucas_primality 121484777 (3 : ZMod 121484777)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (59, 1), (83, 1), (443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (59, 1), (83, 1), (443, 1)] : List FactorBlock).map factorBlockValue).prod) = 121484777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_59
      · exact prime_seventyOneBQ_83
      · exact prime_seventyOneBQ_443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 121484777) ^ 60742388 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 121484777) ^ 17354968 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 121484777) ^ 2059064 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 121484777) ^ 1463672 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 121484777) ^ 274232 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_121581259 : Nat.Prime 121581259 := by
  apply lucas_primality 121581259 (2 : ZMod 121581259)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (53, 1), (382331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (53, 1), (382331, 1)] : List FactorBlock).map factorBlockValue).prod) = 121581259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_53
      · exact prime_seventyOneBQ_382331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 121581259) ^ 60790629 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 121581259) ^ 40527086 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 121581259) ^ 2293986 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 121581259) ^ 318 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_131418821 : Nat.Prime 131418821 := by
  apply lucas_primality 131418821 (2 : ZMod 131418821)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (19, 1), (37, 1), (719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (19, 1), (37, 1), (719, 1)] : List FactorBlock).map factorBlockValue).prod) = 131418821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_13
      · exact prime_seventyOneBQ_19
      · exact prime_seventyOneBQ_37
      · exact prime_seventyOneBQ_719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 131418821) ^ 65709410 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 131418821) ^ 26283764 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 131418821) ^ 10109140 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 131418821) ^ 6916780 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 131418821) ^ 3551860 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 131418821) ^ 182780 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_132254323 : Nat.Prime 132254323 := by
  apply lucas_primality 132254323 (2 : ZMod 132254323)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (367, 1), (3533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (367, 1), (3533, 1)] : List FactorBlock).map factorBlockValue).prod) = 132254323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_17
      · exact prime_seventyOneBQ_367
      · exact prime_seventyOneBQ_3533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 132254323) ^ 66127161 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 132254323) ^ 44084774 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 132254323) ^ 7779666 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 132254323) ^ 360366 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 132254323) ^ 37434 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_133569937 : Nat.Prime 133569937 := by
  apply lucas_primality 133569937 (5 : ZMod 133569937)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (927569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (927569, 1)] : List FactorBlock).map factorBlockValue).prod) = 133569937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_927569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 133569937) ^ 66784968 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 133569937) ^ 44523312 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 133569937) ^ 144 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_134193919 : Nat.Prime 134193919 := by
  apply lucas_primality 134193919 (3 : ZMod 134193919)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1163, 1), (19231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1163, 1), (19231, 1)] : List FactorBlock).map factorBlockValue).prod) = 134193919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_1163
      · exact prime_seventyOneBQ_19231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 134193919) ^ 67096959 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 134193919) ^ 44731306 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 134193919) ^ 115386 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 134193919) ^ 6978 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_151988303 : Nat.Prime 151988303 := by
  apply lucas_primality 151988303 (5 : ZMod 151988303)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (75994151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (75994151, 1)] : List FactorBlock).map factorBlockValue).prod) = 151988303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_75994151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 151988303) ^ 75994151 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 151988303) ^ 2 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_166906601 : Nat.Prime 166906601 := by
  apply lucas_primality 166906601 (17 : ZMod 166906601)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (7, 1), (29, 1), (4111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (7, 1), (29, 1), (4111, 1)] : List FactorBlock).map factorBlockValue).prod) = 166906601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_29
      · exact prime_seventyOneBQ_4111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 166906601) ^ 83453300 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (17 : ZMod 166906601) ^ 33381320 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (17 : ZMod 166906601) ^ 23843800 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (17 : ZMod 166906601) ^ 5755400 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (17 : ZMod 166906601) ^ 40600 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_167670739 : Nat.Prime 167670739 := by
  apply lucas_primality 167670739 (3 : ZMod 167670739)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (137, 1), (67993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (137, 1), (67993, 1)] : List FactorBlock).map factorBlockValue).prod) = 167670739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_137
      · exact prime_seventyOneBQ_67993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 167670739) ^ 83835369 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 167670739) ^ 55890246 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 167670739) ^ 1223874 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 167670739) ^ 2466 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_171287423 : Nat.Prime 171287423 := by
  apply lucas_primality 171287423 (5 : ZMod 171287423)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (2088871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (2088871, 1)] : List FactorBlock).map factorBlockValue).prod) = 171287423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_41
      · exact prime_seventyOneBQ_2088871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 171287423) ^ 85643711 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 171287423) ^ 4177742 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 171287423) ^ 82 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_171755357 : Nat.Prime 171755357 := by
  apply lucas_primality 171755357 (2 : ZMod 171755357)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2213, 1), (19403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2213, 1), (19403, 1)] : List FactorBlock).map factorBlockValue).prod) = 171755357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_2213
      · exact prime_seventyOneBQ_19403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 171755357) ^ 85877678 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 171755357) ^ 77612 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 171755357) ^ 8852 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_178062229 : Nat.Prime 178062229 := by
  apply lucas_primality 178062229 (6 : ZMod 178062229)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (23, 1), (215051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (23, 1), (215051, 1)] : List FactorBlock).map factorBlockValue).prod) = 178062229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_23
      · exact prime_seventyOneBQ_215051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 178062229) ^ 89031114 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 178062229) ^ 59354076 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 178062229) ^ 7741836 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 178062229) ^ 828 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_184505779 : Nat.Prime 184505779 := by
  apply lucas_primality 184505779 (2 : ZMod 184505779)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1061, 1), (9661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1061, 1), (9661, 1)] : List FactorBlock).map factorBlockValue).prod) = 184505779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_1061
      · exact prime_seventyOneBQ_9661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 184505779) ^ 92252889 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 184505779) ^ 61501926 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 184505779) ^ 173898 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 184505779) ^ 19098 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_195035671 : Nat.Prime 195035671 := by
  apply lucas_primality 195035671 (3 : ZMod 195035671)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (2167063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (2167063, 1)] : List FactorBlock).map factorBlockValue).prod) = 195035671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_2167063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 195035671) ^ 97517835 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 195035671) ^ 65011890 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 195035671) ^ 39007134 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 195035671) ^ 90 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_210670619 : Nat.Prime 210670619 := by
  apply lucas_primality 210670619 (2 : ZMod 210670619)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (197, 1), (534697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (197, 1), (534697, 1)] : List FactorBlock).map factorBlockValue).prod) = 210670619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_197
      · exact prime_seventyOneBQ_534697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 210670619) ^ 105335309 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 210670619) ^ 1069394 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 210670619) ^ 394 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_214182989 : Nat.Prime 214182989 := by
  apply lucas_primality 214182989 (2 : ZMod 214182989)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (53545747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (53545747, 1)] : List FactorBlock).map factorBlockValue).prod) = 214182989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_53545747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 214182989) ^ 107091494 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 214182989) ^ 4 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_254735839 : Nat.Prime 254735839 := by
  apply lucas_primality 254735839 (3 : ZMod 254735839)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (127, 1), (15919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (127, 1), (15919, 1)] : List FactorBlock).map factorBlockValue).prod) = 254735839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_127
      · exact prime_seventyOneBQ_15919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 254735839) ^ 127367919 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 254735839) ^ 84911946 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 254735839) ^ 36390834 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 254735839) ^ 2005794 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 254735839) ^ 16002 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_263811557 : Nat.Prime 263811557 := by
  apply lucas_primality 263811557 (2 : ZMod 263811557)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (65952889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (65952889, 1)] : List FactorBlock).map factorBlockValue).prod) = 263811557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_65952889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 263811557) ^ 131905778 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 263811557) ^ 4 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_296228099 : Nat.Prime 296228099 := by
  apply lucas_primality 296228099 (2 : ZMod 296228099)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (5107381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (5107381, 1)] : List FactorBlock).map factorBlockValue).prod) = 296228099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_29
      · exact prime_seventyOneBQ_5107381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 296228099) ^ 148114049 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 296228099) ^ 10214762 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 296228099) ^ 58 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_303027271 : Nat.Prime 303027271 := by
  apply lucas_primality 303027271 (7 : ZMod 303027271)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 2), (13, 1), (101, 1), (157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 2), (13, 1), (101, 1), (157, 1)] : List FactorBlock).map factorBlockValue).prod) = 303027271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_13
      · exact prime_seventyOneBQ_101
      · exact prime_seventyOneBQ_157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 303027271) ^ 151513635 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 303027271) ^ 101009090 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 303027271) ^ 60605454 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 303027271) ^ 43289610 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 303027271) ^ 23309790 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 303027271) ^ 3000270 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 303027271) ^ 1930110 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_310069687 : Nat.Prime 310069687 := by
  apply lucas_primality 310069687 (3 : ZMod 310069687)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2473, 1), (20897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2473, 1), (20897, 1)] : List FactorBlock).map factorBlockValue).prod) = 310069687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_2473
      · exact prime_seventyOneBQ_20897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 310069687) ^ 155034843 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 310069687) ^ 103356562 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 310069687) ^ 125382 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 310069687) ^ 14838 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_346614571 : Nat.Prime 346614571 := by
  apply lucas_primality 346614571 (7 : ZMod 346614571)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (103, 1), (139, 1), (269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (103, 1), (139, 1), (269, 1)] : List FactorBlock).map factorBlockValue).prod) = 346614571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_103
      · exact prime_seventyOneBQ_139
      · exact prime_seventyOneBQ_269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 346614571) ^ 173307285 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 346614571) ^ 115538190 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 346614571) ^ 69322914 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 346614571) ^ 3365190 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 346614571) ^ 2493630 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 346614571) ^ 1288530 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_360755909 : Nat.Prime 360755909 := by
  apply lucas_primality 360755909 (2 : ZMod 360755909)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (90188977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (90188977, 1)] : List FactorBlock).map factorBlockValue).prod) = 360755909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_90188977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 360755909) ^ 180377954 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 360755909) ^ 4 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_385291523 : Nat.Prime 385291523 := by
  apply lucas_primality 385291523 (2 : ZMod 385291523)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (569, 1), (4397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (569, 1), (4397, 1)] : List FactorBlock).map factorBlockValue).prod) = 385291523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_11
      · exact prime_seventyOneBQ_569
      · exact prime_seventyOneBQ_4397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 385291523) ^ 192645761 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 385291523) ^ 55041646 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 385291523) ^ 35026502 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 385291523) ^ 677138 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 385291523) ^ 87626 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_398396269 : Nat.Prime 398396269 := by
  apply lucas_primality 398396269 (6 : ZMod 398396269)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11066563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11066563, 1)] : List FactorBlock).map factorBlockValue).prod) = 398396269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_11066563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 398396269) ^ 199198134 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 398396269) ^ 132798756 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 398396269) ^ 36 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_452500669 : Nat.Prime 452500669 := by
  apply lucas_primality 452500669 (6 : ZMod 452500669)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (1396607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (1396607, 1)] : List FactorBlock).map factorBlockValue).prod) = 452500669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_1396607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 452500669) ^ 226250334 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 452500669) ^ 150833556 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 452500669) ^ 324 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_489120383 : Nat.Prime 489120383 := by
  apply lucas_primality 489120383 (5 : ZMod 489120383)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (307, 1), (41927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (307, 1), (41927, 1)] : List FactorBlock).map factorBlockValue).prod) = 489120383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_19
      · exact prime_seventyOneBQ_307
      · exact prime_seventyOneBQ_41927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 489120383) ^ 244560191 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 489120383) ^ 25743178 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 489120383) ^ 1593226 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 489120383) ^ 11666 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_507296863 : Nat.Prime 507296863 := by
  apply lucas_primality 507296863 (3 : ZMod 507296863)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (37, 1), (61, 1), (12487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (37, 1), (61, 1), (12487, 1)] : List FactorBlock).map factorBlockValue).prod) = 507296863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_37
      · exact prime_seventyOneBQ_61
      · exact prime_seventyOneBQ_12487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 507296863) ^ 253648431 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 507296863) ^ 169098954 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 507296863) ^ 13710726 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 507296863) ^ 8316342 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 507296863) ^ 40626 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_518765383 : Nat.Prime 518765383 := by
  apply lucas_primality 518765383 (3 : ZMod 518765383)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (37, 1), (778927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (37, 1), (778927, 1)] : List FactorBlock).map factorBlockValue).prod) = 518765383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_37
      · exact prime_seventyOneBQ_778927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 518765383) ^ 259382691 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 518765383) ^ 172921794 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 518765383) ^ 14020686 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 518765383) ^ 666 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_536775677 : Nat.Prime 536775677 := by
  apply lucas_primality 536775677 (2 : ZMod 536775677)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (134193919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (134193919, 1)] : List FactorBlock).map factorBlockValue).prod) = 536775677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_134193919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 536775677) ^ 268387838 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 536775677) ^ 4 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_568039621 : Nat.Prime 568039621 := by
  apply lucas_primality 568039621 (2 : ZMod 568039621)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (9467327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (9467327, 1)] : List FactorBlock).map factorBlockValue).prod) = 568039621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_9467327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 568039621) ^ 284019810 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 568039621) ^ 189346540 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 568039621) ^ 113607924 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 568039621) ^ 60 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_579685373 : Nat.Prime 579685373 := by
  apply lucas_primality 579685373 (2 : ZMod 579685373)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (461, 1), (44909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (461, 1), (44909, 1)] : List FactorBlock).map factorBlockValue).prod) = 579685373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_461
      · exact prime_seventyOneBQ_44909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 579685373) ^ 289842686 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 579685373) ^ 82812196 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 579685373) ^ 1257452 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 579685373) ^ 12908 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_584490169 : Nat.Prime 584490169 := by
  apply lucas_primality 584490169 (11 : ZMod 584490169)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (23, 1), (39217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (23, 1), (39217, 1)] : List FactorBlock).map factorBlockValue).prod) = 584490169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_23
      · exact prime_seventyOneBQ_39217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 584490169) ^ 292245084 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 584490169) ^ 194830056 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 584490169) ^ 25412616 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 584490169) ^ 14904 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_664816237 : Nat.Prime 664816237 := by
  apply lucas_primality 664816237 (5 : ZMod 664816237)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (7914479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (7914479, 1)] : List FactorBlock).map factorBlockValue).prod) = 664816237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_7914479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 664816237) ^ 332408118 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 664816237) ^ 221605412 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 664816237) ^ 94973748 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 664816237) ^ 84 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_669780851 : Nat.Prime 669780851 := by
  apply lucas_primality 669780851 (2 : ZMod 669780851)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (13395617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (13395617, 1)] : List FactorBlock).map factorBlockValue).prod) = 669780851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_13395617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 669780851) ^ 334890425 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 669780851) ^ 133956170 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 669780851) ^ 50 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_703149043 : Nat.Prime 703149043 := by
  apply lucas_primality 703149043 (2 : ZMod 703149043)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (117191507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (117191507, 1)] : List FactorBlock).map factorBlockValue).prod) = 703149043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_117191507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 703149043) ^ 351574521 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 703149043) ^ 234383014 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 703149043) ^ 6 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_787975393 : Nat.Prime 787975393 := by
  apply lucas_primality 787975393 (5 : ZMod 787975393)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (41, 1), (107, 1), (1871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (41, 1), (107, 1), (1871, 1)] : List FactorBlock).map factorBlockValue).prod) = 787975393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_41
      · exact prime_seventyOneBQ_107
      · exact prime_seventyOneBQ_1871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 787975393) ^ 393987696 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 787975393) ^ 262658464 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 787975393) ^ 19218912 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 787975393) ^ 7364256 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 787975393) ^ 421152 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_794103809 : Nat.Prime 794103809 := by
  apply lucas_primality 794103809 (3 : ZMod 794103809)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 12), (193873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 12), (193873, 1)] : List FactorBlock).map factorBlockValue).prod) = 794103809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_193873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 794103809) ^ 397051904 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 794103809) ^ 4096 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_803696251 : Nat.Prime 803696251 := by
  apply lucas_primality 803696251 (2 : ZMod 803696251)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 4), (7, 1), (17, 1), (1801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 4), (7, 1), (17, 1), (1801, 1)] : List FactorBlock).map factorBlockValue).prod) = 803696251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_17
      · exact prime_seventyOneBQ_1801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 803696251) ^ 401848125 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 803696251) ^ 267898750 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 803696251) ^ 160739250 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 803696251) ^ 114813750 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 803696251) ^ 47276250 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 803696251) ^ 446250 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_832419667 : Nat.Prime 832419667 := by
  apply lucas_primality 832419667 (2 : ZMod 832419667)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (13, 1), (395261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (13, 1), (395261, 1)] : List FactorBlock).map factorBlockValue).prod) = 832419667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_13
      · exact prime_seventyOneBQ_395261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 832419667) ^ 416209833 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 832419667) ^ 277473222 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 832419667) ^ 64032282 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 832419667) ^ 2106 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_897308257 : Nat.Prime 897308257 := by
  apply lucas_primality 897308257 (5 : ZMod 897308257)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (13, 1), (29, 1), (24793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (13, 1), (29, 1), (24793, 1)] : List FactorBlock).map factorBlockValue).prod) = 897308257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_13
      · exact prime_seventyOneBQ_29
      · exact prime_seventyOneBQ_24793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 897308257) ^ 448654128 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 897308257) ^ 299102752 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 897308257) ^ 69023712 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 897308257) ^ 30941664 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 897308257) ^ 36192 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_1084467809 : Nat.Prime 1084467809 := by
  apply lucas_primality 1084467809 (3 : ZMod 1084467809)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (17, 1), (1993507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (17, 1), (1993507, 1)] : List FactorBlock).map factorBlockValue).prod) = 1084467809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_17
      · exact prime_seventyOneBQ_1993507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1084467809) ^ 542233904 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1084467809) ^ 63792224 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1084467809) ^ 544 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_1157027251 : Nat.Prime 1157027251 := by
  apply lucas_primality 1157027251 (3 : ZMod 1157027251)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (1542703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (1542703, 1)] : List FactorBlock).map factorBlockValue).prod) = 1157027251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_1542703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1157027251) ^ 578513625 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1157027251) ^ 385675750 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1157027251) ^ 231405450 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1157027251) ^ 750 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_1223078641 : Nat.Prime 1223078641 := by
  apply lucas_primality 1223078641 (13 : ZMod 1223078641)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (7, 1), (19, 1), (38317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (7, 1), (19, 1), (38317, 1)] : List FactorBlock).map factorBlockValue).prod) = 1223078641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_19
      · exact prime_seventyOneBQ_38317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 1223078641) ^ 611539320 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (13 : ZMod 1223078641) ^ 407692880 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (13 : ZMod 1223078641) ^ 244615728 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (13 : ZMod 1223078641) ^ 174725520 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (13 : ZMod 1223078641) ^ 64372560 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (13 : ZMod 1223078641) ^ 31920 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_1430218333 : Nat.Prime 1430218333 := by
  apply lucas_primality 1430218333 (2 : ZMod 1430218333)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (431, 1), (92177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (431, 1), (92177, 1)] : List FactorBlock).map factorBlockValue).prod) = 1430218333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_431
      · exact prime_seventyOneBQ_92177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1430218333) ^ 715109166 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1430218333) ^ 476739444 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1430218333) ^ 3318372 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1430218333) ^ 15516 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_1528274387 : Nat.Prime 1528274387 := by
  apply lucas_primality 1528274387 (2 : ZMod 1528274387)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (197, 1), (204151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (197, 1), (204151, 1)] : List FactorBlock).map factorBlockValue).prod) = 1528274387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_19
      · exact prime_seventyOneBQ_197
      · exact prime_seventyOneBQ_204151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1528274387) ^ 764137193 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1528274387) ^ 80435494 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1528274387) ^ 7757738 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1528274387) ^ 7486 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_1666704353 : Nat.Prime 1666704353 := by
  apply lucas_primality 1666704353 (3 : ZMod 1666704353)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3529, 1), (14759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3529, 1), (14759, 1)] : List FactorBlock).map factorBlockValue).prod) = 1666704353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3529
      · exact prime_seventyOneBQ_14759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1666704353) ^ 833352176 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1666704353) ^ 472288 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1666704353) ^ 112928 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_2077326913 : Nat.Prime 2077326913 := by
  apply lucas_primality 2077326913 (5 : ZMod 2077326913)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (113, 1), (95747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (113, 1), (95747, 1)] : List FactorBlock).map factorBlockValue).prod) = 2077326913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_113
      · exact prime_seventyOneBQ_95747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2077326913) ^ 1038663456 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2077326913) ^ 692442304 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2077326913) ^ 18383424 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2077326913) ^ 21696 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_2414794093 : Nat.Prime 2414794093 := by
  apply lucas_primality 2414794093 (2 : ZMod 2414794093)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (631, 1), (318911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (631, 1), (318911, 1)] : List FactorBlock).map factorBlockValue).prod) = 2414794093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_631
      · exact prime_seventyOneBQ_318911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2414794093) ^ 1207397046 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2414794093) ^ 804931364 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2414794093) ^ 3826932 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2414794093) ^ 7572 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_2591049443 : Nat.Prime 2591049443 := by
  apply lucas_primality 2591049443 (2 : ZMod 2591049443)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1009, 1), (1283969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1009, 1), (1283969, 1)] : List FactorBlock).map factorBlockValue).prod) = 2591049443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_1009
      · exact prime_seventyOneBQ_1283969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2591049443) ^ 1295524721 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2591049443) ^ 2567938 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2591049443) ^ 2018 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_2832782977 : Nat.Prime 2832782977 := by
  apply lucas_primality 2832782977 (5 : ZMod 2832782977)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (31, 1), (137, 1), (193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (31, 1), (137, 1), (193, 1)] : List FactorBlock).map factorBlockValue).prod) = 2832782977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_31
      · exact prime_seventyOneBQ_137
      · exact prime_seventyOneBQ_193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2832782977) ^ 1416391488 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2832782977) ^ 944260992 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2832782977) ^ 91380096 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2832782977) ^ 20677248 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2832782977) ^ 14677632 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_3090075623 : Nat.Prime 3090075623 := by
  apply lucas_primality 3090075623 (5 : ZMod 3090075623)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (67175557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (67175557, 1)] : List FactorBlock).map factorBlockValue).prod) = 3090075623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_23
      · exact prime_seventyOneBQ_67175557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3090075623) ^ 1545037811 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 3090075623) ^ 134351114 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 3090075623) ^ 46 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_3268432841 : Nat.Prime 3268432841 := by
  apply lucas_primality 3268432841 (3 : ZMod 3268432841)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (181, 1), (451441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (181, 1), (451441, 1)] : List FactorBlock).map factorBlockValue).prod) = 3268432841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_181
      · exact prime_seventyOneBQ_451441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3268432841) ^ 1634216420 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 3268432841) ^ 653686568 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 3268432841) ^ 18057640 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 3268432841) ^ 7240 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_3537432079 : Nat.Prime 3537432079 := by
  apply lucas_primality 3537432079 (3 : ZMod 3537432079)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1693, 1), (348241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1693, 1), (348241, 1)] : List FactorBlock).map factorBlockValue).prod) = 3537432079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_1693
      · exact prime_seventyOneBQ_348241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3537432079) ^ 1768716039 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 3537432079) ^ 1179144026 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 3537432079) ^ 2089446 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 3537432079) ^ 10158 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_6122501911 : Nat.Prime 6122501911 := by
  apply lucas_primality 6122501911 (3 : ZMod 6122501911)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (7, 1), (3239419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (7, 1), (3239419, 1)] : List FactorBlock).map factorBlockValue).prod) = 6122501911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_3239419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6122501911) ^ 3061250955 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 6122501911) ^ 2040833970 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 6122501911) ^ 1224500382 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 6122501911) ^ 874643130 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 6122501911) ^ 1890 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_6361720793 : Nat.Prime 6361720793 := by
  apply lucas_primality 6361720793 (3 : ZMod 6361720793)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (1601, 1), (70957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (1601, 1), (70957, 1)] : List FactorBlock).map factorBlockValue).prod) = 6361720793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_1601
      · exact prime_seventyOneBQ_70957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6361720793) ^ 3180860396 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 6361720793) ^ 908817256 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 6361720793) ^ 3973592 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 6361720793) ^ 89656 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_6942163507 : Nat.Prime 6942163507 := by
  apply lucas_primality 6942163507 (2 : ZMod 6942163507)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1157027251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1157027251, 1)] : List FactorBlock).map factorBlockValue).prod) = 6942163507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_1157027251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6942163507) ^ 3471081753 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6942163507) ^ 2314054502 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6942163507) ^ 6 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_8705775587 : Nat.Prime 8705775587 := by
  apply lucas_primality 8705775587 (2 : ZMod 8705775587)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (9377, 1), (20183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (9377, 1), (20183, 1)] : List FactorBlock).map factorBlockValue).prod) = 8705775587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_23
      · exact prime_seventyOneBQ_9377
      · exact prime_seventyOneBQ_20183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8705775587) ^ 4352887793 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 8705775587) ^ 378511982 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 8705775587) ^ 928418 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 8705775587) ^ 431342 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_10039094683 : Nat.Prime 10039094683 := by
  apply lucas_primality 10039094683 (3 : ZMod 10039094683)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31751, 1), (52697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31751, 1), (52697, 1)] : List FactorBlock).map factorBlockValue).prod) = 10039094683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_31751
      · exact prime_seventyOneBQ_52697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 10039094683) ^ 5019547341 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 10039094683) ^ 3346364894 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 10039094683) ^ 316182 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 10039094683) ^ 190506 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_10593489961 : Nat.Prime 10593489961 := by
  apply lucas_primality 10593489961 (7 : ZMod 10593489961)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (23, 1), (426469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (23, 1), (426469, 1)] : List FactorBlock).map factorBlockValue).prod) = 10593489961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_23
      · exact prime_seventyOneBQ_426469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 10593489961) ^ 5296744980 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 10593489961) ^ 3531163320 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 10593489961) ^ 2118697992 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 10593489961) ^ 460586520 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 10593489961) ^ 24840 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_11024095087 : Nat.Prime 11024095087 := by
  apply lucas_primality 11024095087 (3 : ZMod 11024095087)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (23, 1), (8876083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (23, 1), (8876083, 1)] : List FactorBlock).map factorBlockValue).prod) = 11024095087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_23
      · exact prime_seventyOneBQ_8876083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 11024095087) ^ 5512047543 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 11024095087) ^ 3674698362 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 11024095087) ^ 479308482 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 11024095087) ^ 1242 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_11754154457 : Nat.Prime 11754154457 := by
  apply lucas_primality 11754154457 (3 : ZMod 11754154457)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (133569937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (133569937, 1)] : List FactorBlock).map factorBlockValue).prod) = 11754154457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_11
      · exact prime_seventyOneBQ_133569937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 11754154457) ^ 5877077228 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 11754154457) ^ 1068559496 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 11754154457) ^ 88 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_13674802439 : Nat.Prime 13674802439 := by
  apply lucas_primality 13674802439 (7 : ZMod 13674802439)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (2267, 1), (274187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (2267, 1), (274187, 1)] : List FactorBlock).map factorBlockValue).prod) = 13674802439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_11
      · exact prime_seventyOneBQ_2267
      · exact prime_seventyOneBQ_274187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 13674802439) ^ 6837401219 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 13674802439) ^ 1243163858 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 13674802439) ^ 6032114 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 13674802439) ^ 49874 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_14012696989 : Nat.Prime 14012696989 := by
  apply lucas_primality 14012696989 (10 : ZMod 14012696989)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (16487, 1), (23609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (16487, 1), (23609, 1)] : List FactorBlock).map factorBlockValue).prod) = 14012696989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_16487
      · exact prime_seventyOneBQ_23609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 14012696989) ^ 7006348494 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (10 : ZMod 14012696989) ^ 4670898996 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (10 : ZMod 14012696989) ^ 849924 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (10 : ZMod 14012696989) ^ 593532 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_17244585521 : Nat.Prime 17244585521 := by
  apply lucas_primality 17244585521 (3 : ZMod 17244585521)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (29, 1), (7433011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (29, 1), (7433011, 1)] : List FactorBlock).map factorBlockValue).prod) = 17244585521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_29
      · exact prime_seventyOneBQ_7433011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 17244585521) ^ 8622292760 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 17244585521) ^ 3448917104 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 17244585521) ^ 594640880 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 17244585521) ^ 2320 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_18769805189 : Nat.Prime 18769805189 := by
  apply lucas_primality 18769805189 (2 : ZMod 18769805189)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1511, 1), (3105527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1511, 1), (3105527, 1)] : List FactorBlock).map factorBlockValue).prod) = 18769805189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_1511
      · exact prime_seventyOneBQ_3105527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 18769805189) ^ 9384902594 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 18769805189) ^ 12422108 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 18769805189) ^ 6044 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_19645792633 : Nat.Prime 19645792633 := by
  apply lucas_primality 19645792633 (7 : ZMod 19645792633)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (9137, 1), (29863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (9137, 1), (29863, 1)] : List FactorBlock).map factorBlockValue).prod) = 19645792633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_9137
      · exact prime_seventyOneBQ_29863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 19645792633) ^ 9822896316 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 19645792633) ^ 6548597544 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 19645792633) ^ 2150136 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 19645792633) ^ 657864 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_22363180369 : Nat.Prime 22363180369 := by
  apply lucas_primality 22363180369 (11 : ZMod 22363180369)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (103, 1), (4523297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (103, 1), (4523297, 1)] : List FactorBlock).map factorBlockValue).prod) = 22363180369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_103
      · exact prime_seventyOneBQ_4523297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 22363180369) ^ 11181590184 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 22363180369) ^ 7454393456 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 22363180369) ^ 217118256 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 22363180369) ^ 4944 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_22712085181 : Nat.Prime 22712085181 := by
  apply lucas_primality 22712085181 (2 : ZMod 22712085181)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (37, 1), (1136741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (37, 1), (1136741, 1)] : List FactorBlock).map factorBlockValue).prod) = 22712085181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_37
      · exact prime_seventyOneBQ_1136741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22712085181) ^ 11356042590 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 22712085181) ^ 7570695060 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 22712085181) ^ 4542417036 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 22712085181) ^ 613840140 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 22712085181) ^ 19980 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_25582946563 : Nat.Prime 25582946563 := by
  apply lucas_primality 25582946563 (3 : ZMod 25582946563)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1777, 1), (799817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1777, 1), (799817, 1)] : List FactorBlock).map factorBlockValue).prod) = 25582946563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_1777
      · exact prime_seventyOneBQ_799817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 25582946563) ^ 12791473281 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 25582946563) ^ 8527648854 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 25582946563) ^ 14396706 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 25582946563) ^ 31986 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_26749941329 : Nat.Prime 26749941329 := by
  apply lucas_primality 26749941329 (3 : ZMod 26749941329)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (151988303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (151988303, 1)] : List FactorBlock).map factorBlockValue).prod) = 26749941329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_11
      · exact prime_seventyOneBQ_151988303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 26749941329) ^ 13374970664 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 26749941329) ^ 2431812848 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 26749941329) ^ 176 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_29350003687 : Nat.Prime 29350003687 := by
  apply lucas_primality 29350003687 (5 : ZMod 29350003687)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (79, 1), (331, 1), (187069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (79, 1), (331, 1), (187069, 1)] : List FactorBlock).map factorBlockValue).prod) = 29350003687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_79
      · exact prime_seventyOneBQ_331
      · exact prime_seventyOneBQ_187069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 29350003687) ^ 14675001843 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 29350003687) ^ 9783334562 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 29350003687) ^ 371519034 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 29350003687) ^ 88670706 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 29350003687) ^ 156894 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_33837336371 : Nat.Prime 33837336371 := by
  apply lucas_primality 33837336371 (2 : ZMod 33837336371)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (4289, 1), (788933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (4289, 1), (788933, 1)] : List FactorBlock).map factorBlockValue).prod) = 33837336371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_4289
      · exact prime_seventyOneBQ_788933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 33837336371) ^ 16918668185 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 33837336371) ^ 6767467274 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 33837336371) ^ 7889330 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 33837336371) ^ 42890 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_34489171043 : Nat.Prime 34489171043 := by
  apply lucas_primality 34489171043 (2 : ZMod 34489171043)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17244585521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17244585521, 1)] : List FactorBlock).map factorBlockValue).prod) = 34489171043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_17244585521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 34489171043) ^ 17244585521 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 34489171043) ^ 2 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_35892330281 : Nat.Prime 35892330281 := by
  apply lucas_primality 35892330281 (3 : ZMod 35892330281)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (897308257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (897308257, 1)] : List FactorBlock).map factorBlockValue).prod) = 35892330281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_897308257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 35892330281) ^ 17946165140 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 35892330281) ^ 7178466056 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 35892330281) ^ 40 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_38120121019 : Nat.Prime 38120121019 := by
  apply lucas_primality 38120121019 (2 : ZMod 38120121019)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (7, 1), (23, 1), (487183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (7, 1), (23, 1), (487183, 1)] : List FactorBlock).map factorBlockValue).prod) = 38120121019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_23
      · exact prime_seventyOneBQ_487183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 38120121019) ^ 19060060509 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 38120121019) ^ 12706707006 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 38120121019) ^ 5445731574 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 38120121019) ^ 1657396566 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 38120121019) ^ 78246 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_39905635883 : Nat.Prime 39905635883 := by
  apply lucas_primality 39905635883 (2 : ZMod 39905635883)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 1), (167670739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 1), (167670739, 1)] : List FactorBlock).map factorBlockValue).prod) = 39905635883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_17
      · exact prime_seventyOneBQ_167670739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 39905635883) ^ 19952817941 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 39905635883) ^ 5700805126 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 39905635883) ^ 2347390346 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 39905635883) ^ 238 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_43308558151 : Nat.Prime 43308558151 := by
  apply lucas_primality 43308558151 (3 : ZMod 43308558151)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (11, 1), (13, 1), (2019047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (11, 1), (13, 1), (2019047, 1)] : List FactorBlock).map factorBlockValue).prod) = 43308558151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_11
      · exact prime_seventyOneBQ_13
      · exact prime_seventyOneBQ_2019047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 43308558151) ^ 21654279075 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 43308558151) ^ 14436186050 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 43308558151) ^ 8661711630 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 43308558151) ^ 3937141650 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 43308558151) ^ 3331427550 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 43308558151) ^ 21450 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_44792746241 : Nat.Prime 44792746241 := by
  apply lucas_primality 44792746241 (6 : ZMod 44792746241)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (5, 1), (11, 1), (19, 1), (167437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (5, 1), (11, 1), (19, 1), (167437, 1)] : List FactorBlock).map factorBlockValue).prod) = 44792746241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_11
      · exact prime_seventyOneBQ_19
      · exact prime_seventyOneBQ_167437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 44792746241) ^ 22396373120 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 44792746241) ^ 8958549248 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 44792746241) ^ 4072067840 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 44792746241) ^ 2357512960 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 44792746241) ^ 267520 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_50212244519 : Nat.Prime 50212244519 := by
  apply lucas_primality 50212244519 (13 : ZMod 50212244519)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (73, 1), (757, 1), (19753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (73, 1), (757, 1), (19753, 1)] : List FactorBlock).map factorBlockValue).prod) = 50212244519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_23
      · exact prime_seventyOneBQ_73
      · exact prime_seventyOneBQ_757
      · exact prime_seventyOneBQ_19753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 50212244519) ^ 25106122259 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (13 : ZMod 50212244519) ^ 2183141066 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (13 : ZMod 50212244519) ^ 687838966 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (13 : ZMod 50212244519) ^ 66330574 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (13 : ZMod 50212244519) ^ 2542006 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_60234568099 : Nat.Prime 60234568099 := by
  apply lucas_primality 60234568099 (19 : ZMod 60234568099)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (10039094683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (10039094683, 1)] : List FactorBlock).map factorBlockValue).prod) = 60234568099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_10039094683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (19 : ZMod 60234568099) ^ 30117284049 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (19 : ZMod 60234568099) ^ 20078189366 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (19 : ZMod 60234568099) ^ 6 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_64331854927 : Nat.Prime 64331854927 := by
  apply lucas_primality 64331854927 (5 : ZMod 64331854927)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (467, 1), (22959263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (467, 1), (22959263, 1)] : List FactorBlock).map factorBlockValue).prod) = 64331854927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_467
      · exact prime_seventyOneBQ_22959263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 64331854927) ^ 32165927463 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 64331854927) ^ 21443951642 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 64331854927) ^ 137755578 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 64331854927) ^ 2802 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_73004386297 : Nat.Prime 73004386297 := by
  apply lucas_primality 73004386297 (7 : ZMod 73004386297)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (132254323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (132254323, 1)] : List FactorBlock).map factorBlockValue).prod) = 73004386297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_23
      · exact prime_seventyOneBQ_132254323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 73004386297) ^ 36502193148 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 73004386297) ^ 24334795432 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 73004386297) ^ 3174103752 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 73004386297) ^ 552 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_97526946557 : Nat.Prime 97526946557 := by
  apply lucas_primality 97526946557 (2 : ZMod 97526946557)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 2), (67, 1), (521, 1), (4133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 2), (67, 1), (521, 1), (4133, 1)] : List FactorBlock).map factorBlockValue).prod) = 97526946557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_13
      · exact prime_seventyOneBQ_67
      · exact prime_seventyOneBQ_521
      · exact prime_seventyOneBQ_4133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 97526946557) ^ 48763473278 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 97526946557) ^ 7502072812 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 97526946557) ^ 1455626068 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 97526946557) ^ 187191836 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 97526946557) ^ 23597132 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_103554343649 : Nat.Prime 103554343649 := by
  apply lucas_primality 103554343649 (3 : ZMod 103554343649)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 2), (66042311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 2), (66042311, 1)] : List FactorBlock).map factorBlockValue).prod) = 103554343649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_66042311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 103554343649) ^ 51777171824 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 103554343649) ^ 14793477664 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 103554343649) ^ 1568 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_117723937763 : Nat.Prime 117723937763 := by
  apply lucas_primality 117723937763 (2 : ZMod 117723937763)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (138829, 1), (423989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (138829, 1), (423989, 1)] : List FactorBlock).map factorBlockValue).prod) = 117723937763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_138829
      · exact prime_seventyOneBQ_423989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 117723937763) ^ 58861968881 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 117723937763) ^ 847978 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 117723937763) ^ 277658 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_120272690687 : Nat.Prime 120272690687 := by
  apply lucas_primality 120272690687 (5 : ZMod 120272690687)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (3537432079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (3537432079, 1)] : List FactorBlock).map factorBlockValue).prod) = 120272690687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_17
      · exact prime_seventyOneBQ_3537432079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 120272690687) ^ 60136345343 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 120272690687) ^ 7074864158 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 120272690687) ^ 34 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_124958943127 : Nat.Prime 124958943127 := by
  apply lucas_primality 124958943127 (3 : ZMod 124958943127)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (6942163507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (6942163507, 1)] : List FactorBlock).map factorBlockValue).prod) = 124958943127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_6942163507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 124958943127) ^ 62479471563 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 124958943127) ^ 41652981042 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 124958943127) ^ 18 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_156315210739 : Nat.Prime 156315210739 := by
  apply lucas_primality 156315210739 (3 : ZMod 156315210739)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (491, 1), (53060153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (491, 1), (53060153, 1)] : List FactorBlock).map factorBlockValue).prod) = 156315210739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_491
      · exact prime_seventyOneBQ_53060153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 156315210739) ^ 78157605369 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 156315210739) ^ 52105070246 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 156315210739) ^ 318360918 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 156315210739) ^ 2946 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_224317187737 : Nat.Prime 224317187737 := by
  apply lucas_primality 224317187737 (7 : ZMod 224317187737)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1021, 1), (9154309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1021, 1), (9154309, 1)] : List FactorBlock).map factorBlockValue).prod) = 224317187737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_1021
      · exact prime_seventyOneBQ_9154309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 224317187737) ^ 112158593868 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 224317187737) ^ 74772395912 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 224317187737) ^ 219703416 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 224317187737) ^ 24504 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_249774293413 : Nat.Prime 249774293413 := by
  apply lucas_primality 249774293413 (2 : ZMod 249774293413)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (7, 1), (110129759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (7, 1), (110129759, 1)] : List FactorBlock).map factorBlockValue).prod) = 249774293413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_110129759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 249774293413) ^ 124887146706 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 249774293413) ^ 83258097804 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 249774293413) ^ 35682041916 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 249774293413) ^ 2268 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_254937761599 : Nat.Prime 254937761599 := by
  apply lucas_primality 254937761599 (6 : ZMod 254937761599)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (3268432841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (3268432841, 1)] : List FactorBlock).map factorBlockValue).prod) = 254937761599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_13
      · exact prime_seventyOneBQ_3268432841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 254937761599) ^ 127468880799 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 254937761599) ^ 84979253866 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 254937761599) ^ 19610597046 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 254937761599) ^ 78 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_255829465631 : Nat.Prime 255829465631 := by
  apply lucas_primality 255829465631 (11 : ZMod 255829465631)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (25582946563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (25582946563, 1)] : List FactorBlock).map factorBlockValue).prod) = 255829465631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_25582946563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 255829465631) ^ 127914732815 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 255829465631) ^ 51165893126 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 255829465631) ^ 10 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_298530312937 : Nat.Prime 298530312937 := by
  apply lucas_primality 298530312937 (7 : ZMod 298530312937)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (587, 1), (3167, 1), (6691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (587, 1), (3167, 1), (6691, 1)] : List FactorBlock).map factorBlockValue).prod) = 298530312937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_587
      · exact prime_seventyOneBQ_3167
      · exact prime_seventyOneBQ_6691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 298530312937) ^ 149265156468 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 298530312937) ^ 99510104312 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 298530312937) ^ 508569528 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 298530312937) ^ 94262808 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 298530312937) ^ 44616696 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_315617887391 : Nat.Prime 315617887391 := by
  apply lucas_primality 315617887391 (7 : ZMod 315617887391)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (241, 1), (10073983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (241, 1), (10073983, 1)] : List FactorBlock).map factorBlockValue).prod) = 315617887391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_13
      · exact prime_seventyOneBQ_241
      · exact prime_seventyOneBQ_10073983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 315617887391) ^ 157808943695 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 315617887391) ^ 63123577478 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 315617887391) ^ 24278299030 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 315617887391) ^ 1309617790 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 315617887391) ^ 31330 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_351414102947 : Nat.Prime 351414102947 := by
  apply lucas_primality 351414102947 (2 : ZMod 351414102947)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (139, 1), (163, 1), (209597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (139, 1), (163, 1), (209597, 1)] : List FactorBlock).map factorBlockValue).prod) = 351414102947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_37
      · exact prime_seventyOneBQ_139
      · exact prime_seventyOneBQ_163
      · exact prime_seventyOneBQ_209597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 351414102947) ^ 175707051473 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 351414102947) ^ 9497678458 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 351414102947) ^ 2528159014 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 351414102947) ^ 2155914742 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 351414102947) ^ 1676618 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_411798232613 : Nat.Prime 411798232613 := by
  apply lucas_primality 411798232613 (2 : ZMod 411798232613)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (41, 1), (43, 1), (4491887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (41, 1), (43, 1), (4491887, 1)] : List FactorBlock).map factorBlockValue).prod) = 411798232613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_13
      · exact prime_seventyOneBQ_41
      · exact prime_seventyOneBQ_43
      · exact prime_seventyOneBQ_4491887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 411798232613) ^ 205899116306 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 411798232613) ^ 31676787124 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 411798232613) ^ 10043859332 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 411798232613) ^ 9576703084 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 411798232613) ^ 91676 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_457259080997 : Nat.Prime 457259080997 := by
  apply lucas_primality 457259080997 (2 : ZMod 457259080997)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (281, 1), (9721, 1), (41849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (281, 1), (9721, 1), (41849, 1)] : List FactorBlock).map factorBlockValue).prod) = 457259080997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_281
      · exact prime_seventyOneBQ_9721
      · exact prime_seventyOneBQ_41849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 457259080997) ^ 228629540498 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 457259080997) ^ 1627256516 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 457259080997) ^ 47038276 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 457259080997) ^ 10926404 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_476762932937 : Nat.Prime 476762932937 := by
  apply lucas_primality 476762932937 (5 : ZMod 476762932937)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (19, 1), (184505779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (19, 1), (184505779, 1)] : List FactorBlock).map factorBlockValue).prod) = 476762932937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_17
      · exact prime_seventyOneBQ_19
      · exact prime_seventyOneBQ_184505779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 476762932937) ^ 238381466468 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 476762932937) ^ 28044878408 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 476762932937) ^ 25092785944 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 476762932937) ^ 2584 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_511658931263 : Nat.Prime 511658931263 := by
  apply lucas_primality 511658931263 (5 : ZMod 511658931263)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (255829465631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (255829465631, 1)] : List FactorBlock).map factorBlockValue).prod) = 511658931263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_255829465631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 511658931263) ^ 255829465631 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 511658931263) ^ 2 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_525418646041 : Nat.Prime 525418646041 := by
  apply lucas_primality 525418646041 (23 : ZMod 525418646041)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (43, 1), (33941773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (43, 1), (33941773, 1)] : List FactorBlock).map factorBlockValue).prod) = 525418646041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_43
      · exact prime_seventyOneBQ_33941773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 525418646041) ^ 262709323020 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (23 : ZMod 525418646041) ^ 175139548680 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (23 : ZMod 525418646041) ^ 105083729208 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (23 : ZMod 525418646041) ^ 12219038280 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (23 : ZMod 525418646041) ^ 15480 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_585161679343 : Nat.Prime 585161679343 := by
  apply lucas_primality 585161679343 (13 : ZMod 585161679343)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (97526946557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (97526946557, 1)] : List FactorBlock).map factorBlockValue).prod) = 585161679343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_97526946557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 585161679343) ^ 292580839671 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (13 : ZMod 585161679343) ^ 195053893114 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (13 : ZMod 585161679343) ^ 6 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_677091820903 : Nat.Prime 677091820903 := by
  apply lucas_primality 677091820903 (3 : ZMod 677091820903)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (31, 1), (22637, 1), (22973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (31, 1), (22637, 1), (22973, 1)] : List FactorBlock).map factorBlockValue).prod) = 677091820903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_31
      · exact prime_seventyOneBQ_22637
      · exact prime_seventyOneBQ_22973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 677091820903) ^ 338545910451 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 677091820903) ^ 225697273634 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 677091820903) ^ 96727402986 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 677091820903) ^ 21841671642 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 677091820903) ^ 29910846 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 677091820903) ^ 29473374 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_677589608939 : Nat.Prime 677589608939 := by
  apply lucas_primality 677589608939 (2 : ZMod 677589608939)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (37, 1), (832419667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (37, 1), (832419667, 1)] : List FactorBlock).map factorBlockValue).prod) = 677589608939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_11
      · exact prime_seventyOneBQ_37
      · exact prime_seventyOneBQ_832419667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 677589608939) ^ 338794804469 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 677589608939) ^ 61599055358 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 677589608939) ^ 18313232674 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 677589608939) ^ 814 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_823596465227 : Nat.Prime 823596465227 := by
  apply lucas_primality 823596465227 (2 : ZMod 823596465227)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (411798232613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (411798232613, 1)] : List FactorBlock).map factorBlockValue).prod) = 823596465227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_411798232613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 823596465227) ^ 411798232613 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 823596465227) ^ 2 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_850703780621 : Nat.Prime 850703780621 := by
  apply lucas_primality 850703780621 (2 : ZMod 850703780621)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 1), (83, 1), (1091, 1), (27631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 1), (83, 1), (1091, 1), (27631, 1)] : List FactorBlock).map factorBlockValue).prod) = 850703780621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_17
      · exact prime_seventyOneBQ_83
      · exact prime_seventyOneBQ_1091
      · exact prime_seventyOneBQ_27631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 850703780621) ^ 425351890310 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 850703780621) ^ 170140756124 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 850703780621) ^ 50041398860 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 850703780621) ^ 10249443140 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 850703780621) ^ 779746820 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 850703780621) ^ 30788020 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_917938975013 : Nat.Prime 917938975013 := by
  apply lucas_primality 917938975013 (2 : ZMod 917938975013)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1889, 1), (121484777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1889, 1), (121484777, 1)] : List FactorBlock).map factorBlockValue).prod) = 917938975013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_1889
      · exact prime_seventyOneBQ_121484777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 917938975013) ^ 458969487506 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 917938975013) ^ 485939108 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 917938975013) ^ 7556 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_1009930578949 : Nat.Prime 1009930578949 := by
  apply lucas_primality 1009930578949 (7 : ZMod 1009930578949)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (4261, 1), (6583813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (4261, 1), (6583813, 1)] : List FactorBlock).map factorBlockValue).prod) = 1009930578949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_4261
      · exact prime_seventyOneBQ_6583813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1009930578949) ^ 504965289474 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 1009930578949) ^ 336643526316 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 1009930578949) ^ 237017268 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 1009930578949) ^ 153396 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_1023317862527 : Nat.Prime 1023317862527 := by
  apply lucas_primality 1023317862527 (5 : ZMod 1023317862527)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (511658931263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (511658931263, 1)] : List FactorBlock).map factorBlockValue).prod) = 1023317862527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_511658931263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1023317862527) ^ 511658931263 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1023317862527) ^ 2 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_1063678973353 : Nat.Prime 1063678973353 := by
  apply lucas_primality 1063678973353 (7 : ZMod 1063678973353)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (29, 1), (1528274387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (29, 1), (1528274387, 1)] : List FactorBlock).map factorBlockValue).prod) = 1063678973353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_29
      · exact prime_seventyOneBQ_1528274387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1063678973353) ^ 531839486676 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 1063678973353) ^ 354559657784 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 1063678973353) ^ 36678585288 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 1063678973353) ^ 696 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_1141216558721 : Nat.Prime 1141216558721 := by
  apply lucas_primality 1141216558721 (3 : ZMod 1141216558721)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 1), (7, 1), (254735839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 1), (7, 1), (254735839, 1)] : List FactorBlock).map factorBlockValue).prod) = 1141216558721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_254735839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1141216558721) ^ 570608279360 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1141216558721) ^ 228243311744 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1141216558721) ^ 163030936960 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1141216558721) ^ 4480 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_1230510825251 : Nat.Prime 1230510825251 := by
  apply lucas_primality 1230510825251 (2 : ZMod 1230510825251)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (7, 1), (703149043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (7, 1), (703149043, 1)] : List FactorBlock).map factorBlockValue).prod) = 1230510825251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_703149043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1230510825251) ^ 615255412625 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1230510825251) ^ 246102165050 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1230510825251) ^ 175787260750 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1230510825251) ^ 1750 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_2673963025177 : Nat.Prime 2673963025177 := by
  apply lucas_primality 2673963025177 (10 : ZMod 2673963025177)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (43, 1), (2591049443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (43, 1), (2591049443, 1)] : List FactorBlock).map factorBlockValue).prod) = 2673963025177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_43
      · exact prime_seventyOneBQ_2591049443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2673963025177) ^ 1336981512588 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (10 : ZMod 2673963025177) ^ 891321008392 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (10 : ZMod 2673963025177) ^ 62185186632 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (10 : ZMod 2673963025177) ^ 1032 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_3043375833073 : Nat.Prime 3043375833073 := by
  apply lucas_primality 3043375833073 (5 : ZMod 3043375833073)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (1231, 1), (5839, 1), (8821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (1231, 1), (5839, 1), (8821, 1)] : List FactorBlock).map factorBlockValue).prod) = 3043375833073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_1231
      · exact prime_seventyOneBQ_5839
      · exact prime_seventyOneBQ_8821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3043375833073) ^ 1521687916536 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 3043375833073) ^ 1014458611024 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 3043375833073) ^ 2472279312 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 3043375833073) ^ 521215248 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 3043375833073) ^ 345014832 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_3132197541149 : Nat.Prime 3132197541149 := by
  apply lucas_primality 3132197541149 (2 : ZMod 3132197541149)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (60234568099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (60234568099, 1)] : List FactorBlock).map factorBlockValue).prod) = 3132197541149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_13
      · exact prime_seventyOneBQ_60234568099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3132197541149) ^ 1566098770574 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3132197541149) ^ 240938272396 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3132197541149) ^ 52 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_3363684589501 : Nat.Prime 3363684589501 := by
  apply lucas_primality 3363684589501 (7 : ZMod 3363684589501)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 3), (31, 1), (4139, 1), (17477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 3), (31, 1), (4139, 1), (17477, 1)] : List FactorBlock).map factorBlockValue).prod) = 3363684589501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_31
      · exact prime_seventyOneBQ_4139
      · exact prime_seventyOneBQ_17477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3363684589501) ^ 1681842294750 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 3363684589501) ^ 1121228196500 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 3363684589501) ^ 672736917900 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 3363684589501) ^ 108505954500 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 3363684589501) ^ 812680500 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 3363684589501) ^ 192463500 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_3544481901619 : Nat.Prime 3544481901619 := by
  apply lucas_primality 3544481901619 (3 : ZMod 3544481901619)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (23, 1), (1223078641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (23, 1), (1223078641, 1)] : List FactorBlock).map factorBlockValue).prod) = 3544481901619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_23
      · exact prime_seventyOneBQ_1223078641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3544481901619) ^ 1772240950809 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 3544481901619) ^ 1181493967206 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 3544481901619) ^ 506354557374 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 3544481901619) ^ 154107908766 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 3544481901619) ^ 2898 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_3904618679737 : Nat.Prime 3904618679737 := by
  apply lucas_primality 3904618679737 (5 : ZMod 3904618679737)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (310697, 1), (523637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (310697, 1), (523637, 1)] : List FactorBlock).map factorBlockValue).prod) = 3904618679737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_310697
      · exact prime_seventyOneBQ_523637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3904618679737) ^ 1952309339868 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 3904618679737) ^ 1301539559912 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 3904618679737) ^ 12567288 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 3904618679737) ^ 7456728 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_4126104661669 : Nat.Prime 4126104661669 := by
  apply lucas_primality 4126104661669 (2 : ZMod 4126104661669)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (29, 1), (127, 1), (673, 1), (12611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (29, 1), (127, 1), (673, 1), (12611, 1)] : List FactorBlock).map factorBlockValue).prod) = 4126104661669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_11
      · exact prime_seventyOneBQ_29
      · exact prime_seventyOneBQ_127
      · exact prime_seventyOneBQ_673
      · exact prime_seventyOneBQ_12611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4126104661669) ^ 2063052330834 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4126104661669) ^ 1375368220556 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4126104661669) ^ 375100423788 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4126104661669) ^ 142279471092 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4126104661669) ^ 32489013084 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4126104661669) ^ 6130913316 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4126104661669) ^ 327182988 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_4776745615207 : Nat.Prime 4776745615207 := by
  apply lucas_primality 4776745615207 (5 : ZMod 4776745615207)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3779, 1), (210670619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3779, 1), (210670619, 1)] : List FactorBlock).map factorBlockValue).prod) = 4776745615207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_3779
      · exact prime_seventyOneBQ_210670619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4776745615207) ^ 2388372807603 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 4776745615207) ^ 1592248538402 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 4776745615207) ^ 1264023714 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 4776745615207) ^ 22674 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_4906163807641 : Nat.Prime 4906163807641 := by
  apply lucas_primality 4906163807641 (11 : ZMod 4906163807641)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (2819, 1), (4834421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (2819, 1), (4834421, 1)] : List FactorBlock).map factorBlockValue).prod) = 4906163807641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_2819
      · exact prime_seventyOneBQ_4834421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 4906163807641) ^ 2453081903820 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 4906163807641) ^ 1635387935880 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 4906163807641) ^ 981232761528 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 4906163807641) ^ 1740391560 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 4906163807641) ^ 1014840 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_6177998917997 : Nat.Prime 6177998917997 := by
  apply lucas_primality 6177998917997 (2 : ZMod 6177998917997)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2719, 1), (568039621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2719, 1), (568039621, 1)] : List FactorBlock).map factorBlockValue).prod) = 6177998917997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_2719
      · exact prime_seventyOneBQ_568039621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6177998917997) ^ 3088999458998 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6177998917997) ^ 2272158484 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6177998917997) ^ 10876 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_6478508525131 : Nat.Prime 6478508525131 := by
  apply lucas_primality 6478508525131 (2 : ZMod 6478508525131)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 7), (5, 1), (296228099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 7), (5, 1), (296228099, 1)] : List FactorBlock).map factorBlockValue).prod) = 6478508525131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_296228099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6478508525131) ^ 3239254262565 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6478508525131) ^ 2159502841710 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6478508525131) ^ 1295701705026 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6478508525131) ^ 21870 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_6674681061119 : Nat.Prime 6674681061119 := by
  apply lucas_primality 6674681061119 (7 : ZMod 6674681061119)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (476762932937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (476762932937, 1)] : List FactorBlock).map factorBlockValue).prod) = 6674681061119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_476762932937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 6674681061119) ^ 3337340530559 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 6674681061119) ^ 953525865874 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 6674681061119) ^ 14 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_7855099162567 : Nat.Prime 7855099162567 := by
  apply lucas_primality 7855099162567 (3 : ZMod 7855099162567)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (191, 1), (360755909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (191, 1), (360755909, 1)] : List FactorBlock).map factorBlockValue).prod) = 7855099162567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_19
      · exact prime_seventyOneBQ_191
      · exact prime_seventyOneBQ_360755909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7855099162567) ^ 3927549581283 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 7855099162567) ^ 2618366387522 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 7855099162567) ^ 413426271714 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 7855099162567) ^ 41126173626 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 7855099162567) ^ 21774 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_11120147934089 : Nat.Prime 11120147934089 := by
  apply lucas_primality 11120147934089 (3 : ZMod 11120147934089)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (859, 1), (95187187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (859, 1), (95187187, 1)] : List FactorBlock).map factorBlockValue).prod) = 11120147934089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_17
      · exact prime_seventyOneBQ_859
      · exact prime_seventyOneBQ_95187187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 11120147934089) ^ 5560073967044 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 11120147934089) ^ 654126349064 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 11120147934089) ^ 12945457432 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 11120147934089) ^ 116824 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_11847363073849 : Nat.Prime 11847363073849 := by
  apply lucas_primality 11847363073849 (11 : ZMod 11847363073849)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (89, 1), (383, 1), (4827257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (89, 1), (383, 1), (4827257, 1)] : List FactorBlock).map factorBlockValue).prod) = 11847363073849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_89
      · exact prime_seventyOneBQ_383
      · exact prime_seventyOneBQ_4827257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 11847363073849) ^ 5923681536924 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 11847363073849) ^ 3949121024616 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 11847363073849) ^ 133116439032 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 11847363073849) ^ 30933062856 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 11847363073849) ^ 2454264 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_12173503332293 : Nat.Prime 12173503332293 := by
  apply lucas_primality 12173503332293 (2 : ZMod 12173503332293)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3043375833073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3043375833073, 1)] : List FactorBlock).map factorBlockValue).prod) = 12173503332293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3043375833073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 12173503332293) ^ 6086751666146 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 12173503332293) ^ 4 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_14292003754163 : Nat.Prime 14292003754163 := by
  apply lucas_primality 14292003754163 (2 : ZMod 14292003754163)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (1091, 1), (385291523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (1091, 1), (385291523, 1)] : List FactorBlock).map factorBlockValue).prod) = 14292003754163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_17
      · exact prime_seventyOneBQ_1091
      · exact prime_seventyOneBQ_385291523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14292003754163) ^ 7146001877081 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 14292003754163) ^ 840706103186 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 14292003754163) ^ 13099911782 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 14292003754163) ^ 37094 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_17860637100941 : Nat.Prime 17860637100941 := by
  apply lucas_primality 17860637100941 (3 : ZMod 17860637100941)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 2), (3090075623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 2), (3090075623, 1)] : List FactorBlock).map factorBlockValue).prod) = 17860637100941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_17
      · exact prime_seventyOneBQ_3090075623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 17860637100941) ^ 8930318550470 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 17860637100941) ^ 3572127420188 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 17860637100941) ^ 1050625711820 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 17860637100941) ^ 5780 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_18751562110751 : Nat.Prime 18751562110751 := by
  apply lucas_primality 18751562110751 (13 : ZMod 18751562110751)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (7, 1), (263, 1), (40742123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (7, 1), (263, 1), (40742123, 1)] : List FactorBlock).map factorBlockValue).prod) = 18751562110751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_263
      · exact prime_seventyOneBQ_40742123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 18751562110751) ^ 9375781055375 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (13 : ZMod 18751562110751) ^ 3750312422150 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (13 : ZMod 18751562110751) ^ 2678794587250 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (13 : ZMod 18751562110751) ^ 71298715250 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (13 : ZMod 18751562110751) ^ 460250 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_24211082802947 : Nat.Prime 24211082802947 := by
  apply lucas_primality 24211082802947 (2 : ZMod 24211082802947)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (41, 1), (22712085181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (41, 1), (22712085181, 1)] : List FactorBlock).map factorBlockValue).prod) = 24211082802947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_13
      · exact prime_seventyOneBQ_41
      · exact prime_seventyOneBQ_22712085181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 24211082802947) ^ 12105541401473 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 24211082802947) ^ 1862390984842 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 24211082802947) ^ 590514214706 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 24211082802947) ^ 1066 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_29723410584709 : Nat.Prime 29723410584709 := by
  apply lucas_primality 29723410584709 (10 : ZMod 29723410584709)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (47, 1), (53, 1), (101, 1), (1381, 1), (7129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (47, 1), (53, 1), (101, 1), (1381, 1), (7129, 1)] : List FactorBlock).map factorBlockValue).prod) = 29723410584709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_47
      · exact prime_seventyOneBQ_53
      · exact prime_seventyOneBQ_101
      · exact prime_seventyOneBQ_1381
      · exact prime_seventyOneBQ_7129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 29723410584709) ^ 14861705292354 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (10 : ZMod 29723410584709) ^ 9907803528236 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (10 : ZMod 29723410584709) ^ 632412991164 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (10 : ZMod 29723410584709) ^ 560819067636 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (10 : ZMod 29723410584709) ^ 294291193908 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (10 : ZMod 29723410584709) ^ 21523106868 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (10 : ZMod 29723410584709) ^ 4169366052 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_43390828113001 : Nat.Prime 43390828113001 := by
  apply lucas_primality 43390828113001 (11 : ZMod 43390828113001)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 3), (27239, 1), (530989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 3), (27239, 1), (530989, 1)] : List FactorBlock).map factorBlockValue).prod) = 43390828113001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_27239
      · exact prime_seventyOneBQ_530989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 43390828113001) ^ 21695414056500 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 43390828113001) ^ 14463609371000 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 43390828113001) ^ 8678165622600 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 43390828113001) ^ 1592967000 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 43390828113001) ^ 81717000 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_74441223091321 : Nat.Prime 74441223091321 := by
  apply lucas_primality 74441223091321 (13 : ZMod 74441223091321)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (17, 1), (797, 1), (1993, 1), (22973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (17, 1), (797, 1), (1993, 1), (22973, 1)] : List FactorBlock).map factorBlockValue).prod) = 74441223091321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_17
      · exact prime_seventyOneBQ_797
      · exact prime_seventyOneBQ_1993
      · exact prime_seventyOneBQ_22973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 74441223091321) ^ 37220611545660 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (13 : ZMod 74441223091321) ^ 24813741030440 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (13 : ZMod 74441223091321) ^ 14888244618264 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (13 : ZMod 74441223091321) ^ 4378895475960 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (13 : ZMod 74441223091321) ^ 93401785560 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (13 : ZMod 74441223091321) ^ 37351341240 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (13 : ZMod 74441223091321) ^ 3240378840 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_78664400127073 : Nat.Prime 78664400127073 := by
  apply lucas_primality 78664400127073 (5 : ZMod 78664400127073)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (59, 1), (61, 1), (75893381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (59, 1), (61, 1), (75893381, 1)] : List FactorBlock).map factorBlockValue).prod) = 78664400127073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_59
      · exact prime_seventyOneBQ_61
      · exact prime_seventyOneBQ_75893381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 78664400127073) ^ 39332200063536 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 78664400127073) ^ 26221466709024 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 78664400127073) ^ 1333294917408 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 78664400127073) ^ 1289580329952 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 78664400127073) ^ 1036512 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_93625868694881 : Nat.Prime 93625868694881 := by
  apply lucas_primality 93625868694881 (3 : ZMod 93625868694881)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (585161679343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (585161679343, 1)] : List FactorBlock).map factorBlockValue).prod) = 93625868694881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_585161679343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 93625868694881) ^ 46812934347440 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 93625868694881) ^ 18725173738976 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 93625868694881) ^ 160 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_103406557472983 : Nat.Prime 103406557472983 := by
  apply lucas_primality 103406557472983 (3 : ZMod 103406557472983)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (23, 1), (249774293413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (23, 1), (249774293413, 1)] : List FactorBlock).map factorBlockValue).prod) = 103406557472983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_23
      · exact prime_seventyOneBQ_249774293413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 103406557472983) ^ 51703278736491 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 103406557472983) ^ 34468852490994 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 103406557472983) ^ 4495937281434 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 103406557472983) ^ 414 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_140287558496747 : Nat.Prime 140287558496747 := by
  apply lucas_primality 140287558496747 (2 : ZMod 140287558496747)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (4126104661669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (4126104661669, 1)] : List FactorBlock).map factorBlockValue).prod) = 140287558496747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_17
      · exact prime_seventyOneBQ_4126104661669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 140287558496747) ^ 70143779248373 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 140287558496747) ^ 8252209323338 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 140287558496747) ^ 34 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_149587300667947 : Nat.Prime 149587300667947 := by
  apply lucas_primality 149587300667947 (3 : ZMod 149587300667947)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (263, 1), (4733, 1), (20028629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (263, 1), (4733, 1), (20028629, 1)] : List FactorBlock).map factorBlockValue).prod) = 149587300667947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_263
      · exact prime_seventyOneBQ_4733
      · exact prime_seventyOneBQ_20028629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 149587300667947) ^ 74793650333973 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 149587300667947) ^ 49862433555982 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 149587300667947) ^ 568773006342 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 149587300667947) ^ 31605176562 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 149587300667947) ^ 7468674 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_177805880404721 : Nat.Prime 177805880404721 := by
  apply lucas_primality 177805880404721 (3 : ZMod 177805880404721)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (56857, 1), (39090587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (56857, 1), (39090587, 1)] : List FactorBlock).map factorBlockValue).prod) = 177805880404721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_56857
      · exact prime_seventyOneBQ_39090587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 177805880404721) ^ 88902940202360 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 177805880404721) ^ 35561176080944 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 177805880404721) ^ 3127246960 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 177805880404721) ^ 4548560 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_300369646712659 : Nat.Prime 300369646712659 := by
  apply lucas_primality 300369646712659 (2 : ZMod 300369646712659)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (997, 1), (50212244519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (997, 1), (50212244519, 1)] : List FactorBlock).map factorBlockValue).prod) = 300369646712659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_997
      · exact prime_seventyOneBQ_50212244519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 300369646712659) ^ 150184823356329 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 300369646712659) ^ 100123215570886 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 300369646712659) ^ 301273467114 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 300369646712659) ^ 5982 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_362222958707399 : Nat.Prime 362222958707399 := by
  apply lucas_primality 362222958707399 (11 : ZMod 362222958707399)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (2066681, 1), (3810173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (2066681, 1), (3810173, 1)] : List FactorBlock).map factorBlockValue).prod) = 362222958707399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_23
      · exact prime_seventyOneBQ_2066681
      · exact prime_seventyOneBQ_3810173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 362222958707399) ^ 181111479353699 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 362222958707399) ^ 15748824291626 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 362222958707399) ^ 175267958 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 362222958707399) ^ 95067326 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_413626229891933 : Nat.Prime 413626229891933 := by
  apply lucas_primality 413626229891933 (2 : ZMod 413626229891933)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (103406557472983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (103406557472983, 1)] : List FactorBlock).map factorBlockValue).prod) = 413626229891933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_103406557472983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 413626229891933) ^ 206813114945966 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 413626229891933) ^ 4 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_511150160025733 : Nat.Prime 511150160025733 := by
  apply lucas_primality 511150160025733 (2 : ZMod 511150160025733)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (277, 1), (303917, 1), (505979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (277, 1), (303917, 1), (505979, 1)] : List FactorBlock).map factorBlockValue).prod) = 511150160025733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_277
      · exact prime_seventyOneBQ_303917
      · exact prime_seventyOneBQ_505979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 511150160025733) ^ 255575080012866 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 511150160025733) ^ 170383386675244 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 511150160025733) ^ 1845307436916 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 511150160025733) ^ 1681874196 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 511150160025733) ^ 1010220108 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_577613391959767 : Nat.Prime 577613391959767 := by
  apply lucas_primality 577613391959767 (5 : ZMod 577613391959767)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (419, 1), (3719, 1), (61779701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (419, 1), (3719, 1), (61779701, 1)] : List FactorBlock).map factorBlockValue).prod) = 577613391959767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_419
      · exact prime_seventyOneBQ_3719
      · exact prime_seventyOneBQ_61779701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 577613391959767) ^ 288806695979883 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 577613391959767) ^ 192537797319922 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 577613391959767) ^ 1378552248114 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 577613391959767) ^ 155314168314 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 577613391959767) ^ 9349566 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_586265210059741 : Nat.Prime 586265210059741 := by
  apply lucas_primality 586265210059741 (2 : ZMod 586265210059741)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (83, 1), (117723937763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (83, 1), (117723937763, 1)] : List FactorBlock).map factorBlockValue).prod) = 586265210059741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_83
      · exact prime_seventyOneBQ_117723937763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 586265210059741) ^ 293132605029870 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 586265210059741) ^ 195421736686580 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 586265210059741) ^ 117253042011948 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 586265210059741) ^ 7063436265780 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 586265210059741) ^ 4980 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_739044349401377 : Nat.Prime 739044349401377 := by
  apply lucas_primality 739044349401377 (3 : ZMod 739044349401377)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (359, 1), (64331854927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (359, 1), (64331854927, 1)] : List FactorBlock).map factorBlockValue).prod) = 739044349401377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_359
      · exact prime_seventyOneBQ_64331854927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 739044349401377) ^ 369522174700688 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 739044349401377) ^ 2058619357664 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 739044349401377) ^ 11488 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_750146758239523 : Nat.Prime 750146758239523 := by
  apply lucas_primality 750146758239523 (5 : ZMod 750146758239523)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (17860637100941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (17860637100941, 1)] : List FactorBlock).map factorBlockValue).prod) = 750146758239523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_17860637100941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 750146758239523) ^ 375073379119761 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 750146758239523) ^ 250048919413174 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 750146758239523) ^ 107163822605646 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 750146758239523) ^ 42 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_1407896083251313 : Nat.Prime 1407896083251313 := by
  apply lucas_primality 1407896083251313 (5 : ZMod 1407896083251313)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (1493, 1), (19645792633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (1493, 1), (19645792633, 1)] : List FactorBlock).map factorBlockValue).prod) = 1407896083251313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_1493
      · exact prime_seventyOneBQ_19645792633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1407896083251313) ^ 703948041625656 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1407896083251313) ^ 469298694417104 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1407896083251313) ^ 942998046384 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1407896083251313) ^ 71664 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_1630022292952337 : Nat.Prime 1630022292952337 := by
  apply lucas_primality 1630022292952337 (3 : ZMod 1630022292952337)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (2069, 1), (36809, 1), (1337701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (2069, 1), (36809, 1), (1337701, 1)] : List FactorBlock).map factorBlockValue).prod) = 1630022292952337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_2069
      · exact prime_seventyOneBQ_36809
      · exact prime_seventyOneBQ_1337701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1630022292952337) ^ 815011146476168 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1630022292952337) ^ 787830977744 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1630022292952337) ^ 44283253904 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1630022292952337) ^ 1218525136 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_1899066519837709 : Nat.Prime 1899066519837709 := by
  apply lucas_primality 1899066519837709 (2 : ZMod 1899066519837709)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (12173503332293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (12173503332293, 1)] : List FactorBlock).map factorBlockValue).prod) = 1899066519837709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_13
      · exact prime_seventyOneBQ_12173503332293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1899066519837709) ^ 949533259918854 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1899066519837709) ^ 633022173279236 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1899066519837709) ^ 146082039987516 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1899066519837709) ^ 156 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_1957747848921247 : Nat.Prime 1957747848921247 := by
  apply lucas_primality 1957747848921247 (3 : ZMod 1957747848921247)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (139, 1), (383, 1), (971, 1), (371299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (139, 1), (383, 1), (971, 1), (371299, 1)] : List FactorBlock).map factorBlockValue).prod) = 1957747848921247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_17
      · exact prime_seventyOneBQ_139
      · exact prime_seventyOneBQ_383
      · exact prime_seventyOneBQ_971
      · exact prime_seventyOneBQ_371299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1957747848921247) ^ 978873924460623 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1957747848921247) ^ 652582616307082 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1957747848921247) ^ 115161638171838 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1957747848921247) ^ 14084516898714 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1957747848921247) ^ 5111613182562 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1957747848921247) ^ 2016218176026 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1957747848921247) ^ 5272698954 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_2315690028196529 : Nat.Prime 2315690028196529 := by
  apply lucas_primality 2315690028196529 (3 : ZMod 2315690028196529)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (249671, 1), (579685373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (249671, 1), (579685373, 1)] : List FactorBlock).map factorBlockValue).prod) = 2315690028196529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_249671
      · exact prime_seventyOneBQ_579685373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2315690028196529) ^ 1157845014098264 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2315690028196529) ^ 9274965968 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2315690028196529) ^ 3994736 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_2874517307419301 : Nat.Prime 2874517307419301 := by
  apply lucas_primality 2874517307419301 (2 : ZMod 2874517307419301)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (239, 1), (120272690687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (239, 1), (120272690687, 1)] : List FactorBlock).map factorBlockValue).prod) = 2874517307419301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_239
      · exact prime_seventyOneBQ_120272690687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2874517307419301) ^ 1437258653709650 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2874517307419301) ^ 574903461483860 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2874517307419301) ^ 12027269068700 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2874517307419301) ^ 23900 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_3401618891086831 : Nat.Prime 3401618891086831 := by
  apply lucas_primality 3401618891086831 (6 : ZMod 3401618891086831)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (263, 1), (59273, 1), (7273639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (263, 1), (59273, 1), (7273639, 1)] : List FactorBlock).map factorBlockValue).prod) = 3401618891086831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_263
      · exact prime_seventyOneBQ_59273
      · exact prime_seventyOneBQ_7273639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3401618891086831) ^ 1700809445543415 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 3401618891086831) ^ 1133872963695610 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 3401618891086831) ^ 680323778217366 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 3401618891086831) ^ 12933912133410 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 3401618891086831) ^ 57389011710 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 3401618891086831) ^ 467663970 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_3686766071755237 : Nat.Prime 3686766071755237 := by
  apply lucas_primality 3686766071755237 (5 : ZMod 3686766071755237)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (31, 2), (11024095087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (31, 2), (11024095087, 1)] : List FactorBlock).map factorBlockValue).prod) = 3686766071755237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_29
      · exact prime_seventyOneBQ_31
      · exact prime_seventyOneBQ_11024095087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3686766071755237) ^ 1843383035877618 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 3686766071755237) ^ 1228922023918412 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 3686766071755237) ^ 127129864543284 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 3686766071755237) ^ 118927937798556 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 3686766071755237) ^ 334428 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_3758121476653007 : Nat.Prime 3758121476653007 := by
  apply lucas_primality 3758121476653007 (5 : ZMod 3758121476653007)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (383, 1), (4906163807641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (383, 1), (4906163807641, 1)] : List FactorBlock).map factorBlockValue).prod) = 3758121476653007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_383
      · exact prime_seventyOneBQ_4906163807641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3758121476653007) ^ 1879060738326503 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 3758121476653007) ^ 9812327615282 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 3758121476653007) ^ 766 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_4745029933313407 : Nat.Prime 4745029933313407 := by
  apply lucas_primality 4745029933313407 (3 : ZMod 4745029933313407)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (298303, 1), (26779033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (298303, 1), (26779033, 1)] : List FactorBlock).map factorBlockValue).prod) = 4745029933313407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_11
      · exact prime_seventyOneBQ_298303
      · exact prime_seventyOneBQ_26779033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4745029933313407) ^ 2372514966656703 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 4745029933313407) ^ 1581676644437802 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 4745029933313407) ^ 431366357573946 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 4745029933313407) ^ 15906745602 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 4745029933313407) ^ 177191982 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_5055642003216709 : Nat.Prime 5055642003216709 := by
  apply lucas_primality 5055642003216709 (2 : ZMod 5055642003216709)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (19, 1), (60793, 1), (121581259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (19, 1), (60793, 1), (121581259, 1)] : List FactorBlock).map factorBlockValue).prod) = 5055642003216709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_19
      · exact prime_seventyOneBQ_60793
      · exact prime_seventyOneBQ_121581259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5055642003216709) ^ 2527821001608354 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5055642003216709) ^ 1685214001072236 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5055642003216709) ^ 266086421221932 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5055642003216709) ^ 83161581156 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5055642003216709) ^ 41582412 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_7035182520716893 : Nat.Prime 7035182520716893 := by
  apply lucas_primality 7035182520716893 (2 : ZMod 7035182520716893)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (586265210059741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (586265210059741, 1)] : List FactorBlock).map factorBlockValue).prod) = 7035182520716893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_586265210059741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7035182520716893) ^ 3517591260358446 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 7035182520716893) ^ 2345060840238964 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 7035182520716893) ^ 12 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_7559992800768341 : Nat.Prime 7559992800768341 := by
  apply lucas_primality 7559992800768341 (2 : ZMod 7559992800768341)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (43, 1), (86291, 1), (101872609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (43, 1), (86291, 1), (101872609, 1)] : List FactorBlock).map factorBlockValue).prod) = 7559992800768341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_43
      · exact prime_seventyOneBQ_86291
      · exact prime_seventyOneBQ_101872609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7559992800768341) ^ 3779996400384170 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 7559992800768341) ^ 1511998560153668 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 7559992800768341) ^ 175813786064380 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 7559992800768341) ^ 87610443740 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 7559992800768341) ^ 74210260 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_8693351008977577 : Nat.Prime 8693351008977577 := by
  apply lucas_primality 8693351008977577 (7 : ZMod 8693351008977577)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (362222958707399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (362222958707399, 1)] : List FactorBlock).map factorBlockValue).prod) = 8693351008977577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_362222958707399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 8693351008977577) ^ 4346675504488788 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 8693351008977577) ^ 2897783669659192 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 8693351008977577) ^ 24 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_12533332074459611 : Nat.Prime 12533332074459611 := by
  apply lucas_primality 12533332074459611 (2 : ZMod 12533332074459611)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (42703, 1), (29350003687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (42703, 1), (29350003687, 1)] : List FactorBlock).map factorBlockValue).prod) = 12533332074459611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_42703
      · exact prime_seventyOneBQ_29350003687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 12533332074459611) ^ 6266666037229805 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 12533332074459611) ^ 2506666414891922 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 12533332074459611) ^ 293500036870 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 12533332074459611) ^ 427030 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_13915202250538163 : Nat.Prime 13915202250538163 := by
  apply lucas_primality 13915202250538163 (2 : ZMod 13915202250538163)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (17, 1), (19, 1), (201329, 1), (2183507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (17, 1), (19, 1), (201329, 1), (2183507, 1)] : List FactorBlock).map factorBlockValue).prod) = 13915202250538163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_17
      · exact prime_seventyOneBQ_19
      · exact prime_seventyOneBQ_201329
      · exact prime_seventyOneBQ_2183507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13915202250538163) ^ 6957601125269081 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 13915202250538163) ^ 1987886035791166 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 13915202250538163) ^ 818541308855186 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 13915202250538163) ^ 732379065817798 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 13915202250538163) ^ 69116730578 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 13915202250538163) ^ 6372868166 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_20222568012866837 : Nat.Prime 20222568012866837 := by
  apply lucas_primality 20222568012866837 (2 : ZMod 20222568012866837)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5055642003216709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5055642003216709, 1)] : List FactorBlock).map factorBlockValue).prod) = 20222568012866837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5055642003216709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 20222568012866837) ^ 10111284006433418 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 20222568012866837) ^ 4 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_22996138459354409 : Nat.Prime 22996138459354409 := by
  apply lucas_primality 22996138459354409 (3 : ZMod 22996138459354409)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (2874517307419301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (2874517307419301, 1)] : List FactorBlock).map factorBlockValue).prod) = 22996138459354409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_2874517307419301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 22996138459354409) ^ 11498069229677204 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 22996138459354409) ^ 8 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_23076151048527713 : Nat.Prime 23076151048527713 := by
  apply lucas_primality 23076151048527713 (3 : ZMod 23076151048527713)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (21017, 1), (72493, 1), (473311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (21017, 1), (72493, 1), (473311, 1)] : List FactorBlock).map factorBlockValue).prod) = 23076151048527713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_21017
      · exact prime_seventyOneBQ_72493
      · exact prime_seventyOneBQ_473311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 23076151048527713) ^ 11538075524263856 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 23076151048527713) ^ 1097975498336 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 23076151048527713) ^ 318322473184 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 23076151048527713) ^ 48754732192 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_37219919344101931 : Nat.Prime 37219919344101931 := by
  apply lucas_primality 37219919344101931 (3 : ZMod 37219919344101931)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (263, 1), (547, 1), (507296863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (263, 1), (547, 1), (507296863, 1)] : List FactorBlock).map factorBlockValue).prod) = 37219919344101931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_17
      · exact prime_seventyOneBQ_263
      · exact prime_seventyOneBQ_547
      · exact prime_seventyOneBQ_507296863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 37219919344101931) ^ 18609959672050965 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 37219919344101931) ^ 12406639781367310 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 37219919344101931) ^ 7443983868820386 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 37219919344101931) ^ 2189407020241290 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 37219919344101931) ^ 141520605871110 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 37219919344101931) ^ 68043728234190 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 37219919344101931) ^ 73369110 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_42189875448977167 : Nat.Prime 42189875448977167 := by
  apply lucas_primality 42189875448977167 (3 : ZMod 42189875448977167)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (413626229891933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (413626229891933, 1)] : List FactorBlock).map factorBlockValue).prod) = 42189875448977167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_17
      · exact prime_seventyOneBQ_413626229891933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 42189875448977167) ^ 21094937724488583 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 42189875448977167) ^ 14063291816325722 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 42189875448977167) ^ 2481757379351598 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 42189875448977167) ^ 102 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_49781343392296391 : Nat.Prime 49781343392296391 := by
  apply lucas_primality 49781343392296391 (7 : ZMod 49781343392296391)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (895553, 1), (794103809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (895553, 1), (794103809, 1)] : List FactorBlock).map factorBlockValue).prod) = 49781343392296391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_895553
      · exact prime_seventyOneBQ_794103809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 49781343392296391) ^ 24890671696148195 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 49781343392296391) ^ 9956268678459278 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 49781343392296391) ^ 7111620484613770 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 49781343392296391) ^ 55587266630 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 49781343392296391) ^ 62688710 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_67368584044417391 : Nat.Prime 67368584044417391 := by
  apply lucas_primality 67368584044417391 (7 : ZMod 67368584044417391)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (53, 1), (149, 1), (569, 1), (214182989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (53, 1), (149, 1), (569, 1), (214182989, 1)] : List FactorBlock).map factorBlockValue).prod) = 67368584044417391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_53
      · exact prime_seventyOneBQ_149
      · exact prime_seventyOneBQ_569
      · exact prime_seventyOneBQ_214182989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 67368584044417391) ^ 33684292022208695 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 67368584044417391) ^ 13473716808883478 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 67368584044417391) ^ 9624083434916770 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 67368584044417391) ^ 1271105359328630 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 67368584044417391) ^ 452138147949110 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 67368584044417391) ^ 118398214489310 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 67368584044417391) ^ 314537510 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_81656179461256429 : Nat.Prime 81656179461256429 := by
  apply lucas_primality 81656179461256429 (2 : ZMod 81656179461256429)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (353, 1), (917938975013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (353, 1), (917938975013, 1)] : List FactorBlock).map factorBlockValue).prod) = 81656179461256429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_353
      · exact prime_seventyOneBQ_917938975013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 81656179461256429) ^ 40828089730628214 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 81656179461256429) ^ 27218726487085476 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 81656179461256429) ^ 11665168494465204 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 81656179461256429) ^ 231320621703276 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 81656179461256429) ^ 88956 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_88418684350987889 : Nat.Prime 88418684350987889 := by
  apply lucas_primality 88418684350987889 (3 : ZMod 88418684350987889)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (853, 1), (6478508525131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (853, 1), (6478508525131, 1)] : List FactorBlock).map factorBlockValue).prod) = 88418684350987889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_853
      · exact prime_seventyOneBQ_6478508525131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 88418684350987889) ^ 44209342175493944 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 88418684350987889) ^ 103656136402096 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 88418684350987889) ^ 13648 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_124642668952483307 : Nat.Prime 124642668952483307 := by
  apply lucas_primality 124642668952483307 (2 : ZMod 124642668952483307)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (101, 1), (197, 1), (3132197541149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (101, 1), (197, 1), (3132197541149, 1)] : List FactorBlock).map factorBlockValue).prod) = 124642668952483307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_101
      · exact prime_seventyOneBQ_197
      · exact prime_seventyOneBQ_3132197541149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 124642668952483307) ^ 62321334476241653 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 124642668952483307) ^ 1234085831212706 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 124642668952483307) ^ 632703903312098 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 124642668952483307) ^ 39794 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_143572781748184799 : Nat.Prime 143572781748184799 := by
  apply lucas_primality 143572781748184799 (23 : ZMod 143572781748184799)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (2315690028196529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (2315690028196529, 1)] : List FactorBlock).map factorBlockValue).prod) = 143572781748184799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_31
      · exact prime_seventyOneBQ_2315690028196529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (23 : ZMod 143572781748184799) ^ 71786390874092399 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (23 : ZMod 143572781748184799) ^ 4631380056393058 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (23 : ZMod 143572781748184799) ^ 62 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_173477500176250069 : Nat.Prime 173477500176250069 := by
  apply lucas_primality 173477500176250069 (10 : ZMod 173477500176250069)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (41, 1), (1336547, 1), (263811557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (41, 1), (1336547, 1), (263811557, 1)] : List FactorBlock).map factorBlockValue).prod) = 173477500176250069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_41
      · exact prime_seventyOneBQ_1336547
      · exact prime_seventyOneBQ_263811557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 173477500176250069) ^ 86738750088125034 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (10 : ZMod 173477500176250069) ^ 57825833392083356 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (10 : ZMod 173477500176250069) ^ 4231158540884148 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (10 : ZMod 173477500176250069) ^ 129795286044 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (10 : ZMod 173477500176250069) ^ 657581124 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_221849316448808663 : Nat.Prime 221849316448808663 := by
  apply lucas_primality 221849316448808663 (5 : ZMod 221849316448808663)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1559, 1), (2063, 1), (34489171043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1559, 1), (2063, 1), (34489171043, 1)] : List FactorBlock).map factorBlockValue).prod) = 221849316448808663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_1559
      · exact prime_seventyOneBQ_2063
      · exact prime_seventyOneBQ_34489171043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 221849316448808663) ^ 110924658224404331 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 221849316448808663) ^ 142302319723418 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 221849316448808663) ^ 107537235312074 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 221849316448808663) ^ 6432434 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_281558261325688433 : Nat.Prime 281558261325688433 := by
  apply lucas_primality 281558261325688433 (3 : ZMod 281558261325688433)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (75511, 1), (133481, 1), (1745897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (75511, 1), (133481, 1), (1745897, 1)] : List FactorBlock).map factorBlockValue).prod) = 281558261325688433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_75511
      · exact prime_seventyOneBQ_133481
      · exact prime_seventyOneBQ_1745897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 281558261325688433) ^ 140779130662844216 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 281558261325688433) ^ 3728705239312 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 281558261325688433) ^ 2109350853872 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 281558261325688433) ^ 161268540656 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_299053301018337713 : Nat.Prime 299053301018337713 := by
  apply lucas_primality 299053301018337713 (3 : ZMod 299053301018337713)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (11, 3), (223, 1), (307, 1), (439, 1), (66749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (11, 3), (223, 1), (307, 1), (439, 1), (66749, 1)] : List FactorBlock).map factorBlockValue).prod) = 299053301018337713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_11
      · exact prime_seventyOneBQ_223
      · exact prime_seventyOneBQ_307
      · exact prime_seventyOneBQ_439
      · exact prime_seventyOneBQ_66749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 299053301018337713) ^ 149526650509168856 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 299053301018337713) ^ 42721900145476816 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 299053301018337713) ^ 27186663728939792 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 299053301018337713) ^ 1341046192907344 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 299053301018337713) ^ 974114987030416 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 299053301018337713) ^ 681214808697808 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 299053301018337713) ^ 4480266386288 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_337930663596950107 : Nat.Prime 337930663596950107 := by
  apply lucas_primality 337930663596950107 (2 : ZMod 337930663596950107)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (120103, 1), (156315210739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (120103, 1), (156315210739, 1)] : List FactorBlock).map factorBlockValue).prod) = 337930663596950107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_120103
      · exact prime_seventyOneBQ_156315210739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 337930663596950107) ^ 168965331798475053 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 337930663596950107) ^ 112643554532316702 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 337930663596950107) ^ 2813673793302 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 337930663596950107) ^ 2161854 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_487644556012159361 : Nat.Prime 487644556012159361 := by
  apply lucas_primality 487644556012159361 (3 : ZMod 487644556012159361)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 1), (97, 1), (7855099162567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 1), (97, 1), (7855099162567, 1)] : List FactorBlock).map factorBlockValue).prod) = 487644556012159361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_97
      · exact prime_seventyOneBQ_7855099162567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 487644556012159361) ^ 243822278006079680 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 487644556012159361) ^ 97528911202431872 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 487644556012159361) ^ 5027263464042880 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 487644556012159361) ^ 62080 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_648403195703662813 : Nat.Prime 648403195703662813 := by
  apply lucas_primality 648403195703662813 (5 : ZMod 648403195703662813)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (17, 1), (96847, 1), (669780851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (17, 1), (96847, 1), (669780851, 1)] : List FactorBlock).map factorBlockValue).prod) = 648403195703662813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_17
      · exact prime_seventyOneBQ_96847
      · exact prime_seventyOneBQ_669780851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 648403195703662813) ^ 324201597851831406 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 648403195703662813) ^ 216134398567887604 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 648403195703662813) ^ 92629027957666116 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 648403195703662813) ^ 38141364453156636 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 648403195703662813) ^ 6695129386596 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 648403195703662813) ^ 968082612 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_934237349796078551 : Nat.Prime 934237349796078551 := by
  apply lucas_primality 934237349796078551 (11 : ZMod 934237349796078551)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (251, 1), (74441223091321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (251, 1), (74441223091321, 1)] : List FactorBlock).map factorBlockValue).prod) = 934237349796078551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_251
      · exact prime_seventyOneBQ_74441223091321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 934237349796078551) ^ 467118674898039275 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 934237349796078551) ^ 186847469959215710 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 934237349796078551) ^ 3722061154566050 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 934237349796078551) ^ 12550 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_937658791445374459 : Nat.Prime 937658791445374459 := by
  apply lucas_primality 937658791445374459 (3 : ZMod 937658791445374459)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (37, 1), (1407896083251313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (37, 1), (1407896083251313, 1)] : List FactorBlock).map factorBlockValue).prod) = 937658791445374459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_37
      · exact prime_seventyOneBQ_1407896083251313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 937658791445374459) ^ 468829395722687229 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 937658791445374459) ^ 312552930481791486 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 937658791445374459) ^ 25342129498523634 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 937658791445374459) ^ 666 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_1264951695367459993 : Nat.Prime 1264951695367459993 := by
  apply lucas_primality 1264951695367459993 (5 : ZMod 1264951695367459993)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (100313, 1), (525418646041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (100313, 1), (525418646041, 1)] : List FactorBlock).map factorBlockValue).prod) = 1264951695367459993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_100313
      · exact prime_seventyOneBQ_525418646041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1264951695367459993) ^ 632475847683729996 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1264951695367459993) ^ 421650565122486664 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1264951695367459993) ^ 12610047504984 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1264951695367459993) ^ 2407512 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_3054349413592297339 : Nat.Prime 3054349413592297339 := by
  apply lucas_primality 3054349413592297339 (3 : ZMod 3054349413592297339)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (409, 1), (177805880404721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (409, 1), (177805880404721, 1)] : List FactorBlock).map factorBlockValue).prod) = 3054349413592297339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_409
      · exact prime_seventyOneBQ_177805880404721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3054349413592297339) ^ 1527174706796148669 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 3054349413592297339) ^ 1018116471197432446 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 3054349413592297339) ^ 436335630513185334 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 3054349413592297339) ^ 7467846976998282 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 3054349413592297339) ^ 17178 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_4176759703545045091 : Nat.Prime 4176759703545045091 := by
  apply lucas_primality 4176759703545045091 (10 : ZMod 4176759703545045091)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (1907, 1), (4561, 1), (24677, 1), (72073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (1907, 1), (4561, 1), (24677, 1), (72073, 1)] : List FactorBlock).map factorBlockValue).prod) = 4176759703545045091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_1907
      · exact prime_seventyOneBQ_4561
      · exact prime_seventyOneBQ_24677
      · exact prime_seventyOneBQ_72073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 4176759703545045091) ^ 2088379851772522545 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (10 : ZMod 4176759703545045091) ^ 1392253234515015030 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (10 : ZMod 4176759703545045091) ^ 835351940709009018 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (10 : ZMod 4176759703545045091) ^ 2190225329598870 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (10 : ZMod 4176759703545045091) ^ 915755251818690 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (10 : ZMod 4176759703545045091) ^ 169257191050170 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (10 : ZMod 4176759703545045091) ^ 57951794757330 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_4454435879316161801 : Nat.Prime 4454435879316161801 := by
  apply lucas_primality 4454435879316161801 (3 : ZMod 4454435879316161801)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (15572573, 1), (1430218333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (15572573, 1), (1430218333, 1)] : List FactorBlock).map factorBlockValue).prod) = 4454435879316161801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_15572573
      · exact prime_seventyOneBQ_1430218333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4454435879316161801) ^ 2227217939658080900 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 4454435879316161801) ^ 890887175863232360 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 4454435879316161801) ^ 286043666600 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 4454435879316161801) ^ 3114514600 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_5928968234246647651 : Nat.Prime 5928968234246647651 := by
  apply lucas_primality 5928968234246647651 (3 : ZMod 5928968234246647651)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (53, 1), (191, 1), (3904618679737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (53, 1), (191, 1), (3904618679737, 1)] : List FactorBlock).map factorBlockValue).prod) = 5928968234246647651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_53
      · exact prime_seventyOneBQ_191
      · exact prime_seventyOneBQ_3904618679737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5928968234246647651) ^ 2964484117123323825 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 5928968234246647651) ^ 1976322744748882550 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 5928968234246647651) ^ 1185793646849329530 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 5928968234246647651) ^ 111867325174465050 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 5928968234246647651) ^ 31041718503909150 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 5928968234246647651) ^ 1518450 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_8323902487298569999 : Nat.Prime 8323902487298569999 := by
  apply lucas_primality 8323902487298569999 (3 : ZMod 8323902487298569999)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (457, 1), (17048561, 1), (178062229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (457, 1), (17048561, 1), (178062229, 1)] : List FactorBlock).map factorBlockValue).prod) = 8323902487298569999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_457
      · exact prime_seventyOneBQ_17048561
      · exact prime_seventyOneBQ_178062229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8323902487298569999) ^ 4161951243649284999 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 8323902487298569999) ^ 2774634162432856666 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 8323902487298569999) ^ 18214228637414814 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 8323902487298569999) ^ 488246631918 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 8323902487298569999) ^ 46747154262 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_13168570356782819387 : Nat.Prime 13168570356782819387 := by
  apply lucas_primality 13168570356782819387 (2 : ZMod 13168570356782819387)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (163, 1), (173, 1), (877, 1), (14012696989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (163, 1), (173, 1), (877, 1), (14012696989, 1)] : List FactorBlock).map factorBlockValue).prod) = 13168570356782819387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_19
      · exact prime_seventyOneBQ_163
      · exact prime_seventyOneBQ_173
      · exact prime_seventyOneBQ_877
      · exact prime_seventyOneBQ_14012696989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13168570356782819387) ^ 6584285178391409693 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 13168570356782819387) ^ 693082650356990494 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 13168570356782819387) ^ 80788775194986622 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 13168570356782819387) ^ 76118903796432482 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 13168570356782819387) ^ 15015473610926818 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 13168570356782819387) ^ 939759874 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_14453106416033349511 : Nat.Prime 14453106416033349511 := by
  apply lucas_primality 14453106416033349511 (6 : ZMod 14453106416033349511)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (19, 1), (8369, 1), (1009930578949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (19, 1), (8369, 1), (1009930578949, 1)] : List FactorBlock).map factorBlockValue).prod) = 14453106416033349511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_19
      · exact prime_seventyOneBQ_8369
      · exact prime_seventyOneBQ_1009930578949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 14453106416033349511) ^ 7226553208016674755 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 14453106416033349511) ^ 4817702138677783170 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 14453106416033349511) ^ 2890621283206669902 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 14453106416033349511) ^ 760689811370176290 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 14453106416033349511) ^ 1726981290002790 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 14453106416033349511) ^ 14310990 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_23089898352556075009 : Nat.Prime 23089898352556075009 := by
  apply lucas_primality 23089898352556075009 (13 : ZMod 23089898352556075009)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 11), (3, 1), (3758121476653007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 11), (3, 1), (3758121476653007, 1)] : List FactorBlock).map factorBlockValue).prod) = 23089898352556075009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_3758121476653007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 23089898352556075009) ^ 11544949176278037504 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (13 : ZMod 23089898352556075009) ^ 7696632784185358336 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (13 : ZMod 23089898352556075009) ^ 6144 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_44837110952000662903 : Nat.Prime 44837110952000662903 := by
  apply lucas_primality 44837110952000662903 (3 : ZMod 44837110952000662903)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (23, 1), (643, 1), (29723410584709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (23, 1), (643, 1), (29723410584709, 1)] : List FactorBlock).map factorBlockValue).prod) = 44837110952000662903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_17
      · exact prime_seventyOneBQ_23
      · exact prime_seventyOneBQ_643
      · exact prime_seventyOneBQ_29723410584709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 44837110952000662903) ^ 22418555476000331451 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 44837110952000662903) ^ 14945703650666887634 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 44837110952000662903) ^ 2637477114823568406 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 44837110952000662903) ^ 1949439606608724474 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 44837110952000662903) ^ 69731121231727314 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 44837110952000662903) ^ 1508478 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_53043369375128958271 : Nat.Prime 53043369375128958271 := by
  apply lucas_primality 53043369375128958271 (3 : ZMod 53043369375128958271)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (49747, 1), (11847363073849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (49747, 1), (11847363073849, 1)] : List FactorBlock).map factorBlockValue).prod) = 53043369375128958271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_49747
      · exact prime_seventyOneBQ_11847363073849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 53043369375128958271) ^ 26521684687564479135 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 53043369375128958271) ^ 17681123125042986090 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 53043369375128958271) ^ 10608673875025791654 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 53043369375128958271) ^ 1066262676646410 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 53043369375128958271) ^ 4477230 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_104443623653658657409 : Nat.Prime 104443623653658657409 := by
  apply lucas_primality 104443623653658657409 (7 : ZMod 104443623653658657409)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (1229, 1), (4099, 1), (77731, 1), (231529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (1229, 1), (4099, 1), (77731, 1), (231529, 1)] : List FactorBlock).map factorBlockValue).prod) = 104443623653658657409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_1229
      · exact prime_seventyOneBQ_4099
      · exact prime_seventyOneBQ_77731
      · exact prime_seventyOneBQ_231529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 104443623653658657409) ^ 52221811826829328704 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 104443623653658657409) ^ 34814541217886219136 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 104443623653658657409) ^ 84982606715751552 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 104443623653658657409) ^ 25480269249489792 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 104443623653658657409) ^ 1343654702160768 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 104443623653658657409) ^ 451103851585152 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_119999749955170557793 : Nat.Prime 119999749955170557793 := by
  apply lucas_primality 119999749955170557793 (5 : ZMod 119999749955170557793)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (157, 1), (199, 1), (487177, 1), (82123907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (157, 1), (199, 1), (487177, 1), (82123907, 1)] : List FactorBlock).map factorBlockValue).prod) = 119999749955170557793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_157
      · exact prime_seventyOneBQ_199
      · exact prime_seventyOneBQ_487177
      · exact prime_seventyOneBQ_82123907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 119999749955170557793) ^ 59999874977585278896 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 119999749955170557793) ^ 39999916651723519264 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 119999749955170557793) ^ 764329617548857056 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 119999749955170557793) ^ 603013818870203808 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 119999749955170557793) ^ 246316533734496 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 119999749955170557793) ^ 1461203617056 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_319364258987304358001 : Nat.Prime 319364258987304358001 := by
  apply lucas_primality 319364258987304358001 (3 : ZMod 319364258987304358001)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 3), (37, 1), (704897, 1), (6122501911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 3), (37, 1), (704897, 1), (6122501911, 1)] : List FactorBlock).map factorBlockValue).prod) = 319364258987304358001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_37
      · exact prime_seventyOneBQ_704897
      · exact prime_seventyOneBQ_6122501911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 319364258987304358001) ^ 159682129493652179000 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 319364258987304358001) ^ 63872851797460871600 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 319364258987304358001) ^ 8631466459116334000 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 319364258987304358001) ^ 453065141414000 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 319364258987304358001) ^ 52162378000 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_426885712865758630873 : Nat.Prime 426885712865758630873 := by
  apply lucas_primality 426885712865758630873 (5 : ZMod 426885712865758630873)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5928968234246647651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5928968234246647651, 1)] : List FactorBlock).map factorBlockValue).prod) = 426885712865758630873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_5928968234246647651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 426885712865758630873) ^ 213442856432879315436 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 426885712865758630873) ^ 142295237621919543624 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 426885712865758630873) ^ 72 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_509142506116906771349 : Nat.Prime 509142506116906771349 := by
  apply lucas_primality 509142506116906771349 (2 : ZMod 509142506116906771349)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (401, 1), (1553, 1), (380777, 1), (536775677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (401, 1), (1553, 1), (380777, 1), (536775677, 1)] : List FactorBlock).map factorBlockValue).prod) = 509142506116906771349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_401
      · exact prime_seventyOneBQ_1553
      · exact prime_seventyOneBQ_380777
      · exact prime_seventyOneBQ_536775677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 509142506116906771349) ^ 254571253058453385674 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 509142506116906771349) ^ 1269682060141912148 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 509142506116906771349) ^ 327844498465490516 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 509142506116906771349) ^ 1337114652715124 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 509142506116906771349) ^ 948520076324 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_641016722369481874753 : Nat.Prime 641016722369481874753 := by
  apply lucas_primality 641016722369481874753 (11 : ZMod 641016722369481874753)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (7, 1), (466079, 1), (1023317862527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (7, 1), (466079, 1), (1023317862527, 1)] : List FactorBlock).map factorBlockValue).prod) = 641016722369481874753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_466079
      · exact prime_seventyOneBQ_1023317862527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 641016722369481874753) ^ 320508361184740937376 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 641016722369481874753) ^ 213672240789827291584 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 641016722369481874753) ^ 91573817481354553536 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 641016722369481874753) ^ 1375339207236288 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 641016722369481874753) ^ 626410176 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_728869901998847848003 : Nat.Prime 728869901998847848003 := by
  apply lucas_primality 728869901998847848003 (2 : ZMod 728869901998847848003)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1101509, 1), (1261069, 1), (29150809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1101509, 1), (1261069, 1), (29150809, 1)] : List FactorBlock).map factorBlockValue).prod) = 728869901998847848003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_1101509
      · exact prime_seventyOneBQ_1261069
      · exact prime_seventyOneBQ_29150809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 728869901998847848003) ^ 364434950999423924001 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 728869901998847848003) ^ 242956633999615949334 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 728869901998847848003) ^ 661701267986778 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 728869901998847848003) ^ 577977812474058 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 728869901998847848003) ^ 25003419356178 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_1163931439351910573711 : Nat.Prime 1163931439351910573711 := by
  apply lucas_primality 1163931439351910573711 (11 : ZMod 1163931439351910573711)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (1367, 1), (1489, 1), (3363684589501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (1367, 1), (1489, 1), (3363684589501, 1)] : List FactorBlock).map factorBlockValue).prod) = 1163931439351910573711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_17
      · exact prime_seventyOneBQ_1367
      · exact prime_seventyOneBQ_1489
      · exact prime_seventyOneBQ_3363684589501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1163931439351910573711) ^ 581965719675955286855 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 1163931439351910573711) ^ 232786287870382114742 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 1163931439351910573711) ^ 68466555255994739630 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 1163931439351910573711) ^ 851449480140388130 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 1163931439351910573711) ^ 781686661754137390 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 1163931439351910573711) ^ 346028710 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_3783556031505675805979 : Nat.Prime 3783556031505675805979 := by
  apply lucas_primality 3783556031505675805979 (2 : ZMod 3783556031505675805979)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (61, 1), (8761, 1), (7340527, 1), (37095059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (61, 1), (8761, 1), (7340527, 1), (37095059, 1)] : List FactorBlock).map factorBlockValue).prod) = 3783556031505675805979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_13
      · exact prime_seventyOneBQ_61
      · exact prime_seventyOneBQ_8761
      · exact prime_seventyOneBQ_7340527
      · exact prime_seventyOneBQ_37095059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3783556031505675805979) ^ 1891778015752837902989 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3783556031505675805979) ^ 291042771654282754306 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3783556031505675805979) ^ 62025508713207800098 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3783556031505675805979) ^ 431863489499563498 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3783556031505675805979) ^ 515433841671814 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3783556031505675805979) ^ 101996226276542 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_3868860156127086397451 : Nat.Prime 3868860156127086397451 := by
  apply lucas_primality 3868860156127086397451 (2 : ZMod 3868860156127086397451)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (23, 1), (709, 1), (4745029933313407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (23, 1), (709, 1), (4745029933313407, 1)] : List FactorBlock).map factorBlockValue).prod) = 3868860156127086397451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_23
      · exact prime_seventyOneBQ_709
      · exact prime_seventyOneBQ_4745029933313407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3868860156127086397451) ^ 1934430078063543198725 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3868860156127086397451) ^ 773772031225417279490 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3868860156127086397451) ^ 168211311135960278150 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3868860156127086397451) ^ 5456784423310418050 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3868860156127086397451) ^ 815350 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_4087210800909478623253 : Nat.Prime 4087210800909478623253 := by
  apply lucas_primality 4087210800909478623253 (6 : ZMod 4087210800909478623253)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (179, 1), (787975393, 1), (2414794093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (179, 1), (787975393, 1), (2414794093, 1)] : List FactorBlock).map factorBlockValue).prod) = 4087210800909478623253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_179
      · exact prime_seventyOneBQ_787975393
      · exact prime_seventyOneBQ_2414794093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 4087210800909478623253) ^ 2043605400454739311626 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 4087210800909478623253) ^ 1362403600303159541084 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 4087210800909478623253) ^ 22833579893349042588 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 4087210800909478623253) ^ 5186977711764 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 4087210800909478623253) ^ 1692571144164 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_4911391676970314407037 : Nat.Prime 4911391676970314407037 := by
  apply lucas_primality 4911391676970314407037 (2 : ZMod 4911391676970314407037)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (2999, 1), (37219919344101931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (2999, 1), (37219919344101931, 1)] : List FactorBlock).map factorBlockValue).prod) = 4911391676970314407037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_11
      · exact prime_seventyOneBQ_2999
      · exact prime_seventyOneBQ_37219919344101931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4911391676970314407037) ^ 2455695838485157203518 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4911391676970314407037) ^ 446490152451846764276 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4911391676970314407037) ^ 1637676451140484964 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4911391676970314407037) ^ 131956 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_56348914098280139275237 : Nat.Prime 56348914098280139275237 := by
  apply lucas_primality 56348914098280139275237 (2 : ZMod 56348914098280139275237)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (426885712865758630873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (426885712865758630873, 1)] : List FactorBlock).map factorBlockValue).prod) = 56348914098280139275237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_11
      · exact prime_seventyOneBQ_426885712865758630873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 56348914098280139275237) ^ 28174457049140069637618 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 56348914098280139275237) ^ 18782971366093379758412 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 56348914098280139275237) ^ 5122628554389103570476 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 56348914098280139275237) ^ 132 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_63593121331864903943431 : Nat.Prime 63593121331864903943431 := by
  apply lucas_primality 63593121331864903943431 (3 : ZMod 63593121331864903943431)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (1571, 1), (1434451, 1), (44792746241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (1571, 1), (1434451, 1), (44792746241, 1)] : List FactorBlock).map factorBlockValue).prod) = 63593121331864903943431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_1571
      · exact prime_seventyOneBQ_1434451
      · exact prime_seventyOneBQ_44792746241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 63593121331864903943431) ^ 31796560665932451971715 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 63593121331864903943431) ^ 21197707110621634647810 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 63593121331864903943431) ^ 12718624266372980788686 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 63593121331864903943431) ^ 9084731618837843420490 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 63593121331864903943431) ^ 40479389772033675330 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 63593121331864903943431) ^ 44332724737104930 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 63593121331864903943431) ^ 1419719188230 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_69484434281332113790697 : Nat.Prime 69484434281332113790697 := by
  apply lucas_primality 69484434281332113790697 (3 : ZMod 69484434281332113790697)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (33487, 1), (41983, 1), (6177998917997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (33487, 1), (41983, 1), (6177998917997, 1)] : List FactorBlock).map factorBlockValue).prod) = 69484434281332113790697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_33487
      · exact prime_seventyOneBQ_41983
      · exact prime_seventyOneBQ_6177998917997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 69484434281332113790697) ^ 34742217140666056895348 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 69484434281332113790697) ^ 2074967428594144408 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 69484434281332113790697) ^ 1655061198135724312 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 69484434281332113790697) ^ 11247077768 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_77768249503462089002881 : Nat.Prime 77768249503462089002881 := by
  apply lucas_primality 77768249503462089002881 (11 : ZMod 77768249503462089002881)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (5, 1), (17, 1), (19, 1), (109883, 1), (1141216558721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (5, 1), (17, 1), (19, 1), (109883, 1), (1141216558721, 1)] : List FactorBlock).map factorBlockValue).prod) = 77768249503462089002881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_17
      · exact prime_seventyOneBQ_19
      · exact prime_seventyOneBQ_109883
      · exact prime_seventyOneBQ_1141216558721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 77768249503462089002881) ^ 38884124751731044501440 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 77768249503462089002881) ^ 25922749834487363000960 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 77768249503462089002881) ^ 15553649900692417800576 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 77768249503462089002881) ^ 4574602911968358176640 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 77768249503462089002881) ^ 4093065763340109947520 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 77768249503462089002881) ^ 707736861056415360 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (11 : ZMod 77768249503462089002881) ^ 68145041280 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_85187843232697376898977 : Nat.Prime 85187843232697376898977 := by
  apply lucas_primality 85187843232697376898977 (3 : ZMod 85187843232697376898977)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (378401, 1), (7035182520716893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (378401, 1), (7035182520716893, 1)] : List FactorBlock).map factorBlockValue).prod) = 85187843232697376898977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_378401
      · exact prime_seventyOneBQ_7035182520716893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 85187843232697376898977) ^ 42593921616348688449488 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 85187843232697376898977) ^ 225125840662940576 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 85187843232697376898977) ^ 12108832 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_200451688850389807486661 : Nat.Prime 200451688850389807486661 := by
  apply lucas_primality 200451688850389807486661 (2 : ZMod 200451688850389807486661)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (5453977, 1), (17311913, 1), (106150333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (5453977, 1), (17311913, 1), (106150333, 1)] : List FactorBlock).map factorBlockValue).prod) = 200451688850389807486661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_5453977
      · exact prime_seventyOneBQ_17311913
      · exact prime_seventyOneBQ_106150333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 200451688850389807486661) ^ 100225844425194903743330 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 200451688850389807486661) ^ 40090337770077961497332 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 200451688850389807486661) ^ 36753306596340580 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 200451688850389807486661) ^ 11578829494486820 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 200451688850389807486661) ^ 1888375506560020 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_204166339376612310632161 : Nat.Prime 204166339376612310632161 := by
  apply lucas_primality 204166339376612310632161 (7 : ZMod 204166339376612310632161)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (310069687, 1), (457259080997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (310069687, 1), (457259080997, 1)] : List FactorBlock).map factorBlockValue).prod) = 204166339376612310632161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_310069687
      · exact prime_seventyOneBQ_457259080997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 204166339376612310632161) ^ 102083169688306155316080 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 204166339376612310632161) ^ 68055446458870770210720 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 204166339376612310632161) ^ 40833267875322462126432 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 204166339376612310632161) ^ 658453076635680 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 204166339376612310632161) ^ 446500349280 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_204999020126750153596861 : Nat.Prime 204999020126750153596861 := by
  apply lucas_primality 204999020126750153596861 (6 : ZMod 204999020126750153596861)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (53, 1), (937, 1), (4801, 1), (4776745615207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (53, 1), (937, 1), (4801, 1), (4776745615207, 1)] : List FactorBlock).map factorBlockValue).prod) = 204999020126750153596861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_53
      · exact prime_seventyOneBQ_937
      · exact prime_seventyOneBQ_4801
      · exact prime_seventyOneBQ_4776745615207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 204999020126750153596861) ^ 102499510063375076798430 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 204999020126750153596861) ^ 68333006708916717865620 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 204999020126750153596861) ^ 40999804025350030719372 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 204999020126750153596861) ^ 3867906040127361388620 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 204999020126750153596861) ^ 218782305364728018780 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 204999020126750153596861) ^ 42699233519423068860 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 204999020126750153596861) ^ 42916042980 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_233276868698623213463171 : Nat.Prime 233276868698623213463171 := by
  apply lucas_primality 233276868698623213463171 (7 : ZMod 233276868698623213463171)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (109, 1), (712507, 1), (300369646712659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (109, 1), (712507, 1), (300369646712659, 1)] : List FactorBlock).map factorBlockValue).prod) = 233276868698623213463171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_109
      · exact prime_seventyOneBQ_712507
      · exact prime_seventyOneBQ_300369646712659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 233276868698623213463171) ^ 116638434349311606731585 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 233276868698623213463171) ^ 46655373739724642692634 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 233276868698623213463171) ^ 2140154758702965261130 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 233276868698623213463171) ^ 327402914916798310 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 233276868698623213463171) ^ 776632630 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_298534192950705019945823 : Nat.Prime 298534192950705019945823 := by
  apply lucas_primality 298534192950705019945823 (5 : ZMod 298534192950705019945823)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (22363180369, 1), (6674681061119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (22363180369, 1), (6674681061119, 1)] : List FactorBlock).map factorBlockValue).prod) = 298534192950705019945823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_22363180369
      · exact prime_seventyOneBQ_6674681061119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 298534192950705019945823) ^ 149267096475352509972911 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 298534192950705019945823) ^ 13349362122238 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 298534192950705019945823) ^ 44726360738 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_337503965531481862053977 : Nat.Prime 337503965531481862053977 := by
  apply lucas_primality 337503965531481862053977 (3 : ZMod 337503965531481862053977)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (4049, 1), (79379, 1), (18751562110751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (4049, 1), (79379, 1), (18751562110751, 1)] : List FactorBlock).map factorBlockValue).prod) = 337503965531481862053977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_4049
      · exact prime_seventyOneBQ_79379
      · exact prime_seventyOneBQ_18751562110751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 337503965531481862053977) ^ 168751982765740931026988 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 337503965531481862053977) ^ 48214852218783123150568 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 337503965531481862053977) ^ 83354893932201003224 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 337503965531481862053977) ^ 4251804199240124744 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 337503965531481862053977) ^ 17998711976 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_434261178561896704501421 : Nat.Prime 434261178561896704501421 := by
  apply lucas_primality 434261178561896704501421 (2 : ZMod 434261178561896704501421)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (67, 1), (137, 1), (337930663596950107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (67, 1), (137, 1), (337930663596950107, 1)] : List FactorBlock).map factorBlockValue).prod) = 434261178561896704501421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_67
      · exact prime_seventyOneBQ_137
      · exact prime_seventyOneBQ_337930663596950107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 434261178561896704501421) ^ 217130589280948352250710 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 434261178561896704501421) ^ 86852235712379340900284 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 434261178561896704501421) ^ 62037311223128100643060 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 434261178561896704501421) ^ 6481510127789503052260 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 434261178561896704501421) ^ 3169789624539392003660 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 434261178561896704501421) ^ 1285060 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_548021157864741924994331 : Nat.Prime 548021157864741924994331 := by
  apply lucas_primality 548021157864741924994331 (2 : ZMod 548021157864741924994331)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (562613, 1), (13915202250538163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (562613, 1), (13915202250538163, 1)] : List FactorBlock).map factorBlockValue).prod) = 548021157864741924994331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_562613
      · exact prime_seventyOneBQ_13915202250538163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 548021157864741924994331) ^ 274010578932370962497165 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 548021157864741924994331) ^ 109604231572948384998866 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 548021157864741924994331) ^ 78288736837820274999190 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 548021157864741924994331) ^ 974064157537671410 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 548021157864741924994331) ^ 39382910 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_603349137619409778208853 : Nat.Prime 603349137619409778208853 := by
  apply lucas_primality 603349137619409778208853 (2 : ZMod 603349137619409778208853)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (353, 1), (18517, 1), (23076151048527713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (353, 1), (18517, 1), (23076151048527713, 1)] : List FactorBlock).map factorBlockValue).prod) = 603349137619409778208853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_353
      · exact prime_seventyOneBQ_18517
      · exact prime_seventyOneBQ_23076151048527713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 603349137619409778208853) ^ 301674568809704889104426 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 603349137619409778208853) ^ 1709204355862350646484 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 603349137619409778208853) ^ 32583525280521130756 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 603349137619409778208853) ^ 26146004 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_756170264947574817970837 : Nat.Prime 756170264947574817970837 := by
  apply lucas_primality 756170264947574817970837 (2 : ZMod 756170264947574817970837)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (43, 1), (33837336371, 1), (43308558151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (43, 1), (33837336371, 1), (43308558151, 1)] : List FactorBlock).map factorBlockValue).prod) = 756170264947574817970837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_43
      · exact prime_seventyOneBQ_33837336371
      · exact prime_seventyOneBQ_43308558151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 756170264947574817970837) ^ 378085132473787408985418 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 756170264947574817970837) ^ 252056754982524939323612 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 756170264947574817970837) ^ 17585354998780809720252 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 756170264947574817970837) ^ 22347216005916 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 756170264947574817970837) ^ 17460065567436 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_1259769311611543783667107 : Nat.Prime 1259769311611543783667107 := by
  apply lucas_primality 1259769311611543783667107 (2 : ZMod 1259769311611543783667107)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 2), (161911, 1), (34753837, 1), (84610073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 2), (161911, 1), (34753837, 1), (84610073, 1)] : List FactorBlock).map factorBlockValue).prod) = 1259769311611543783667107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_161911
      · exact prime_seventyOneBQ_34753837
      · exact prime_seventyOneBQ_84610073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1259769311611543783667107) ^ 629884655805771891833553 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1259769311611543783667107) ^ 419923103870514594555702 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1259769311611543783667107) ^ 179967044515934826238158 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1259769311611543783667107) ^ 7780628318097867246 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1259769311611543783667107) ^ 36248351847064938 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1259769311611543783667107) ^ 14889117417633522 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_1399412313010359358373317 : Nat.Prime 1399412313010359358373317 := by
  apply lucas_primality 1399412313010359358373317 (2 : ZMod 1399412313010359358373317)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (103, 1), (34019, 1), (1957747848921247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (103, 1), (34019, 1), (1957747848921247, 1)] : List FactorBlock).map factorBlockValue).prod) = 1399412313010359358373317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_17
      · exact prime_seventyOneBQ_103
      · exact prime_seventyOneBQ_34019
      · exact prime_seventyOneBQ_1957747848921247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1399412313010359358373317) ^ 699706156505179679186658 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1399412313010359358373317) ^ 466470771003453119457772 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1399412313010359358373317) ^ 82318371353550550492548 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1399412313010359358373317) ^ 13586527310780187945372 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1399412313010359358373317) ^ 41136197801533241964 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1399412313010359358373317) ^ 714807228 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_1856689864439291868907469 : Nat.Prime 1856689864439291868907469 := by
  apply lucas_primality 1856689864439291868907469 (2 : ZMod 1856689864439291868907469)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1759, 1), (13049, 1), (20222568012866837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1759, 1), (13049, 1), (20222568012866837, 1)] : List FactorBlock).map factorBlockValue).prod) = 1856689864439291868907469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_1759
      · exact prime_seventyOneBQ_13049
      · exact prime_seventyOneBQ_20222568012866837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1856689864439291868907469) ^ 928344932219645934453734 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1856689864439291868907469) ^ 1055537159999597424052 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1856689864439291868907469) ^ 142285988538531065132 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1856689864439291868907469) ^ 91812764 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_3606330502289928913615169 : Nat.Prime 3606330502289928913615169 := by
  apply lucas_primality 3606330502289928913615169 (3 : ZMod 3606330502289928913615169)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (56348914098280139275237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (56348914098280139275237, 1)] : List FactorBlock).map factorBlockValue).prod) = 3606330502289928913615169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_56348914098280139275237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 3606330502289928913615169) ^ 1803165251144964456807584 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 3606330502289928913615169) ^ 64 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_8677860929525523146211793 : Nat.Prime 8677860929525523146211793 := by
  apply lucas_primality 8677860929525523146211793 (13 : ZMod 8677860929525523146211793)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (19, 1), (59, 1), (877, 1), (24809, 1), (823596465227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (19, 1), (59, 1), (877, 1), (24809, 1), (823596465227, 1)] : List FactorBlock).map factorBlockValue).prod) = 8677860929525523146211793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_19
      · exact prime_seventyOneBQ_59
      · exact prime_seventyOneBQ_877
      · exact prime_seventyOneBQ_24809
      · exact prime_seventyOneBQ_823596465227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 8677860929525523146211793) ^ 4338930464762761573105896 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (13 : ZMod 8677860929525523146211793) ^ 2892620309841841048737264 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (13 : ZMod 8677860929525523146211793) ^ 456729522606606481379568 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (13 : ZMod 8677860929525523146211793) ^ 147082388636025816037488 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (13 : ZMod 8677860929525523146211793) ^ 9894938346095237338896 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (13 : ZMod 8677860929525523146211793) ^ 349786808397175345488 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (13 : ZMod 8677860929525523146211793) ^ 10536544650096 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_18905619092635221935429431 : Nat.Prime 18905619092635221935429431 := by
  apply lucas_primality 18905619092635221935429431 (6 : ZMod 18905619092635221935429431)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (11, 1), (173, 1), (541, 1), (683477, 1), (298530312937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (11, 1), (173, 1), (541, 1), (683477, 1), (298530312937, 1)] : List FactorBlock).map factorBlockValue).prod) = 18905619092635221935429431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_11
      · exact prime_seventyOneBQ_173
      · exact prime_seventyOneBQ_541
      · exact prime_seventyOneBQ_683477
      · exact prime_seventyOneBQ_298530312937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 18905619092635221935429431) ^ 9452809546317610967714715 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 18905619092635221935429431) ^ 6301873030878407311809810 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 18905619092635221935429431) ^ 3781123818527044387085886 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 18905619092635221935429431) ^ 1718692644785020175948130 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 18905619092635221935429431) ^ 109281035217544635464910 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 18905619092635221935429431) ^ 34945691483614088605230 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 18905619092635221935429431) ^ 27660944102925514590 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 18905619092635221935429431) ^ 63328976232390 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_20251133599831214811412949 : Nat.Prime 20251133599831214811412949 := by
  apply lucas_primality 20251133599831214811412949 (2 : ZMod 20251133599831214811412949)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (167, 1), (303027271, 1), (14292003754163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (167, 1), (303027271, 1), (14292003754163, 1)] : List FactorBlock).map factorBlockValue).prod) = 20251133599831214811412949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_167
      · exact prime_seventyOneBQ_303027271
      · exact prime_seventyOneBQ_14292003754163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20251133599831214811412949) ^ 10125566799915607405706474 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 20251133599831214811412949) ^ 2893019085690173544487564 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 20251133599831214811412949) ^ 121264273052881525816844 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 20251133599831214811412949) ^ 66829409554466188 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 20251133599831214811412949) ^ 1416955519196 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_22785273825000104612732539 : Nat.Prime 22785273825000104612732539 := by
  apply lucas_primality 22785273825000104612732539 (2 : ZMod 22785273825000104612732539)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (13, 1), (109, 1), (2777, 1), (12533332074459611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (13, 1), (109, 1), (2777, 1), (12533332074459611, 1)] : List FactorBlock).map factorBlockValue).prod) = 22785273825000104612732539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_11
      · exact prime_seventyOneBQ_13
      · exact prime_seventyOneBQ_109
      · exact prime_seventyOneBQ_2777
      · exact prime_seventyOneBQ_12533332074459611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22785273825000104612732539) ^ 11392636912500052306366269 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 22785273825000104612732539) ^ 7595091275000034870910846 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 22785273825000104612732539) ^ 3255039117857157801818934 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 22785273825000104612732539) ^ 2071388529545464055702958 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 22785273825000104612732539) ^ 1752713371153854200979426 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 22785273825000104612732539) ^ 209039209403670684520482 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 22785273825000104612732539) ^ 8204995975873282179594 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 22785273825000104612732539) ^ 1817974158 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_173790784205590860027550049 : Nat.Prime 173790784205590860027550049 := by
  apply lucas_primality 173790784205590860027550049 (3 : ZMod 173790784205590860027550049)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (224317187737, 1), (24211082802947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (224317187737, 1), (24211082802947, 1)] : List FactorBlock).map factorBlockValue).prod) = 173790784205590860027550049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_224317187737
      · exact prime_seventyOneBQ_24211082802947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 173790784205590860027550049) ^ 86895392102795430013775024 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 173790784205590860027550049) ^ 774754649694304 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 173790784205590860027550049) ^ 7178150007584 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_355681986319069429632655397 : Nat.Prime 355681986319069429632655397 := by
  apply lucas_primality 355681986319069429632655397 (2 : ZMod 355681986319069429632655397)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (541267, 1), (3591793, 1), (1063678973353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (541267, 1), (3591793, 1), (1063678973353, 1)] : List FactorBlock).map factorBlockValue).prod) = 355681986319069429632655397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_43
      · exact prime_seventyOneBQ_541267
      · exact prime_seventyOneBQ_3591793
      · exact prime_seventyOneBQ_1063678973353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 355681986319069429632655397) ^ 177840993159534714816327698 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 355681986319069429632655397) ^ 8271674100443475107736172 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 355681986319069429632655397) ^ 657128526806676611788 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 355681986319069429632655397) ^ 99026304221615619172 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 355681986319069429632655397) ^ 334388471737732 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_441794467217370449438456177 : Nat.Prime 441794467217370449438456177 := by
  apply lucas_primality 441794467217370449438456177 (3 : ZMod 441794467217370449438456177)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (281, 1), (743, 1), (518765383, 1), (254937761599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (281, 1), (743, 1), (518765383, 1), (254937761599, 1)] : List FactorBlock).map factorBlockValue).prod) = 441794467217370449438456177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_281
      · exact prime_seventyOneBQ_743
      · exact prime_seventyOneBQ_518765383
      · exact prime_seventyOneBQ_254937761599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 441794467217370449438456177) ^ 220897233608685224719228088 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 441794467217370449438456177) ^ 1572222303264663521133296 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 441794467217370449438456177) ^ 594608973374657401666832 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 441794467217370449438456177) ^ 851626730878784272 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 441794467217370449438456177) ^ 1732950287342224 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_612707655264966316739464771 : Nat.Prime 612707655264966316739464771 := by
  apply lucas_primality 612707655264966316739464771 (7 : ZMod 612707655264966316739464771)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (1856689864439291868907469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (1856689864439291868907469, 1)] : List FactorBlock).map factorBlockValue).prod) = 612707655264966316739464771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_11
      · exact prime_seventyOneBQ_1856689864439291868907469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 612707655264966316739464771) ^ 306353827632483158369732385 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 612707655264966316739464771) ^ 204235885088322105579821590 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 612707655264966316739464771) ^ 122541531052993263347892954 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 612707655264966316739464771) ^ 55700695933178756067224070 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (7 : ZMod 612707655264966316739464771) ^ 330 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_688040563699183486830382571 : Nat.Prime 688040563699183486830382571 := by
  apply lucas_primality 688040563699183486830382571 (2 : ZMod 688040563699183486830382571)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (337, 1), (204166339376612310632161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (337, 1), (204166339376612310632161, 1)] : List FactorBlock).map factorBlockValue).prod) = 688040563699183486830382571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_337
      · exact prime_seventyOneBQ_204166339376612310632161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 688040563699183486830382571) ^ 344020281849591743415191285 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 688040563699183486830382571) ^ 137608112739836697366076514 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 688040563699183486830382571) ^ 2041663393766123106321610 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 688040563699183486830382571) ^ 3370 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_1614249014832699719102051417 : Nat.Prime 1614249014832699719102051417 := by
  apply lucas_primality 1614249014832699719102051417 (3 : ZMod 1614249014832699719102051417)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (31, 2), (131, 1), (383, 1), (270601, 1), (315617887391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (31, 2), (131, 1), (383, 1), (270601, 1), (315617887391, 1)] : List FactorBlock).map factorBlockValue).prod) = 1614249014832699719102051417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_7
      · exact prime_seventyOneBQ_31
      · exact prime_seventyOneBQ_131
      · exact prime_seventyOneBQ_383
      · exact prime_seventyOneBQ_270601
      · exact prime_seventyOneBQ_315617887391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1614249014832699719102051417) ^ 807124507416349859551025708 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1614249014832699719102051417) ^ 230607002118957102728864488 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1614249014832699719102051417) ^ 52072548865570958680711336 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1614249014832699719102051417) ^ 12322511563608394802305736 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1614249014832699719102051417) ^ 4214749385986161146480552 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1614249014832699719102051417) ^ 5965421468629826641816 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1614249014832699719102051417) ^ 5114567580996776 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_1713080587169395620271564769 : Nat.Prime 1713080587169395620271564769 := by
  apply lucas_primality 1713080587169395620271564769 (3 : ZMod 1713080587169395620271564769)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (13, 1), (31, 2), (131, 1), (383, 1), (270601, 1), (315617887391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (13, 1), (31, 2), (131, 1), (383, 1), (270601, 1), (315617887391, 1)] : List FactorBlock).map factorBlockValue).prod) = 1713080587169395620271564769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_13
      · exact prime_seventyOneBQ_31
      · exact prime_seventyOneBQ_131
      · exact prime_seventyOneBQ_383
      · exact prime_seventyOneBQ_270601
      · exact prime_seventyOneBQ_315617887391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1713080587169395620271564769) ^ 856540293584697810135782384 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1713080587169395620271564769) ^ 131775429782261201559351136 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1713080587169395620271564769) ^ 55260664102238568395856928 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1713080587169395620271564769) ^ 13076951047094623055508128 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1713080587169395620271564769) ^ 4472795266760824073816096 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1713080587169395620271564769) ^ 6330651354464305823968 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1713080587169395620271564769) ^ 5427704371670048 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_5995782055092884670950476691 : Nat.Prime 5995782055092884670950476691 := by
  apply lucas_primality 5995782055092884670950476691 (2 : ZMod 5995782055092884670950476691)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (191, 1), (39905635883, 1), (78664400127073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (191, 1), (39905635883, 1), (78664400127073, 1)] : List FactorBlock).map factorBlockValue).prod) = 5995782055092884670950476691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_191
      · exact prime_seventyOneBQ_39905635883
      · exact prime_seventyOneBQ_78664400127073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5995782055092884670950476691) ^ 2997891027546442335475238345 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5995782055092884670950476691) ^ 1199156411018576934190095338 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5995782055092884670950476691) ^ 31391529084255940685604590 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5995782055092884670950476691) ^ 150249004242709430 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5995782055092884670950476691) ^ 76219764536530 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_10492618596412548174163334201 : Nat.Prime 10492618596412548174163334201 := by
  apply lucas_primality 10492618596412548174163334201 (6 : ZMod 10492618596412548174163334201)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (11, 1), (46853, 1), (140111, 1), (256471, 1), (2832782977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (11, 1), (46853, 1), (140111, 1), (256471, 1), (2832782977, 1)] : List FactorBlock).map factorBlockValue).prod) = 10492618596412548174163334201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_5
      · exact prime_seventyOneBQ_11
      · exact prime_seventyOneBQ_46853
      · exact prime_seventyOneBQ_140111
      · exact prime_seventyOneBQ_256471
      · exact prime_seventyOneBQ_2832782977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 10492618596412548174163334201) ^ 5246309298206274087081667100 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 10492618596412548174163334201) ^ 2098523719282509634832666840 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 10492618596412548174163334201) ^ 953874417855686197651212200 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 10492618596412548174163334201) ^ 223947636147366191581400 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 10492618596412548174163334201) ^ 74887900282008894192200 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 10492618596412548174163334201) ^ 40911520586781929240200 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (6 : ZMod 10492618596412548174163334201) ^ 3703996628617324600 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_10492618596412548174163334207 : Nat.Prime 10492618596412548174163334207 := by
  apply lucas_primality 10492618596412548174163334207 (5 : ZMod 10492618596412548174163334207)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (398396269, 1), (13168570356782819387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (398396269, 1), (13168570356782819387, 1)] : List FactorBlock).map factorBlockValue).prod) = 10492618596412548174163334207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_398396269
      · exact prime_seventyOneBQ_13168570356782819387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 10492618596412548174163334207) ^ 5246309298206274087081667103 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 10492618596412548174163334207) ^ 26337140713565638774 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 10492618596412548174163334207) ^ 796792538 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_13990158128550064232217778939 : Nat.Prime 13990158128550064232217778939 := by
  apply lucas_primality 13990158128550064232217778939 (2 : ZMod 13990158128550064232217778939)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (29, 1), (43, 1), (13901, 1), (44837110952000662903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (29, 1), (43, 1), (13901, 1), (44837110952000662903, 1)] : List FactorBlock).map factorBlockValue).prod) = 13990158128550064232217778939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_29
      · exact prime_seventyOneBQ_43
      · exact prime_seventyOneBQ_13901
      · exact prime_seventyOneBQ_44837110952000662903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13990158128550064232217778939) ^ 6995079064275032116108889469 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 13990158128550064232217778939) ^ 4663386042850021410739259646 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 13990158128550064232217778939) ^ 482419245812071180421302722 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 13990158128550064232217778939) ^ 325352514617443354237622766 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 13990158128550064232217778939) ^ 1006413792428606879520738 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (2 : ZMod 13990158128550064232217778939) ^ 312021846 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_83940948771300385393306673609 : Nat.Prime 83940948771300385393306673609 := by
  apply lucas_primality 83940948771300385393306673609 (3 : ZMod 83940948771300385393306673609)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (10492618596412548174163334201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (10492618596412548174163334201, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_10492618596412548174163334201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 83940948771300385393306673609) ^ 41970474385650192696653336804 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 83940948771300385393306673609) ^ 8 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_83940948771300385393306673617 : Nat.Prime 83940948771300385393306673617 := by
  apply lucas_primality 83940948771300385393306673617 (5 : ZMod 83940948771300385393306673617)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (4027, 1), (434261178561896704501421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (4027, 1), (434261178561896704501421, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_4027
      · exact prime_seventyOneBQ_434261178561896704501421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 83940948771300385393306673617) ^ 41970474385650192696653336808 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 83940948771300385393306673617) ^ 27980316257100128464435557872 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 83940948771300385393306673617) ^ 20844536570971041816068208 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (5 : ZMod 83940948771300385393306673617) ^ 193296 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem prime_seventyOneBQ_83940948771300385393306673623 : Nat.Prime 83940948771300385393306673623 := by
  apply lucas_primality 83940948771300385393306673623 (3 : ZMod 83940948771300385393306673623)
  · rw [← seventyOneBQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (691, 1), (6154649, 1), (299053301018337713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (691, 1), (6154649, 1), (299053301018337713, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyOneBQ_2
      · exact prime_seventyOneBQ_3
      · exact prime_seventyOneBQ_11
      · exact prime_seventyOneBQ_691
      · exact prime_seventyOneBQ_6154649
      · exact prime_seventyOneBQ_299053301018337713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 83940948771300385393306673623) ^ 41970474385650192696653336811 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 83940948771300385393306673623) ^ 27980316257100128464435557874 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 83940948771300385393306673623) ^ 7630995342845489581209697602 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 83940948771300385393306673623) ^ 121477494603907938340530642 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 83940948771300385393306673623) ^ 13638624846242309739078 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide
    · change (3 : ZMod 83940948771300385393306673623) ^ 280688922294 ≠ 1
      rw [← seventyOneBQFastPow_eq_pow]
      decide

private theorem phi_seventyOneBQ_83940948771300385393306673600 : Nat.totient 83940948771300385393306673600 = 30522993013571462842613760000 := by
  rw [← show ((([(2, 6), (5, 2), (11, 1), (46853, 1), (140111, 1), (256471, 1), (2832782977, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673600 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_5, prime_seventyOneBQ_11, prime_seventyOneBQ_46853, prime_seventyOneBQ_140111, prime_seventyOneBQ_256471, prime_seventyOneBQ_2832782977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673601 : Nat.totient 83940948771300385393306673601 = 53267656544452915109448876000 := by
  rw [← show ((([(3, 4), (31, 1), (61, 1), (548021157864741924994331, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673601 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_3, prime_seventyOneBQ_31, prime_seventyOneBQ_61, prime_seventyOneBQ_548021157864741924994331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673602 : Nat.totient 83940948771300385393306673602 = 41787196189315448916302467200 := by
  rw [← show ((([(2, 1), (229, 1), (41144869, 1), (4454435879316161801, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673602 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_229, prime_seventyOneBQ_41144869, prime_seventyOneBQ_4454435879316161801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673603 : Nat.totient 83940948771300385393306673603 = 81436869649962375539511953376 := by
  rw [← show ((([(37, 1), (347, 1), (2140543, 1), (3054349413592297339, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673603 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_37, prime_seventyOneBQ_347, prime_seventyOneBQ_2140543, prime_seventyOneBQ_3054349413592297339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673604 : Nat.totient 83940948771300385393306673604 = 22572355938161614303391834112 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (17, 1), (664816237, 1), (88418684350987889, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673604 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_3, prime_seventyOneBQ_7, prime_seventyOneBQ_17, prime_seventyOneBQ_664816237, prime_seventyOneBQ_88418684350987889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673605 : Nat.totient 83940948771300385393306673605 = 67071754482640983455399683776 := by
  rw [← show ((([(5, 1), (829, 1), (20251133599831214811412949, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673605 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_5, prime_seventyOneBQ_829, prime_seventyOneBQ_20251133599831214811412949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673606 : Nat.totient 83940948771300385393306673606 = 38195776263121315664622612480 := by
  rw [← show ((([(2, 1), (13, 1), (71, 1), (70937, 1), (641016722369481874753, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673606 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_13, prime_seventyOneBQ_71, prime_seventyOneBQ_70937, prime_seventyOneBQ_641016722369481874753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673607 : Nat.totient 83940948771300385393306673607 = 55943258826573861900478576640 := by
  rw [← show ((([(3, 1), (3221, 1), (11754154457, 1), (739044349401377, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673607 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_3, prime_seventyOneBQ_3221, prime_seventyOneBQ_11754154457, prime_seventyOneBQ_739044349401377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673608 : Nat.totient 83940948771300385393306673608 = 41970474385650192696653336800 := by
  rw [← show ((([(2, 3), (10492618596412548174163334201, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673608 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_10492618596412548174163334201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673609 : Nat.totient 83940948771300385393306673609 = 83940948771300385393306673608 := by
  rw [← show ((([(83940948771300385393306673609, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673609 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_83940948771300385393306673609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673610 : Nat.totient 83940948771300385393306673610 = 22232676224662957724645311488 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (163, 1), (1567, 1), (420037, 1), (8693351008977577, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673610 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_3, prime_seventyOneBQ_5, prime_seventyOneBQ_163, prime_seventyOneBQ_1567, prime_seventyOneBQ_420037, prime_seventyOneBQ_8693351008977577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673611 : Nat.totient 83940948771300385393306673611 = 60454611922047524281727251200 := by
  rw [← show ((([(7, 1), (11, 1), (19, 1), (41, 1), (1399412313010359358373317, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673611 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_7, prime_seventyOneBQ_11, prime_seventyOneBQ_19, prime_seventyOneBQ_41, prime_seventyOneBQ_1399412313010359358373317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673612 : Nat.totient 83940948771300385393306673612 = 41920411283660350959012642816 := by
  rw [← show ((([(2, 2), (839, 1), (1083253, 1), (23089898352556075009, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673612 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_839, prime_seventyOneBQ_1083253, prime_seventyOneBQ_23089898352556075009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673613 : Nat.totient 83940948771300385393306673613 = 55500400013638768286151352320 := by
  rw [← show ((([(3, 1), (127, 1), (2833, 1), (77768249503462089002881, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673613 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_3, prime_seventyOneBQ_127, prime_seventyOneBQ_2833, prime_seventyOneBQ_77768249503462089002881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673614 : Nat.totient 83940948771300385393306673614 = 41970241108781494073439693720 := by
  rw [← show ((([(2, 1), (179917, 1), (233276868698623213463171, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673614 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_179917, prime_seventyOneBQ_233276868698623213463171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673615 : Nat.totient 83940948771300385393306673615 = 66150171753811359584605324320 := by
  rw [← show ((([(5, 1), (67, 1), (215279, 1), (1163931439351910573711, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673615 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_5, prime_seventyOneBQ_67, prime_seventyOneBQ_215279, prime_seventyOneBQ_1163931439351910573711]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673616 : Nat.totient 83940948771300385393306673616 = 27973368078243138117163470720 := by
  rw [← show ((([(2, 4), (3, 1), (4027, 1), (434261178561896704501421, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673616 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_3, prime_seventyOneBQ_4027, prime_seventyOneBQ_434261178561896704501421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673617 : Nat.totient 83940948771300385393306673617 = 83940948771300385393306673616 := by
  rw [← show ((([(83940948771300385393306673617, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673617 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_83940948771300385393306673617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673618 : Nat.totient 83940948771300385393306673618 = 35974689016302402621967223424 := by
  rw [← show ((([(2, 1), (7, 1), (16023107, 1), (33650269, 1), (11120147934089, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673618 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_7, prime_seventyOneBQ_16023107, prime_seventyOneBQ_33650269, prime_seventyOneBQ_11120147934089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673619 : Nat.totient 83940948771300385393306673619 = 50497546075470597559727232000 := by
  rw [← show ((([(3, 2), (13, 1), (47, 1), (1171, 1), (3121, 1), (4176759703545045091, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673619 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_3, prime_seventyOneBQ_13, prime_seventyOneBQ_47, prime_seventyOneBQ_1171, prime_seventyOneBQ_3121, prime_seventyOneBQ_4176759703545045091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673620 : Nat.totient 83940948771300385393306673620 = 33230231095784001096939678720 := by
  rw [← show ((([(2, 2), (5, 1), (97, 1), (195035671, 1), (221849316448808663, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673620 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_5, prime_seventyOneBQ_97, prime_seventyOneBQ_195035671, prime_seventyOneBQ_221849316448808663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673621 : Nat.totient 83940948771300385393306673621 = 73773426730586061453423820800 := by
  rw [← show ((([(17, 1), (23, 1), (79, 1), (89, 1), (35892330281, 1), (850703780621, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673621 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_17, prime_seventyOneBQ_23, prime_seventyOneBQ_79, prime_seventyOneBQ_89, prime_seventyOneBQ_35892330281, prime_seventyOneBQ_850703780621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673622 : Nat.totient 83940948771300385393306673622 = 25399835653881560242298188800 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (691, 1), (6154649, 1), (299053301018337713, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673622 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_3, prime_seventyOneBQ_11, prime_seventyOneBQ_691, prime_seventyOneBQ_6154649, prime_seventyOneBQ_299053301018337713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673623 : Nat.totient 83940948771300385393306673623 = 83940948771300385393306673622 := by
  rw [← show ((([(83940948771300385393306673623, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673623 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_83940948771300385393306673623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673624 : Nat.totient 83940948771300385393306673624 = 41965435308403746521518635072 := by
  rw [← show ((([(2, 3), (8329, 1), (1259769311611543783667107, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673624 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_8329, prime_seventyOneBQ_1259769311611543783667107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673625 : Nat.totient 83940948771300385393306673625 = 37648986187451170160232364800 := by
  rw [← show ((([(3, 1), (5, 3), (7, 1), (53, 1), (603349137619409778208853, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673625 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_3, prime_seventyOneBQ_5, prime_seventyOneBQ_7, prime_seventyOneBQ_53, prime_seventyOneBQ_603349137619409778208853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673626 : Nat.totient 83940948771300385393306673626 = 41970297092470315277839203600 := by
  rw [← show ((([(2, 1), (236891, 1), (346614571, 1), (511150160025733, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673626 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_236891, prime_seventyOneBQ_346614571, prime_seventyOneBQ_511150160025733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673627 : Nat.totient 83940948771300385393306673627 = 83328241116035419076567208720 := by
  rw [← show ((([(137, 1), (612707655264966316739464771, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673627 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_137, prime_seventyOneBQ_612707655264966316739464771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673628 : Nat.totient 83940948771300385393306673628 = 26385312616768210898205100800 := by
  rw [← show ((([(2, 2), (3, 3), (29, 1), (43, 1), (13901, 1), (44837110952000662903, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673628 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_3, prime_seventyOneBQ_29, prime_seventyOneBQ_43, prime_seventyOneBQ_13901, prime_seventyOneBQ_44837110952000662903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673629 : Nat.totient 83940948771300385393306673629 = 83611677208548526175744640000 := by
  rw [← show ((([(271, 1), (4283, 1), (1666704353, 1), (43390828113001, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673629 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_271, prime_seventyOneBQ_4283, prime_seventyOneBQ_1666704353, prime_seventyOneBQ_43390828113001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673630 : Nat.totient 83940948771300385393306673630 = 31809201639650672359568844672 := by
  rw [← show ((([(2, 1), (5, 1), (19, 1), (441794467217370449438456177, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673630 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_5, prime_seventyOneBQ_19, prime_seventyOneBQ_441794467217370449438456177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673631 : Nat.totient 83940948771300385393306673631 = 55941312937082905458717081600 := by
  rw [← show ((([(3, 1), (2897, 1), (19806181, 1), (487644556012159361, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673631 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_3, prime_seventyOneBQ_2897, prime_seventyOneBQ_19806181, prime_seventyOneBQ_487644556012159361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673632 : Nat.totient 83940948771300385393306673632 = 31807503501548556170188800000 := by
  rw [← show ((([(2, 5), (7, 2), (13, 1), (31, 2), (131, 1), (383, 1), (270601, 1), (315617887391, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673632 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_7, prime_seventyOneBQ_13, prime_seventyOneBQ_31, prime_seventyOneBQ_131, prime_seventyOneBQ_383, prime_seventyOneBQ_270601, prime_seventyOneBQ_315617887391]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673633 : Nat.totient 83940948771300385393306673633 = 74112750322854978656820003840 := by
  rw [← show ((([(11, 1), (59, 1), (83, 1), (2077326913, 1), (750146758239523, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673633 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_11, prime_seventyOneBQ_59, prime_seventyOneBQ_83, prime_seventyOneBQ_2077326913, prime_seventyOneBQ_750146758239523]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673634 : Nat.totient 83940948771300385393306673634 = 27980316257100128464435557876 := by
  rw [← show ((([(2, 1), (3, 1), (13990158128550064232217778939, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673634 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_3, prime_seventyOneBQ_13990158128550064232217778939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673635 : Nat.totient 83940948771300385393306673635 = 66646689452570254197630640000 := by
  rw [← show ((([(5, 1), (167, 1), (1151, 1), (1451, 1), (171287423, 1), (351414102947, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673635 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_5, prime_seventyOneBQ_167, prime_seventyOneBQ_1151, prime_seventyOneBQ_1451, prime_seventyOneBQ_171287423, prime_seventyOneBQ_351414102947]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673636 : Nat.totient 83940948771300385393306673636 = 41970474385649612946935007432 := by
  rw [← show ((([(2, 2), (140287558496747, 1), (149587300667947, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673636 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_140287558496747, prime_seventyOneBQ_149587300667947]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673637 : Nat.totient 83940948771300385393306673637 = 55959900030344075397642017280 := by
  rw [← show ((([(3, 2), (80761, 1), (1414297, 1), (81656179461256429, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673637 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_3, prime_seventyOneBQ_80761, prime_seventyOneBQ_1414297, prime_seventyOneBQ_81656179461256429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673638 : Nat.totient 83940948771300385393306673638 = 39500511200251680047734862080 := by
  rw [← show ((([(2, 1), (17, 1), (35531, 1), (69484434281332113790697, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673638 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_17, prime_seventyOneBQ_35531, prime_seventyOneBQ_69484434281332113790697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673639 : Nat.totient 83940948771300385393306673639 = 71198858643155946455064228000 := by
  rw [← show ((([(7, 1), (101, 1), (1867, 1), (63593121331864903943431, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673639 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_7, prime_seventyOneBQ_101, prime_seventyOneBQ_1867, prime_seventyOneBQ_63593121331864903943431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673640 : Nat.totient 83940948771300385393306673640 = 21779273194715775669614703360 := by
  rw [← show ((([(2, 3), (3, 1), (5, 1), (37, 1), (18905619092635221935429431, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673640 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_3, prime_seventyOneBQ_5, prime_seventyOneBQ_37, prime_seventyOneBQ_18905619092635221935429431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673641 : Nat.totient 83940948771300385393306673641 = 83708908390920030715022944320 := by
  rw [← show ((([(367, 1), (33629, 1), (100957, 1), (67368584044417391, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673641 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_367, prime_seventyOneBQ_33629, prime_seventyOneBQ_100957, prime_seventyOneBQ_67368584044417391]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673642 : Nat.totient 83940948771300385393306673642 = 41970474066285933709217560000 := by
  rw [← show ((([(2, 1), (131418821, 1), (319364258987304358001, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673642 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_131418821, prime_seventyOneBQ_319364258987304358001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673643 : Nat.totient 83940948771300385393306673643 = 55960603333125092970009617664 := by
  rw [← show ((([(3, 1), (3688453, 1), (3994553, 1), (1899066519837709, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673643 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_3, prime_seventyOneBQ_3688453, prime_seventyOneBQ_3994553, prime_seventyOneBQ_1899066519837709]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673644 : Nat.totient 83940948771300385393306673644 = 36496064683174080605785500160 := by
  rw [← show ((([(2, 2), (11, 1), (23, 2), (3606330502289928913615169, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673644 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_11, prime_seventyOneBQ_23, prime_seventyOneBQ_3606330502289928913615169]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673645 : Nat.totient 83940948771300385393306673645 = 61986965983457225558529692160 := by
  rw [← show ((([(5, 1), (13, 1), (315961, 1), (4087210800909478623253, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673645 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_5, prime_seventyOneBQ_13, prime_seventyOneBQ_315961, prime_seventyOneBQ_4087210800909478623253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673646 : Nat.totient 83940948771300385393306673646 = 23899432313026521452549376000 := by
  rw [← show ((([(2, 1), (3, 2), (7, 1), (571, 1), (587, 1), (26317, 1), (166906601, 1), (452500669, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673646 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_3, prime_seventyOneBQ_7, prime_seventyOneBQ_571, prime_seventyOneBQ_587, prime_seventyOneBQ_26317, prime_seventyOneBQ_166906601, prime_seventyOneBQ_452500669]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673647 : Nat.totient 83940948771300385393306673647 = 82766772475216359995220642432 := by
  rw [← show ((([(73, 1), (3407, 1), (337503965531481862053977, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673647 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_73, prime_seventyOneBQ_3407, prime_seventyOneBQ_337503965531481862053977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673648 : Nat.totient 83940948771300385393306673648 = 41970474280301629839203611584 := by
  rw [← show ((([(2, 4), (398396269, 1), (13168570356782819387, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673648 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_398396269, prime_seventyOneBQ_13168570356782819387]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673649 : Nat.totient 83940948771300385393306673649 = 52633924486364974802351725440 := by
  rw [← show ((([(3, 1), (19, 1), (139, 1), (8375491, 1), (1264951695367459993, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673649 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_3, prime_seventyOneBQ_19, prime_seventyOneBQ_139, prime_seventyOneBQ_8375491, prime_seventyOneBQ_1264951695367459993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673650 : Nat.totient 83940948771300385393306673650 = 33576379508060229928047855360 := by
  rw [← show ((([(2, 1), (5, 2), (73004386297, 1), (22996138459354409, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673650 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_5, prime_seventyOneBQ_73004386297, prime_seventyOneBQ_22996138459354409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673651 : Nat.totient 83940948771300385393306673651 = 83147424011587809327491726848 := by
  rw [← show ((([(107, 1), (9209, 1), (85187843232697376898977, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673651 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_107, prime_seventyOneBQ_9209, prime_seventyOneBQ_85187843232697376898977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673652 : Nat.totient 83940948771300385393306673652 = 27251962414779226501852446720 := by
  rw [← show ((([(2, 2), (3, 1), (41, 1), (1103, 1), (1289, 1), (119999749955170557793, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673652 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_3, prime_seventyOneBQ_41, prime_seventyOneBQ_1103, prime_seventyOneBQ_1289, prime_seventyOneBQ_119999749955170557793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673653 : Nat.totient 83940948771300385393306673653 = 71949381606259579349823777360 := by
  rw [← show ((([(7, 1), (23552471, 1), (509142506116906771349, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673653 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_7, prime_seventyOneBQ_23552471, prime_seventyOneBQ_509142506116906771349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673654 : Nat.totient 83940948771300385393306673654 = 41968537729324983647753722560 := by
  rw [← show ((([(2, 1), (41227, 1), (45691, 1), (584490169, 1), (38120121019, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673654 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_41227, prime_seventyOneBQ_45691, prime_seventyOneBQ_584490169, prime_seventyOneBQ_38120121019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673655 : Nat.totient 83940948771300385393306673655 = 38304596604286270391389562880 := by
  rw [← show ((([(3, 3), (5, 1), (11, 1), (17, 1), (5128063, 1), (648403195703662813, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673655 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_3, prime_seventyOneBQ_5, prime_seventyOneBQ_11, prime_seventyOneBQ_17, prime_seventyOneBQ_5128063, prime_seventyOneBQ_648403195703662813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673656 : Nat.totient 83940948771300385393306673656 = 41970474385650192696653336824 := by
  rw [← show ((([(2, 3), (10492618596412548174163334207, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673656 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_10492618596412548174163334207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673657 : Nat.totient 83940948771300385393306673657 = 80523461245407891020350709760 := by
  rw [← show ((([(29, 1), (239, 1), (439, 1), (3649153, 1), (7559992800768341, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673657 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_29, prime_seventyOneBQ_239, prime_seventyOneBQ_439, prime_seventyOneBQ_3649153, prime_seventyOneBQ_7559992800768341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673658 : Nat.totient 83940948771300385393306673658 = 25826777152954483854670142400 := by
  rw [← show ((([(2, 1), (3, 1), (13, 2), (21397, 1), (3868860156127086397451, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673658 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_3, prime_seventyOneBQ_13, prime_seventyOneBQ_21397, prime_seventyOneBQ_3868860156127086397451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673659 : Nat.totient 83940948771300385393306673659 = 83940948666856761738844320000 := by
  rw [← show ((([(803696251, 1), (104443623653658657409, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673659 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_803696251, prime_seventyOneBQ_104443623653658657409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673660 : Nat.totient 83940948771300385393306673660 = 28629074524123634636713236480 := by
  rw [← show ((([(2, 2), (5, 1), (7, 1), (191, 1), (39905635883, 1), (78664400127073, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673660 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_5, prime_seventyOneBQ_7, prime_seventyOneBQ_191, prime_seventyOneBQ_39905635883, prime_seventyOneBQ_78664400127073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673661 : Nat.totient 83940948771300385393306673661 = 55897878273377960126777062320 := by
  rw [← show ((([(3, 1), (911, 1), (42139, 1), (728869901998847848003, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673661 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_3, prime_seventyOneBQ_911, prime_seventyOneBQ_42139, prime_seventyOneBQ_728869901998847848003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673662 : Nat.totient 83940948771300385393306673662 = 41282433821951009209822954200 := by
  rw [← show ((([(2, 1), (61, 1), (688040563699183486830382571, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673662 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_61, prime_seventyOneBQ_688040563699183486830382571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673663 : Nat.totient 83940948771300385393306673663 = 81087030833968098311264593920 := by
  rw [← show ((([(31, 1), (877, 1), (1559, 1), (55817, 1), (4075609, 1), (8705775587, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673663 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_31, prime_seventyOneBQ_877, prime_seventyOneBQ_1559, prime_seventyOneBQ_55817, prime_seventyOneBQ_4075609, prime_seventyOneBQ_8705775587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673664 : Nat.totient 83940948771300385393306673664 = 27972772359484302061500653568 := by
  rw [← show ((([(2, 9), (3, 2), (3709, 1), (4911391676970314407037, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673664 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_3, prime_seventyOneBQ_3709, prime_seventyOneBQ_4911391676970314407037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673665 : Nat.totient 83940948771300385393306673665 = 66582403015510708344987623424 := by
  rw [← show ((([(5, 1), (223, 1), (269, 1), (3217, 1), (6361720793, 1), (13674802439, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673665 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_5, prime_seventyOneBQ_223, prime_seventyOneBQ_269, prime_seventyOneBQ_3217, prime_seventyOneBQ_6361720793, prime_seventyOneBQ_13674802439]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673666 : Nat.totient 83940948771300385393306673666 = 37039417363197990234937800000 := by
  rw [← show ((([(2, 1), (11, 1), (47, 1), (151, 1), (659, 1), (239831, 1), (3401618891086831, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673666 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_11, prime_seventyOneBQ_47, prime_seventyOneBQ_151, prime_seventyOneBQ_659, prime_seventyOneBQ_239831, prime_seventyOneBQ_3401618891086831]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673667 : Nat.totient 83940948771300385393306673667 = 45880767030275987047273212672 := by
  rw [← show ((([(3, 1), (7, 1), (23, 1), (173790784205590860027550049, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673667 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_3, prime_seventyOneBQ_7, prime_seventyOneBQ_23, prime_seventyOneBQ_173790784205590860027550049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673668 : Nat.totient 83940948771300385393306673668 = 39761502049504635253688850048 := by
  rw [← show ((([(2, 2), (19, 1), (677589608939, 1), (1630022292952337, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673668 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_19, prime_seventyOneBQ_677589608939, prime_seventyOneBQ_1630022292952337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673669 : Nat.totient 83940948771300385393306673669 = 83851208750584735360998020352 := by
  rw [← show ((([(937, 1), (544963, 1), (61476887, 1), (2673963025177, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673669 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_937, prime_seventyOneBQ_544963, prime_seventyOneBQ_61476887, prime_seventyOneBQ_2673963025177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673670 : Nat.totient 83940948771300385393306673670 = 22382613013519088770319562240 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (13649, 1), (204999020126750153596861, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673670 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_3, prime_seventyOneBQ_5, prime_seventyOneBQ_13649, prime_seventyOneBQ_204999020126750153596861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673671 : Nat.totient 83940948771300385393306673671 = 75531539090071975686452532576 := by
  rw [← show ((([(13, 1), (43, 1), (503, 1), (298534192950705019945823, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673671 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_13, prime_seventyOneBQ_43, prime_seventyOneBQ_503, prime_seventyOneBQ_298534192950705019945823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673672 : Nat.totient 83940948771300385393306673672 = 39392401583270298385760256000 := by
  rw [← show ((([(2, 3), (17, 1), (1061, 1), (1109, 1), (1543, 1), (3631, 1), (93625868694881, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673672 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_17, prime_seventyOneBQ_1061, prime_seventyOneBQ_1109, prime_seventyOneBQ_1543, prime_seventyOneBQ_3631, prime_seventyOneBQ_93625868694881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673673 : Nat.totient 83940948771300385393306673673 = 55839766736313714116414944800 := by
  rw [← show ((([(3, 2), (463, 1), (116120051, 1), (173477500176250069, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673673 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_3, prime_seventyOneBQ_463, prime_seventyOneBQ_116120051, prime_seventyOneBQ_173477500176250069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673674 : Nat.totient 83940948771300385393306673674 = 35974692330557308025702860140 := by
  rw [← show ((([(2, 1), (7, 1), (5995782055092884670950476691, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673674 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_7, prime_seventyOneBQ_5995782055092884670950476691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673675 : Nat.totient 83940948771300385393306673675 = 67037849401485300444635356800 := by
  rw [← show ((([(5, 2), (823, 1), (2027, 1), (299359, 1), (61298071, 1), (109683463, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673675 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_5, prime_seventyOneBQ_823, prime_seventyOneBQ_2027, prime_seventyOneBQ_299359, prime_seventyOneBQ_61298071, prime_seventyOneBQ_109683463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673676 : Nat.totient 83940948771300385393306673676 = 27889175161800128045984626512 := by
  rw [← show ((([(2, 2), (3, 1), (307, 1), (22785273825000104612732539, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673676 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_3, prime_seventyOneBQ_307, prime_seventyOneBQ_22785273825000104612732539]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673677 : Nat.totient 83940948771300385393306673677 = 72490802757566310763527168000 := by
  rw [← show ((([(11, 1), (37, 1), (71, 1), (103, 1), (431693, 1), (630871, 1), (103554343649, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673677 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_11, prime_seventyOneBQ_37, prime_seventyOneBQ_71, prime_seventyOneBQ_103, prime_seventyOneBQ_431693, prime_seventyOneBQ_630871, prime_seventyOneBQ_103554343649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673678 : Nat.totient 83940948771300385393306673678 = 41178578640330842863377534816 := by
  rw [← show ((([(2, 1), (53, 1), (18769805189, 1), (42189875448977167, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673678 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_53, prime_seventyOneBQ_18769805189, prime_seventyOneBQ_42189875448977167]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673679 : Nat.totient 83940948771300385393306673679 = 55917816096426872003499076832 := by
  rw [← show ((([(3, 1), (1307, 1), (171755357, 1), (124642668952483307, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673679 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_3, prime_seventyOneBQ_1307, prime_seventyOneBQ_171755357, prime_seventyOneBQ_124642668952483307]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673680 : Nat.totient 83940948771300385393306673680 = 33575655736172237206178935296 := by
  rw [← show ((([(2, 4), (5, 1), (46747, 1), (6088139, 1), (3686766071755237, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673680 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_5, prime_seventyOneBQ_46747, prime_seventyOneBQ_6088139, prime_seventyOneBQ_3686766071755237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673681 : Nat.totient 83940948771300385393306673681 = 71949384661114616051405720256 := by
  rw [← show ((([(7, 2), (1713080587169395620271564769, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673681 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_7, prime_seventyOneBQ_1713080587169395620271564769]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673682 : Nat.totient 83940948771300385393306673682 = 27562697999760023998798047840 := by
  rw [← show ((([(2, 1), (3, 6), (67, 1), (17261357, 1), (49781343392296391, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673682 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_3, prime_seventyOneBQ_67, prime_seventyOneBQ_17261357, prime_seventyOneBQ_49781343392296391]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673683 : Nat.totient 83940948771300385393306673683 = 82930864566562381938393538560 := by
  rw [← show ((([(113, 2), (449, 1), (1013, 1), (14453106416033349511, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673683 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_113, prime_seventyOneBQ_449, prime_seventyOneBQ_1013, prime_seventyOneBQ_14453106416033349511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673684 : Nat.totient 83940948771300385393306673684 = 38741976355984793258449233984 := by
  rw [← show ((([(2, 2), (13, 1), (1614249014832699719102051417, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673684 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_13, prime_seventyOneBQ_1614249014832699719102051417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673685 : Nat.totient 83940948771300385393306673685 = 44768503738458694347751065600 := by
  rw [← show ((([(3, 1), (5, 1), (19747891, 1), (10593489961, 1), (26749941329, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673685 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_3, prime_seventyOneBQ_5, prime_seventyOneBQ_19747891, prime_seventyOneBQ_10593489961, prime_seventyOneBQ_26749941329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673686 : Nat.totient 83940948771300385393306673686 = 40354888456868238490765248000 := by
  rw [← show ((([(2, 1), (29, 2), (241, 1), (221653, 1), (934237349796078551, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673686 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_29, prime_seventyOneBQ_241, prime_seventyOneBQ_221653, prime_seventyOneBQ_934237349796078551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673687 : Nat.totient 83940948771300385393306673687 = 79494302829365766873508320000 := by
  rw [← show ((([(19, 1), (3929, 1), (9397, 1), (97244171, 1), (1230510825251, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673687 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_19, prime_seventyOneBQ_3929, prime_seventyOneBQ_9397, prime_seventyOneBQ_97244171, prime_seventyOneBQ_1230510825251]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673688 : Nat.totient 83940948771300385393306673688 = 21744874469655299843492198400 := by
  rw [← show ((([(2, 3), (3, 1), (7, 1), (11, 2), (389, 1), (11321, 1), (937658791445374459, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673688 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_3, prime_seventyOneBQ_7, prime_seventyOneBQ_11, prime_seventyOneBQ_389, prime_seventyOneBQ_11321, prime_seventyOneBQ_937658791445374459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673689 : Nat.totient 83940948771300385393306673689 = 78864400127527954352772765696 := by
  rw [← show ((([(17, 1), (569, 1), (8677860929525523146211793, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673689 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_17, prime_seventyOneBQ_569, prime_seventyOneBQ_8677860929525523146211793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673690 : Nat.totient 83940948771300385393306673690 = 32000589257486661866850512640 := by
  rw [← show ((([(2, 1), (5, 1), (23, 1), (277, 1), (9176861, 1), (143572781748184799, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673690 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_5, prime_seventyOneBQ_23, prime_seventyOneBQ_277, prime_seventyOneBQ_9176861, prime_seventyOneBQ_143572781748184799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673691 : Nat.totient 83940948771300385393306673691 = 55960609812864067894801489440 := by
  rw [← show ((([(3, 2), (2465081, 1), (3783556031505675805979, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673691 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_3, prime_seventyOneBQ_2465081, prime_seventyOneBQ_3783556031505675805979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673692 : Nat.totient 83940948771300385393306673692 = 41259110413012053837388025936 := by
  rw [← show ((([(2, 2), (59, 1), (355681986319069429632655397, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673692 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_59, prime_seventyOneBQ_355681986319069429632655397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673693 : Nat.totient 83940948771300385393306673693 = 81893608557342983337052055520 := by
  rw [← show ((([(41, 1), (3544481901619, 1), (577613391959767, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673693 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_41, prime_seventyOneBQ_3544481901619, prime_seventyOneBQ_577613391959767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673694 : Nat.totient 83940948771300385393306673694 = 27034802365593832829093491200 := by
  rw [← show ((([(2, 1), (3, 1), (31, 1), (631, 1), (2540173, 1), (281558261325688433, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673694 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_3, prime_seventyOneBQ_31, prime_seventyOneBQ_631, prime_seventyOneBQ_2540173, prime_seventyOneBQ_281558261325688433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673695 : Nat.totient 83940948771300385393306673695 = 57537037284583523210221265280 := by
  rw [← show ((([(5, 1), (7, 1), (3109, 1), (14543, 1), (53043369375128958271, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673695 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_5, prime_seventyOneBQ_7, prime_seventyOneBQ_3109, prime_seventyOneBQ_14543, prime_seventyOneBQ_53043369375128958271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673696 : Nat.totient 83940948771300385393306673696 = 41958375661411031499565747968 := by
  rw [← show ((([(2, 5), (3469, 1), (756170264947574817970837, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673696 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_3469, prime_seventyOneBQ_756170264947574817970837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673697 : Nat.totient 83940948771300385393306673697 = 51648897813597803037669364224 := by
  rw [← show ((([(3, 1), (13, 1), (9059, 1), (37897, 1), (9259267, 1), (677091820903, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673697 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_3, prime_seventyOneBQ_13, prime_seventyOneBQ_9059, prime_seventyOneBQ_37897, prime_seventyOneBQ_9259267, prime_seventyOneBQ_677091820903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673698 : Nat.totient 83940948771300385393306673698 = 41316402318757824954999437568 := by
  rw [← show ((([(2, 1), (109, 1), (173, 1), (1499, 1), (45767, 1), (259627, 1), (124958943127, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673698 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_109, prime_seventyOneBQ_173, prime_seventyOneBQ_1499, prime_seventyOneBQ_45767, prime_seventyOneBQ_259627, prime_seventyOneBQ_124958943127]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673699 : Nat.totient 83940948771300385393306673699 = 76307948911566391914021728800 := by
  rw [← show ((([(11, 1), (38069, 1), (200451688850389807486661, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673699 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_11, prime_seventyOneBQ_38069, prime_seventyOneBQ_200451688850389807486661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673700 : Nat.totient 83940948771300385393306673700 = 22100752207470096200782609920 := by
  rw [← show ((([(2, 2), (3, 2), (5, 2), (79, 1), (141833, 1), (8323902487298569999, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673700 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_2, prime_seventyOneBQ_3, prime_seventyOneBQ_5, prime_seventyOneBQ_79, prime_seventyOneBQ_141833, prime_seventyOneBQ_8323902487298569999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyOneBQ_83940948771300385393306673701 : Nat.totient 83940948771300385393306673701 = 83938209378217770654502599168 := by
  rw [← show ((([(30829, 1), (5133127, 1), (489120383, 1), (1084467809, 1)] : List FactorBlock).map factorBlockValue).prod) = 83940948771300385393306673701 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyOneBQ_30829, prime_seventyOneBQ_5133127, prime_seventyOneBQ_489120383, prime_seventyOneBQ_1084467809]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64SeventyOneBQ : certifiedKill 1 83940948771300385393306673599 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_seventyOneBQ_83940948771300385393306673600, phi_seventyOneBQ_83940948771300385393306673601, phi_seventyOneBQ_83940948771300385393306673602,
    phi_seventyOneBQ_83940948771300385393306673603, phi_seventyOneBQ_83940948771300385393306673604, phi_seventyOneBQ_83940948771300385393306673605,
    phi_seventyOneBQ_83940948771300385393306673606, phi_seventyOneBQ_83940948771300385393306673607, phi_seventyOneBQ_83940948771300385393306673608,
    phi_seventyOneBQ_83940948771300385393306673609, phi_seventyOneBQ_83940948771300385393306673610, phi_seventyOneBQ_83940948771300385393306673611,
    phi_seventyOneBQ_83940948771300385393306673612, phi_seventyOneBQ_83940948771300385393306673613, phi_seventyOneBQ_83940948771300385393306673614,
    phi_seventyOneBQ_83940948771300385393306673615, phi_seventyOneBQ_83940948771300385393306673616, phi_seventyOneBQ_83940948771300385393306673617,
    phi_seventyOneBQ_83940948771300385393306673618, phi_seventyOneBQ_83940948771300385393306673619, phi_seventyOneBQ_83940948771300385393306673620,
    phi_seventyOneBQ_83940948771300385393306673621, phi_seventyOneBQ_83940948771300385393306673622, phi_seventyOneBQ_83940948771300385393306673623,
    phi_seventyOneBQ_83940948771300385393306673624, phi_seventyOneBQ_83940948771300385393306673625, phi_seventyOneBQ_83940948771300385393306673626,
    phi_seventyOneBQ_83940948771300385393306673627, phi_seventyOneBQ_83940948771300385393306673628, phi_seventyOneBQ_83940948771300385393306673629,
    phi_seventyOneBQ_83940948771300385393306673630, phi_seventyOneBQ_83940948771300385393306673631, phi_seventyOneBQ_83940948771300385393306673632,
    phi_seventyOneBQ_83940948771300385393306673633, phi_seventyOneBQ_83940948771300385393306673634, phi_seventyOneBQ_83940948771300385393306673635,
    phi_seventyOneBQ_83940948771300385393306673636, phi_seventyOneBQ_83940948771300385393306673637, phi_seventyOneBQ_83940948771300385393306673638,
    phi_seventyOneBQ_83940948771300385393306673639, phi_seventyOneBQ_83940948771300385393306673640, phi_seventyOneBQ_83940948771300385393306673641,
    phi_seventyOneBQ_83940948771300385393306673642, phi_seventyOneBQ_83940948771300385393306673643, phi_seventyOneBQ_83940948771300385393306673644,
    phi_seventyOneBQ_83940948771300385393306673645, phi_seventyOneBQ_83940948771300385393306673646, phi_seventyOneBQ_83940948771300385393306673647,
    phi_seventyOneBQ_83940948771300385393306673648, phi_seventyOneBQ_83940948771300385393306673649, phi_seventyOneBQ_83940948771300385393306673650,
    phi_seventyOneBQ_83940948771300385393306673651, phi_seventyOneBQ_83940948771300385393306673652, phi_seventyOneBQ_83940948771300385393306673653,
    phi_seventyOneBQ_83940948771300385393306673654, phi_seventyOneBQ_83940948771300385393306673655, phi_seventyOneBQ_83940948771300385393306673656,
    phi_seventyOneBQ_83940948771300385393306673657, phi_seventyOneBQ_83940948771300385393306673658, phi_seventyOneBQ_83940948771300385393306673659,
    phi_seventyOneBQ_83940948771300385393306673660, phi_seventyOneBQ_83940948771300385393306673661, phi_seventyOneBQ_83940948771300385393306673662,
    phi_seventyOneBQ_83940948771300385393306673663, phi_seventyOneBQ_83940948771300385393306673664, phi_seventyOneBQ_83940948771300385393306673665,
    phi_seventyOneBQ_83940948771300385393306673666, phi_seventyOneBQ_83940948771300385393306673667, phi_seventyOneBQ_83940948771300385393306673668,
    phi_seventyOneBQ_83940948771300385393306673669, phi_seventyOneBQ_83940948771300385393306673670, phi_seventyOneBQ_83940948771300385393306673671,
    phi_seventyOneBQ_83940948771300385393306673672, phi_seventyOneBQ_83940948771300385393306673673, phi_seventyOneBQ_83940948771300385393306673674,
    phi_seventyOneBQ_83940948771300385393306673675, phi_seventyOneBQ_83940948771300385393306673676, phi_seventyOneBQ_83940948771300385393306673677,
    phi_seventyOneBQ_83940948771300385393306673678, phi_seventyOneBQ_83940948771300385393306673679, phi_seventyOneBQ_83940948771300385393306673680,
    phi_seventyOneBQ_83940948771300385393306673681, phi_seventyOneBQ_83940948771300385393306673682, phi_seventyOneBQ_83940948771300385393306673683,
    phi_seventyOneBQ_83940948771300385393306673684, phi_seventyOneBQ_83940948771300385393306673685, phi_seventyOneBQ_83940948771300385393306673686,
    phi_seventyOneBQ_83940948771300385393306673687, phi_seventyOneBQ_83940948771300385393306673688, phi_seventyOneBQ_83940948771300385393306673689,
    phi_seventyOneBQ_83940948771300385393306673690, phi_seventyOneBQ_83940948771300385393306673691, phi_seventyOneBQ_83940948771300385393306673692,
    phi_seventyOneBQ_83940948771300385393306673693, phi_seventyOneBQ_83940948771300385393306673694, phi_seventyOneBQ_83940948771300385393306673695,
    phi_seventyOneBQ_83940948771300385393306673696, phi_seventyOneBQ_83940948771300385393306673697, phi_seventyOneBQ_83940948771300385393306673698,
    phi_seventyOneBQ_83940948771300385393306673699, phi_seventyOneBQ_83940948771300385393306673700, phi_seventyOneBQ_83940948771300385393306673701]

end TotientTailPeriodKiller
end Erdos249257
