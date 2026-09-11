import Erdos249257.DiagonalPincerCertificatesT64

-- Explicit full-window certificate for the earliest successful 63P sweep coordinate.
namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def sixtyThreeBIFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem sixtyThreeBIFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    sixtyThreeBIFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [sixtyThreeBIFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [sixtyThreeBIFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then sixtyThreeBIFastPow a n * sixtyThreeBIFastPow a n * a
        else sixtyThreeBIFastPow a n * sixtyThreeBIFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_sixtyThreeBI_2 : Nat.Prime 2 := by norm_num
private theorem prime_sixtyThreeBI_3 : Nat.Prime 3 := by norm_num
private theorem prime_sixtyThreeBI_5 : Nat.Prime 5 := by norm_num
private theorem prime_sixtyThreeBI_7 : Nat.Prime 7 := by norm_num
private theorem prime_sixtyThreeBI_11 : Nat.Prime 11 := by norm_num
private theorem prime_sixtyThreeBI_13 : Nat.Prime 13 := by norm_num
private theorem prime_sixtyThreeBI_17 : Nat.Prime 17 := by norm_num
private theorem prime_sixtyThreeBI_19 : Nat.Prime 19 := by norm_num
private theorem prime_sixtyThreeBI_23 : Nat.Prime 23 := by norm_num
private theorem prime_sixtyThreeBI_29 : Nat.Prime 29 := by norm_num
private theorem prime_sixtyThreeBI_31 : Nat.Prime 31 := by norm_num
private theorem prime_sixtyThreeBI_37 : Nat.Prime 37 := by norm_num
private theorem prime_sixtyThreeBI_41 : Nat.Prime 41 := by norm_num
private theorem prime_sixtyThreeBI_43 : Nat.Prime 43 := by norm_num
private theorem prime_sixtyThreeBI_47 : Nat.Prime 47 := by norm_num
private theorem prime_sixtyThreeBI_53 : Nat.Prime 53 := by norm_num
private theorem prime_sixtyThreeBI_59 : Nat.Prime 59 := by norm_num
private theorem prime_sixtyThreeBI_61 : Nat.Prime 61 := by norm_num
private theorem prime_sixtyThreeBI_67 : Nat.Prime 67 := by norm_num
private theorem prime_sixtyThreeBI_71 : Nat.Prime 71 := by norm_num
private theorem prime_sixtyThreeBI_73 : Nat.Prime 73 := by norm_num
private theorem prime_sixtyThreeBI_79 : Nat.Prime 79 := by norm_num
private theorem prime_sixtyThreeBI_83 : Nat.Prime 83 := by norm_num
private theorem prime_sixtyThreeBI_89 : Nat.Prime 89 := by norm_num
private theorem prime_sixtyThreeBI_97 : Nat.Prime 97 := by norm_num
private theorem prime_sixtyThreeBI_101 : Nat.Prime 101 := by norm_num
private theorem prime_sixtyThreeBI_103 : Nat.Prime 103 := by norm_num
private theorem prime_sixtyThreeBI_107 : Nat.Prime 107 := by norm_num
private theorem prime_sixtyThreeBI_109 : Nat.Prime 109 := by norm_num
private theorem prime_sixtyThreeBI_113 : Nat.Prime 113 := by norm_num
private theorem prime_sixtyThreeBI_127 : Nat.Prime 127 := by norm_num
private theorem prime_sixtyThreeBI_131 : Nat.Prime 131 := by norm_num
private theorem prime_sixtyThreeBI_137 : Nat.Prime 137 := by norm_num
private theorem prime_sixtyThreeBI_139 : Nat.Prime 139 := by norm_num
private theorem prime_sixtyThreeBI_149 : Nat.Prime 149 := by norm_num
private theorem prime_sixtyThreeBI_157 : Nat.Prime 157 := by norm_num
private theorem prime_sixtyThreeBI_163 : Nat.Prime 163 := by norm_num
private theorem prime_sixtyThreeBI_173 : Nat.Prime 173 := by norm_num
private theorem prime_sixtyThreeBI_179 : Nat.Prime 179 := by norm_num
private theorem prime_sixtyThreeBI_181 : Nat.Prime 181 := by norm_num
private theorem prime_sixtyThreeBI_193 : Nat.Prime 193 := by norm_num
private theorem prime_sixtyThreeBI_197 : Nat.Prime 197 := by norm_num
private theorem prime_sixtyThreeBI_199 : Nat.Prime 199 := by norm_num
private theorem prime_sixtyThreeBI_211 : Nat.Prime 211 := by norm_num
private theorem prime_sixtyThreeBI_223 : Nat.Prime 223 := by norm_num
private theorem prime_sixtyThreeBI_227 : Nat.Prime 227 := by norm_num
private theorem prime_sixtyThreeBI_229 : Nat.Prime 229 := by norm_num
private theorem prime_sixtyThreeBI_233 : Nat.Prime 233 := by norm_num
private theorem prime_sixtyThreeBI_239 : Nat.Prime 239 := by norm_num
private theorem prime_sixtyThreeBI_241 : Nat.Prime 241 := by norm_num
private theorem prime_sixtyThreeBI_251 : Nat.Prime 251 := by norm_num
private theorem prime_sixtyThreeBI_269 : Nat.Prime 269 := by norm_num
private theorem prime_sixtyThreeBI_281 : Nat.Prime 281 := by norm_num
private theorem prime_sixtyThreeBI_283 : Nat.Prime 283 := by norm_num
private theorem prime_sixtyThreeBI_293 : Nat.Prime 293 := by norm_num
private theorem prime_sixtyThreeBI_307 : Nat.Prime 307 := by norm_num
private theorem prime_sixtyThreeBI_311 : Nat.Prime 311 := by norm_num
private theorem prime_sixtyThreeBI_313 : Nat.Prime 313 := by norm_num
private theorem prime_sixtyThreeBI_317 : Nat.Prime 317 := by norm_num
private theorem prime_sixtyThreeBI_331 : Nat.Prime 331 := by norm_num
private theorem prime_sixtyThreeBI_337 : Nat.Prime 337 := by norm_num
private theorem prime_sixtyThreeBI_347 : Nat.Prime 347 := by norm_num
private theorem prime_sixtyThreeBI_353 : Nat.Prime 353 := by norm_num
private theorem prime_sixtyThreeBI_367 : Nat.Prime 367 := by norm_num
private theorem prime_sixtyThreeBI_379 : Nat.Prime 379 := by norm_num
private theorem prime_sixtyThreeBI_383 : Nat.Prime 383 := by norm_num
private theorem prime_sixtyThreeBI_389 : Nat.Prime 389 := by norm_num
private theorem prime_sixtyThreeBI_397 : Nat.Prime 397 := by norm_num
private theorem prime_sixtyThreeBI_401 : Nat.Prime 401 := by norm_num
private theorem prime_sixtyThreeBI_409 : Nat.Prime 409 := by norm_num
private theorem prime_sixtyThreeBI_419 : Nat.Prime 419 := by norm_num
private theorem prime_sixtyThreeBI_421 : Nat.Prime 421 := by norm_num
private theorem prime_sixtyThreeBI_433 : Nat.Prime 433 := by norm_num
private theorem prime_sixtyThreeBI_439 : Nat.Prime 439 := by norm_num
private theorem prime_sixtyThreeBI_479 : Nat.Prime 479 := by norm_num
private theorem prime_sixtyThreeBI_491 : Nat.Prime 491 := by norm_num
private theorem prime_sixtyThreeBI_499 : Nat.Prime 499 := by norm_num
private theorem prime_sixtyThreeBI_509 : Nat.Prime 509 := by norm_num
private theorem prime_sixtyThreeBI_521 : Nat.Prime 521 := by norm_num
private theorem prime_sixtyThreeBI_587 : Nat.Prime 587 := by norm_num
private theorem prime_sixtyThreeBI_613 : Nat.Prime 613 := by norm_num
private theorem prime_sixtyThreeBI_631 : Nat.Prime 631 := by norm_num
private theorem prime_sixtyThreeBI_641 : Nat.Prime 641 := by norm_num
private theorem prime_sixtyThreeBI_643 : Nat.Prime 643 := by norm_num
private theorem prime_sixtyThreeBI_647 : Nat.Prime 647 := by norm_num
private theorem prime_sixtyThreeBI_659 : Nat.Prime 659 := by norm_num
private theorem prime_sixtyThreeBI_673 : Nat.Prime 673 := by norm_num
private theorem prime_sixtyThreeBI_683 : Nat.Prime 683 := by norm_num
private theorem prime_sixtyThreeBI_719 : Nat.Prime 719 := by norm_num
private theorem prime_sixtyThreeBI_727 : Nat.Prime 727 := by norm_num
private theorem prime_sixtyThreeBI_757 : Nat.Prime 757 := by norm_num
private theorem prime_sixtyThreeBI_809 : Nat.Prime 809 := by norm_num
private theorem prime_sixtyThreeBI_853 : Nat.Prime 853 := by norm_num
private theorem prime_sixtyThreeBI_859 : Nat.Prime 859 := by norm_num
private theorem prime_sixtyThreeBI_883 : Nat.Prime 883 := by norm_num
private theorem prime_sixtyThreeBI_907 : Nat.Prime 907 := by norm_num
private theorem prime_sixtyThreeBI_911 : Nat.Prime 911 := by norm_num
private theorem prime_sixtyThreeBI_929 : Nat.Prime 929 := by norm_num
private theorem prime_sixtyThreeBI_971 : Nat.Prime 971 := by norm_num
private theorem prime_sixtyThreeBI_991 : Nat.Prime 991 := by norm_num
private theorem prime_sixtyThreeBI_997 : Nat.Prime 997 := by norm_num
private theorem prime_sixtyThreeBI_1019 : Nat.Prime 1019 := by norm_num
private theorem prime_sixtyThreeBI_1021 : Nat.Prime 1021 := by norm_num
private theorem prime_sixtyThreeBI_1033 : Nat.Prime 1033 := by norm_num
private theorem prime_sixtyThreeBI_1039 : Nat.Prime 1039 := by norm_num
private theorem prime_sixtyThreeBI_1051 : Nat.Prime 1051 := by norm_num
private theorem prime_sixtyThreeBI_1087 : Nat.Prime 1087 := by norm_num
private theorem prime_sixtyThreeBI_1093 : Nat.Prime 1093 := by norm_num
private theorem prime_sixtyThreeBI_1103 : Nat.Prime 1103 := by norm_num
private theorem prime_sixtyThreeBI_1109 : Nat.Prime 1109 := by norm_num
private theorem prime_sixtyThreeBI_1117 : Nat.Prime 1117 := by norm_num
private theorem prime_sixtyThreeBI_1187 : Nat.Prime 1187 := by norm_num
private theorem prime_sixtyThreeBI_1201 : Nat.Prime 1201 := by norm_num
private theorem prime_sixtyThreeBI_1213 : Nat.Prime 1213 := by norm_num
private theorem prime_sixtyThreeBI_1259 : Nat.Prime 1259 := by norm_num
private theorem prime_sixtyThreeBI_1291 : Nat.Prime 1291 := by norm_num
private theorem prime_sixtyThreeBI_1327 : Nat.Prime 1327 := by norm_num
private theorem prime_sixtyThreeBI_1423 : Nat.Prime 1423 := by norm_num
private theorem prime_sixtyThreeBI_1429 : Nat.Prime 1429 := by norm_num
private theorem prime_sixtyThreeBI_1447 : Nat.Prime 1447 := by norm_num
private theorem prime_sixtyThreeBI_1471 : Nat.Prime 1471 := by norm_num
private theorem prime_sixtyThreeBI_1487 : Nat.Prime 1487 := by norm_num
private theorem prime_sixtyThreeBI_1493 : Nat.Prime 1493 := by norm_num
private theorem prime_sixtyThreeBI_1543 : Nat.Prime 1543 := by norm_num
private theorem prime_sixtyThreeBI_1553 : Nat.Prime 1553 := by norm_num
private theorem prime_sixtyThreeBI_1571 : Nat.Prime 1571 := by norm_num
private theorem prime_sixtyThreeBI_1597 : Nat.Prime 1597 := by norm_num
private theorem prime_sixtyThreeBI_1669 : Nat.Prime 1669 := by norm_num
private theorem prime_sixtyThreeBI_1753 : Nat.Prime 1753 := by norm_num
private theorem prime_sixtyThreeBI_1801 : Nat.Prime 1801 := by norm_num
private theorem prime_sixtyThreeBI_1811 : Nat.Prime 1811 := by norm_num
private theorem prime_sixtyThreeBI_1847 : Nat.Prime 1847 := by norm_num
private theorem prime_sixtyThreeBI_1873 : Nat.Prime 1873 := by norm_num
private theorem prime_sixtyThreeBI_1913 : Nat.Prime 1913 := by norm_num
private theorem prime_sixtyThreeBI_1949 : Nat.Prime 1949 := by norm_num
private theorem prime_sixtyThreeBI_2027 : Nat.Prime 2027 := by norm_num
private theorem prime_sixtyThreeBI_2063 : Nat.Prime 2063 := by norm_num
private theorem prime_sixtyThreeBI_2179 : Nat.Prime 2179 := by norm_num
private theorem prime_sixtyThreeBI_2237 : Nat.Prime 2237 := by norm_num
private theorem prime_sixtyThreeBI_2239 : Nat.Prime 2239 := by norm_num
private theorem prime_sixtyThreeBI_2311 : Nat.Prime 2311 := by norm_num
private theorem prime_sixtyThreeBI_2371 : Nat.Prime 2371 := by norm_num
private theorem prime_sixtyThreeBI_2521 : Nat.Prime 2521 := by norm_num
private theorem prime_sixtyThreeBI_2657 : Nat.Prime 2657 := by norm_num
private theorem prime_sixtyThreeBI_2689 : Nat.Prime 2689 := by norm_num
private theorem prime_sixtyThreeBI_2729 : Nat.Prime 2729 := by norm_num
private theorem prime_sixtyThreeBI_2753 : Nat.Prime 2753 := by norm_num
private theorem prime_sixtyThreeBI_2777 : Nat.Prime 2777 := by norm_num
private theorem prime_sixtyThreeBI_2819 : Nat.Prime 2819 := by norm_num
private theorem prime_sixtyThreeBI_2857 : Nat.Prime 2857 := by norm_num
private theorem prime_sixtyThreeBI_2999 : Nat.Prime 2999 := by norm_num
private theorem prime_sixtyThreeBI_3187 : Nat.Prime 3187 := by norm_num
private theorem prime_sixtyThreeBI_3319 : Nat.Prime 3319 := by norm_num
private theorem prime_sixtyThreeBI_3433 : Nat.Prime 3433 := by norm_num
private theorem prime_sixtyThreeBI_3467 : Nat.Prime 3467 := by norm_num
private theorem prime_sixtyThreeBI_3659 : Nat.Prime 3659 := by norm_num
private theorem prime_sixtyThreeBI_3709 : Nat.Prime 3709 := by norm_num
private theorem prime_sixtyThreeBI_3889 : Nat.Prime 3889 := by norm_num
private theorem prime_sixtyThreeBI_3917 : Nat.Prime 3917 := by norm_num
private theorem prime_sixtyThreeBI_4019 : Nat.Prime 4019 := by norm_num
private theorem prime_sixtyThreeBI_4079 : Nat.Prime 4079 := by norm_num
private theorem prime_sixtyThreeBI_4099 : Nat.Prime 4099 := by norm_num
private theorem prime_sixtyThreeBI_4339 : Nat.Prime 4339 := by norm_num
private theorem prime_sixtyThreeBI_4373 : Nat.Prime 4373 := by norm_num
private theorem prime_sixtyThreeBI_4441 : Nat.Prime 4441 := by norm_num
private theorem prime_sixtyThreeBI_4451 : Nat.Prime 4451 := by norm_num
private theorem prime_sixtyThreeBI_4783 : Nat.Prime 4783 := by norm_num
private theorem prime_sixtyThreeBI_4903 : Nat.Prime 4903 := by norm_num
private theorem prime_sixtyThreeBI_4937 : Nat.Prime 4937 := by norm_num
private theorem prime_sixtyThreeBI_5323 : Nat.Prime 5323 := by norm_num
private theorem prime_sixtyThreeBI_5351 : Nat.Prime 5351 := by norm_num
private theorem prime_sixtyThreeBI_5573 : Nat.Prime 5573 := by norm_num
private theorem prime_sixtyThreeBI_5743 : Nat.Prime 5743 := by norm_num
private theorem prime_sixtyThreeBI_5953 : Nat.Prime 5953 := by norm_num
private theorem prime_sixtyThreeBI_6029 : Nat.Prime 6029 := by norm_num
private theorem prime_sixtyThreeBI_6221 : Nat.Prime 6221 := by norm_num
private theorem prime_sixtyThreeBI_6271 : Nat.Prime 6271 := by norm_num
private theorem prime_sixtyThreeBI_6299 : Nat.Prime 6299 := by norm_num
private theorem prime_sixtyThreeBI_6397 : Nat.Prime 6397 := by norm_num
private theorem prime_sixtyThreeBI_6421 : Nat.Prime 6421 := by norm_num
private theorem prime_sixtyThreeBI_6473 : Nat.Prime 6473 := by norm_num
private theorem prime_sixtyThreeBI_6547 : Nat.Prime 6547 := by norm_num
private theorem prime_sixtyThreeBI_6991 : Nat.Prime 6991 := by norm_num
private theorem prime_sixtyThreeBI_7013 : Nat.Prime 7013 := by norm_num
private theorem prime_sixtyThreeBI_7103 : Nat.Prime 7103 := by norm_num
private theorem prime_sixtyThreeBI_7583 : Nat.Prime 7583 := by norm_num
private theorem prime_sixtyThreeBI_7607 : Nat.Prime 7607 := by norm_num
private theorem prime_sixtyThreeBI_7621 : Nat.Prime 7621 := by norm_num
private theorem prime_sixtyThreeBI_7681 : Nat.Prime 7681 := by norm_num
private theorem prime_sixtyThreeBI_7687 : Nat.Prime 7687 := by norm_num
private theorem prime_sixtyThreeBI_7949 : Nat.Prime 7949 := by norm_num
private theorem prime_sixtyThreeBI_7993 : Nat.Prime 7993 := by norm_num
private theorem prime_sixtyThreeBI_8167 : Nat.Prime 8167 := by norm_num
private theorem prime_sixtyThreeBI_8231 : Nat.Prime 8231 := by norm_num
private theorem prime_sixtyThreeBI_8387 : Nat.Prime 8387 := by norm_num
private theorem prime_sixtyThreeBI_8699 : Nat.Prime 8699 := by norm_num
private theorem prime_sixtyThreeBI_9011 : Nat.Prime 9011 := by norm_num
private theorem prime_sixtyThreeBI_9109 : Nat.Prime 9109 := by norm_num
private theorem prime_sixtyThreeBI_9907 : Nat.Prime 9907 := by norm_num
private theorem prime_sixtyThreeBI_10103 : Nat.Prime 10103 := by norm_num
private theorem prime_sixtyThreeBI_10211 : Nat.Prime 10211 := by norm_num
private theorem prime_sixtyThreeBI_10247 : Nat.Prime 10247 := by norm_num
private theorem prime_sixtyThreeBI_10433 : Nat.Prime 10433 := by norm_num
private theorem prime_sixtyThreeBI_10729 : Nat.Prime 10729 := by norm_num
private theorem prime_sixtyThreeBI_11621 : Nat.Prime 11621 := by norm_num
private theorem prime_sixtyThreeBI_11681 : Nat.Prime 11681 := by norm_num
private theorem prime_sixtyThreeBI_11813 : Nat.Prime 11813 := by norm_num
private theorem prime_sixtyThreeBI_12301 : Nat.Prime 12301 := by norm_num
private theorem prime_sixtyThreeBI_12721 : Nat.Prime 12721 := by norm_num
private theorem prime_sixtyThreeBI_13597 : Nat.Prime 13597 := by norm_num
private theorem prime_sixtyThreeBI_13711 : Nat.Prime 13711 := by norm_num
private theorem prime_sixtyThreeBI_13901 : Nat.Prime 13901 := by norm_num
private theorem prime_sixtyThreeBI_14327 : Nat.Prime 14327 := by norm_num
private theorem prime_sixtyThreeBI_14533 : Nat.Prime 14533 := by norm_num
private theorem prime_sixtyThreeBI_14563 : Nat.Prime 14563 := by norm_num
private theorem prime_sixtyThreeBI_14983 : Nat.Prime 14983 := by norm_num
private theorem prime_sixtyThreeBI_15073 : Nat.Prime 15073 := by norm_num
private theorem prime_sixtyThreeBI_15161 : Nat.Prime 15161 := by norm_num
private theorem prime_sixtyThreeBI_15307 : Nat.Prime 15307 := by norm_num
private theorem prime_sixtyThreeBI_15907 : Nat.Prime 15907 := by norm_num
private theorem prime_sixtyThreeBI_16063 : Nat.Prime 16063 := by norm_num
private theorem prime_sixtyThreeBI_16091 : Nat.Prime 16091 := by norm_num
private theorem prime_sixtyThreeBI_16871 : Nat.Prime 16871 := by norm_num
private theorem prime_sixtyThreeBI_17207 : Nat.Prime 17207 := by norm_num
private theorem prime_sixtyThreeBI_17623 : Nat.Prime 17623 := by norm_num
private theorem prime_sixtyThreeBI_18269 : Nat.Prime 18269 := by norm_num
private theorem prime_sixtyThreeBI_18947 : Nat.Prime 18947 := by norm_num
private theorem prime_sixtyThreeBI_19139 : Nat.Prime 19139 := by norm_num
private theorem prime_sixtyThreeBI_19553 : Nat.Prime 19553 := by norm_num
private theorem prime_sixtyThreeBI_19717 : Nat.Prime 19717 := by norm_num
private theorem prime_sixtyThreeBI_19889 : Nat.Prime 19889 := by norm_num
private theorem prime_sixtyThreeBI_19979 : Nat.Prime 19979 := by norm_num
private theorem prime_sixtyThreeBI_20773 : Nat.Prime 20773 := by norm_num
private theorem prime_sixtyThreeBI_21661 : Nat.Prime 21661 := by norm_num
private theorem prime_sixtyThreeBI_22271 : Nat.Prime 22271 := by norm_num
private theorem prime_sixtyThreeBI_22381 : Nat.Prime 22381 := by norm_num
private theorem prime_sixtyThreeBI_22481 : Nat.Prime 22481 := by norm_num
private theorem prime_sixtyThreeBI_23459 : Nat.Prime 23459 := by norm_num
private theorem prime_sixtyThreeBI_23549 : Nat.Prime 23549 := by norm_num
private theorem prime_sixtyThreeBI_24671 : Nat.Prime 24671 := by norm_num
private theorem prime_sixtyThreeBI_27823 : Nat.Prime 27823 := by norm_num
private theorem prime_sixtyThreeBI_27953 : Nat.Prime 27953 := by norm_num
private theorem prime_sixtyThreeBI_30869 : Nat.Prime 30869 := by norm_num
private theorem prime_sixtyThreeBI_31517 : Nat.Prime 31517 := by norm_num
private theorem prime_sixtyThreeBI_31883 : Nat.Prime 31883 := by norm_num
private theorem prime_sixtyThreeBI_32983 : Nat.Prime 32983 := by norm_num
private theorem prime_sixtyThreeBI_33289 : Nat.Prime 33289 := by norm_num
private theorem prime_sixtyThreeBI_36973 : Nat.Prime 36973 := by norm_num
private theorem prime_sixtyThreeBI_37123 : Nat.Prime 37123 := by norm_num
private theorem prime_sixtyThreeBI_37501 : Nat.Prime 37501 := by norm_num
private theorem prime_sixtyThreeBI_38377 : Nat.Prime 38377 := by norm_num
private theorem prime_sixtyThreeBI_38453 : Nat.Prime 38453 := by norm_num
private theorem prime_sixtyThreeBI_39451 : Nat.Prime 39451 := by norm_num
private theorem prime_sixtyThreeBI_40739 : Nat.Prime 40739 := by norm_num
private theorem prime_sixtyThreeBI_40949 : Nat.Prime 40949 := by norm_num
private theorem prime_sixtyThreeBI_42569 : Nat.Prime 42569 := by norm_num
private theorem prime_sixtyThreeBI_42703 : Nat.Prime 42703 := by norm_num
private theorem prime_sixtyThreeBI_44867 : Nat.Prime 44867 := by norm_num
private theorem prime_sixtyThreeBI_47431 : Nat.Prime 47431 := by norm_num
private theorem prime_sixtyThreeBI_49603 : Nat.Prime 49603 := by norm_num
private theorem prime_sixtyThreeBI_50359 : Nat.Prime 50359 := by norm_num
private theorem prime_sixtyThreeBI_56701 : Nat.Prime 56701 := by norm_num
private theorem prime_sixtyThreeBI_58439 : Nat.Prime 58439 := by norm_num
private theorem prime_sixtyThreeBI_59729 : Nat.Prime 59729 := by norm_num
private theorem prime_sixtyThreeBI_60029 : Nat.Prime 60029 := by norm_num
private theorem prime_sixtyThreeBI_61703 : Nat.Prime 61703 := by norm_num
private theorem prime_sixtyThreeBI_65993 : Nat.Prime 65993 := by norm_num
private theorem prime_sixtyThreeBI_67733 : Nat.Prime 67733 := by norm_num
private theorem prime_sixtyThreeBI_70079 : Nat.Prime 70079 := by norm_num
private theorem prime_sixtyThreeBI_73243 : Nat.Prime 73243 := by norm_num
private theorem prime_sixtyThreeBI_74203 : Nat.Prime 74203 := by norm_num
private theorem prime_sixtyThreeBI_85819 : Nat.Prime 85819 := by norm_num
private theorem prime_sixtyThreeBI_89231 : Nat.Prime 89231 := by norm_num
private theorem prime_sixtyThreeBI_91961 : Nat.Prime 91961 := by norm_num
private theorem prime_sixtyThreeBI_92507 : Nat.Prime 92507 := by norm_num
private theorem prime_sixtyThreeBI_106217 : Nat.Prime 106217 := by norm_num
private theorem prime_sixtyThreeBI_110533 : Nat.Prime 110533 := by norm_num
private theorem prime_sixtyThreeBI_110629 : Nat.Prime 110629 := by norm_num
private theorem prime_sixtyThreeBI_114013 : Nat.Prime 114013 := by norm_num
private theorem prime_sixtyThreeBI_124427 : Nat.Prime 124427 := by norm_num
private theorem prime_sixtyThreeBI_126227 : Nat.Prime 126227 := by norm_num
private theorem prime_sixtyThreeBI_130069 : Nat.Prime 130069 := by norm_num
private theorem prime_sixtyThreeBI_134669 : Nat.Prime 134669 := by norm_num
private theorem prime_sixtyThreeBI_137933 : Nat.Prime 137933 := by norm_num
private theorem prime_sixtyThreeBI_149333 : Nat.Prime 149333 := by norm_num
private theorem prime_sixtyThreeBI_151243 : Nat.Prime 151243 := by norm_num
private theorem prime_sixtyThreeBI_153271 : Nat.Prime 153271 := by norm_num
private theorem prime_sixtyThreeBI_160649 : Nat.Prime 160649 := by norm_num
private theorem prime_sixtyThreeBI_162641 : Nat.Prime 162641 := by norm_num
private theorem prime_sixtyThreeBI_166237 : Nat.Prime 166237 := by norm_num
private theorem prime_sixtyThreeBI_168433 : Nat.Prime 168433 := by norm_num
private theorem prime_sixtyThreeBI_179119 : Nat.Prime 179119 := by norm_num
private theorem prime_sixtyThreeBI_180053 : Nat.Prime 180053 := by norm_num
private theorem prime_sixtyThreeBI_191461 : Nat.Prime 191461 := by norm_num
private theorem prime_sixtyThreeBI_198221 : Nat.Prime 198221 := by norm_num
private theorem prime_sixtyThreeBI_204733 : Nat.Prime 204733 := by norm_num
private theorem prime_sixtyThreeBI_212987 : Nat.Prime 212987 := by norm_num
private theorem prime_sixtyThreeBI_216133 : Nat.Prime 216133 := by norm_num
private theorem prime_sixtyThreeBI_222511 : Nat.Prime 222511 := by norm_num
private theorem prime_sixtyThreeBI_260723 : Nat.Prime 260723 := by norm_num
private theorem prime_sixtyThreeBI_261089 : Nat.Prime 261089 := by norm_num
private theorem prime_sixtyThreeBI_262747 : Nat.Prime 262747 := by norm_num
private theorem prime_sixtyThreeBI_263399 : Nat.Prime 263399 := by norm_num
private theorem prime_sixtyThreeBI_274301 : Nat.Prime 274301 := by norm_num
private theorem prime_sixtyThreeBI_280811 : Nat.Prime 280811 := by norm_num
private theorem prime_sixtyThreeBI_294923 : Nat.Prime 294923 := by norm_num
private theorem prime_sixtyThreeBI_326537 : Nat.Prime 326537 := by norm_num
private theorem prime_sixtyThreeBI_351223 : Nat.Prime 351223 := by norm_num
private theorem prime_sixtyThreeBI_363871 : Nat.Prime 363871 := by norm_num
private theorem prime_sixtyThreeBI_367163 : Nat.Prime 367163 := by norm_num
private theorem prime_sixtyThreeBI_377183 : Nat.Prime 377183 := by norm_num
private theorem prime_sixtyThreeBI_381631 : Nat.Prime 381631 := by norm_num
private theorem prime_sixtyThreeBI_393017 : Nat.Prime 393017 := by norm_num
private theorem prime_sixtyThreeBI_428693 : Nat.Prime 428693 := by norm_num
private theorem prime_sixtyThreeBI_444929 : Nat.Prime 444929 := by norm_num
private theorem prime_sixtyThreeBI_450277 : Nat.Prime 450277 := by norm_num
private theorem prime_sixtyThreeBI_452869 : Nat.Prime 452869 := by norm_num
private theorem prime_sixtyThreeBI_486053 : Nat.Prime 486053 := by norm_num
private theorem prime_sixtyThreeBI_520151 : Nat.Prime 520151 := by norm_num
private theorem prime_sixtyThreeBI_524827 : Nat.Prime 524827 := by norm_num
private theorem prime_sixtyThreeBI_543307 : Nat.Prime 543307 := by norm_num
private theorem prime_sixtyThreeBI_570967 : Nat.Prime 570967 := by norm_num
private theorem prime_sixtyThreeBI_603667 : Nat.Prime 603667 := by norm_num
private theorem prime_sixtyThreeBI_610639 : Nat.Prime 610639 := by norm_num
private theorem prime_sixtyThreeBI_616153 : Nat.Prime 616153 := by norm_num
private theorem prime_sixtyThreeBI_638629 : Nat.Prime 638629 := by norm_num
private theorem prime_sixtyThreeBI_669551 : Nat.Prime 669551 := by norm_num
private theorem prime_sixtyThreeBI_705559 : Nat.Prime 705559 := by norm_num
private theorem prime_sixtyThreeBI_775757 : Nat.Prime 775757 := by norm_num
private theorem prime_sixtyThreeBI_803519 : Nat.Prime 803519 := by norm_num
private theorem prime_sixtyThreeBI_917789 : Nat.Prime 917789 := by norm_num
private theorem prime_sixtyThreeBI_953131 : Nat.Prime 953131 := by norm_num
private theorem prime_sixtyThreeBI_964609 : Nat.Prime 964609 := by norm_num
private theorem prime_sixtyThreeBI_994199 : Nat.Prime 994199 := by norm_num
private theorem prime_sixtyThreeBI_1117099 : Nat.Prime 1117099 := by norm_num
private theorem prime_sixtyThreeBI_1156907 : Nat.Prime 1156907 := by norm_num
private theorem prime_sixtyThreeBI_1195891 : Nat.Prime 1195891 := by norm_num
private theorem prime_sixtyThreeBI_1225327 : Nat.Prime 1225327 := by norm_num
private theorem prime_sixtyThreeBI_1331773 : Nat.Prime 1331773 := by norm_num
private theorem prime_sixtyThreeBI_1456799 : Nat.Prime 1456799 := by norm_num
private theorem prime_sixtyThreeBI_1471621 : Nat.Prime 1471621 := by norm_num
private theorem prime_sixtyThreeBI_1616827 : Nat.Prime 1616827 := by norm_num
private theorem prime_sixtyThreeBI_1877111 : Nat.Prime 1877111 := by norm_num
private theorem prime_sixtyThreeBI_1988291 : Nat.Prime 1988291 := by norm_num
private theorem prime_sixtyThreeBI_1989803 : Nat.Prime 1989803 := by norm_num
private theorem prime_sixtyThreeBI_1997587 : Nat.Prime 1997587 := by norm_num
private theorem prime_sixtyThreeBI_2007251 : Nat.Prime 2007251 := by norm_num
private theorem prime_sixtyThreeBI_2137913 : Nat.Prime 2137913 := by norm_num
private theorem prime_sixtyThreeBI_2343349 : Nat.Prime 2343349 := by norm_num
private theorem prime_sixtyThreeBI_2384953 : Nat.Prime 2384953 := by norm_num
private theorem prime_sixtyThreeBI_2466661 : Nat.Prime 2466661 := by norm_num
private theorem prime_sixtyThreeBI_2492563 : Nat.Prime 2492563 := by norm_num
private theorem prime_sixtyThreeBI_2676419 : Nat.Prime 2676419 := by norm_num
private theorem prime_sixtyThreeBI_2681929 : Nat.Prime 2681929 := by norm_num
private theorem prime_sixtyThreeBI_2800403 : Nat.Prime 2800403 := by norm_num
private theorem prime_sixtyThreeBI_2829961 : Nat.Prime 2829961 := by norm_num
private theorem prime_sixtyThreeBI_2894989 : Nat.Prime 2894989 := by norm_num
private theorem prime_sixtyThreeBI_2914673 : Nat.Prime 2914673 := by norm_num
private theorem prime_sixtyThreeBI_2958721 : Nat.Prime 2958721 := by norm_num
private theorem prime_sixtyThreeBI_3374473 : Nat.Prime 3374473 := by norm_num
private theorem prime_sixtyThreeBI_4130129 : Nat.Prime 4130129 := by norm_num
private theorem prime_sixtyThreeBI_4154959 : Nat.Prime 4154959 := by norm_num
private theorem prime_sixtyThreeBI_4213679 : Nat.Prime 4213679 := by norm_num
private theorem prime_sixtyThreeBI_4572109 : Nat.Prime 4572109 := by norm_num
private theorem prime_sixtyThreeBI_4613729 : Nat.Prime 4613729 := by norm_num
private theorem prime_sixtyThreeBI_4974793 : Nat.Prime 4974793 := by norm_num
private theorem prime_sixtyThreeBI_5206241 : Nat.Prime 5206241 := by norm_num
private theorem prime_sixtyThreeBI_5366419 : Nat.Prime 5366419 := by norm_num
private theorem prime_sixtyThreeBI_5752939 : Nat.Prime 5752939 := by norm_num
private theorem prime_sixtyThreeBI_5801401 : Nat.Prime 5801401 := by norm_num
private theorem prime_sixtyThreeBI_6208303 : Nat.Prime 6208303 := by norm_num
private theorem prime_sixtyThreeBI_6315073 : Nat.Prime 6315073 := by norm_num
private theorem prime_sixtyThreeBI_6505063 : Nat.Prime 6505063 := by norm_num
private theorem prime_sixtyThreeBI_6516421 : Nat.Prime 6516421 := by norm_num
private theorem prime_sixtyThreeBI_6539513 : Nat.Prime 6539513 := by norm_num
private theorem prime_sixtyThreeBI_7184447 : Nat.Prime 7184447 := by norm_num
private theorem prime_sixtyThreeBI_7256369 : Nat.Prime 7256369 := by norm_num
private theorem prime_sixtyThreeBI_7586629 : Nat.Prime 7586629 := by norm_num
private theorem prime_sixtyThreeBI_7989493 : Nat.Prime 7989493 := by norm_num
private theorem prime_sixtyThreeBI_8025469 : Nat.Prime 8025469 := by norm_num
private theorem prime_sixtyThreeBI_8364023 : Nat.Prime 8364023 := by norm_num
private theorem prime_sixtyThreeBI_8966203 : Nat.Prime 8966203 := by norm_num
private theorem prime_sixtyThreeBI_9407179 : Nat.Prime 9407179 := by norm_num
private theorem prime_sixtyThreeBI_10520963 : Nat.Prime 10520963 := by norm_num
private theorem prime_sixtyThreeBI_10529899 : Nat.Prime 10529899 := by norm_num
private theorem prime_sixtyThreeBI_10764779 : Nat.Prime 10764779 := by norm_num
private theorem prime_sixtyThreeBI_10971929 : Nat.Prime 10971929 := by norm_num
private theorem prime_sixtyThreeBI_11683733 : Nat.Prime 11683733 := by norm_num
private theorem prime_sixtyThreeBI_11986463 : Nat.Prime 11986463 := by norm_num
private theorem prime_sixtyThreeBI_12789611 : Nat.Prime 12789611 := by norm_num
private theorem prime_sixtyThreeBI_13015517 : Nat.Prime 13015517 := by norm_num
private theorem prime_sixtyThreeBI_13303487 : Nat.Prime 13303487 := by norm_num
private theorem prime_sixtyThreeBI_14664301 : Nat.Prime 14664301 := by norm_num
private theorem prime_sixtyThreeBI_19972319 : Nat.Prime 19972319 := by norm_num
private theorem prime_sixtyThreeBI_20994901 : Nat.Prime 20994901 := by norm_num
private theorem prime_sixtyThreeBI_22107181 : Nat.Prime 22107181 := by norm_num
private theorem prime_sixtyThreeBI_22171999 : Nat.Prime 22171999 := by norm_num
private theorem prime_sixtyThreeBI_22671689 : Nat.Prime 22671689 := by norm_num
private theorem prime_sixtyThreeBI_22949011 : Nat.Prime 22949011 := by norm_num
private theorem prime_sixtyThreeBI_23649391 : Nat.Prime 23649391 := by norm_num
private theorem prime_sixtyThreeBI_25518379 : Nat.Prime 25518379 := by norm_num
private theorem prime_sixtyThreeBI_25525321 : Nat.Prime 25525321 := by norm_num
private theorem prime_sixtyThreeBI_26405261 : Nat.Prime 26405261 := by norm_num
private theorem prime_sixtyThreeBI_27047677 : Nat.Prime 27047677 := by norm_num
private theorem prime_sixtyThreeBI_27262513 : Nat.Prime 27262513 := by norm_num
private theorem prime_sixtyThreeBI_28133291 : Nat.Prime 28133291 := by norm_num

private theorem prime_sixtyThreeBI_31633369 : Nat.Prime 31633369 := by
  apply lucas_primality 31633369 (7 : ZMod 31633369)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (53, 1), (1913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (53, 1), (1913, 1)] : List FactorBlock).map factorBlockValue).prod) = 31633369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_13
      · exact prime_sixtyThreeBI_53
      · exact prime_sixtyThreeBI_1913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 31633369) ^ 15816684 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 31633369) ^ 10544456 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 31633369) ^ 2433336 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 31633369) ^ 596856 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 31633369) ^ 16536 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_33709433 : Nat.Prime 33709433 := by
  apply lucas_primality 33709433 (3 : ZMod 33709433)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (4213679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (4213679, 1)] : List FactorBlock).map factorBlockValue).prod) = 33709433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_4213679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 33709433) ^ 16854716 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 33709433) ^ 8 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_36130519 : Nat.Prime 36130519 := by
  apply lucas_primality 36130519 (3 : ZMod 36130519)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (2007251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (2007251, 1)] : List FactorBlock).map factorBlockValue).prod) = 36130519 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_2007251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 36130519) ^ 18065259 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 36130519) ^ 12043506 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 36130519) ^ 18 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_37469867 : Nat.Prime 37469867 := by
  apply lucas_primality 37469867 (2 : ZMod 37469867)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2676419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2676419, 1)] : List FactorBlock).map factorBlockValue).prod) = 37469867 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_2676419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 37469867) ^ 18734933 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 37469867) ^ 5352838 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 37469867) ^ 14 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_43883009 : Nat.Prime 43883009 := by
  apply lucas_primality 43883009 (3 : ZMod 43883009)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (13, 1), (19, 1), (347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (13, 1), (19, 1), (347, 1)] : List FactorBlock).map factorBlockValue).prod) = 43883009 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_13
      · exact prime_sixtyThreeBI_19
      · exact prime_sixtyThreeBI_347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 43883009) ^ 21941504 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 43883009) ^ 3375616 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 43883009) ^ 2309632 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 43883009) ^ 126464 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_43952869 : Nat.Prime 43952869 := by
  apply lucas_primality 43952869 (2 : ZMod 43952869)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 6), (15073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 6), (15073, 1)] : List FactorBlock).map factorBlockValue).prod) = 43952869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_15073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 43952869) ^ 21976434 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 43952869) ^ 14650956 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 43952869) ^ 2916 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_48468223 : Nat.Prime 48468223 := by
  apply lucas_primality 48468223 (3 : ZMod 48468223)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (23, 1), (29, 1), (367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (23, 1), (29, 1), (367, 1)] : List FactorBlock).map factorBlockValue).prod) = 48468223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_11
      · exact prime_sixtyThreeBI_23
      · exact prime_sixtyThreeBI_29
      · exact prime_sixtyThreeBI_367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 48468223) ^ 24234111 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 48468223) ^ 16156074 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 48468223) ^ 4406202 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 48468223) ^ 2107314 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 48468223) ^ 1671318 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 48468223) ^ 132066 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_49942351 : Nat.Prime 49942351 := by
  apply lucas_primality 49942351 (6 : ZMod 49942351)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (29, 1), (43, 1), (89, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (29, 1), (43, 1), (89, 1)] : List FactorBlock).map factorBlockValue).prod) = 49942351 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_29
      · exact prime_sixtyThreeBI_43
      · exact prime_sixtyThreeBI_89
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 49942351) ^ 24971175 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (6 : ZMod 49942351) ^ 16647450 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (6 : ZMod 49942351) ^ 9988470 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (6 : ZMod 49942351) ^ 1722150 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (6 : ZMod 49942351) ^ 1161450 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (6 : ZMod 49942351) ^ 561150 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_50084959 : Nat.Prime 50084959 := by
  apply lucas_primality 50084959 (3 : ZMod 50084959)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (11, 1), (17, 1), (911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (11, 1), (17, 1), (911, 1)] : List FactorBlock).map factorBlockValue).prod) = 50084959 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_11
      · exact prime_sixtyThreeBI_17
      · exact prime_sixtyThreeBI_911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 50084959) ^ 25042479 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 50084959) ^ 16694986 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 50084959) ^ 7154994 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 50084959) ^ 4553178 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 50084959) ^ 2946174 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 50084959) ^ 54978 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_53735701 : Nat.Prime 53735701 := by
  apply lucas_primality 53735701 (7 : ZMod 53735701)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (179119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (179119, 1)] : List FactorBlock).map factorBlockValue).prod) = 53735701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_179119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 53735701) ^ 26867850 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 53735701) ^ 17911900 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 53735701) ^ 10747140 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 53735701) ^ 300 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_56008061 : Nat.Prime 56008061 := by
  apply lucas_primality 56008061 (2 : ZMod 56008061)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (2800403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (2800403, 1)] : List FactorBlock).map factorBlockValue).prod) = 56008061 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_2800403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 56008061) ^ 28004030 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 56008061) ^ 11201612 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 56008061) ^ 20 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_58772507 : Nat.Prime 58772507 := by
  apply lucas_primality 58772507 (2 : ZMod 58772507)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (101, 1), (22381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (101, 1), (22381, 1)] : List FactorBlock).map factorBlockValue).prod) = 58772507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_13
      · exact prime_sixtyThreeBI_101
      · exact prime_sixtyThreeBI_22381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 58772507) ^ 29386253 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 58772507) ^ 4520962 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 58772507) ^ 581906 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 58772507) ^ 2626 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_66622273 : Nat.Prime 66622273 := by
  apply lucas_primality 66622273 (5 : ZMod 66622273)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (53, 1), (6547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (53, 1), (6547, 1)] : List FactorBlock).map factorBlockValue).prod) = 66622273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_53
      · exact prime_sixtyThreeBI_6547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 66622273) ^ 33311136 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 66622273) ^ 22207424 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 66622273) ^ 1257024 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 66622273) ^ 10176 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_70018687 : Nat.Prime 70018687 := by
  apply lucas_primality 70018687 (3 : ZMod 70018687)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (204733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (204733, 1)] : List FactorBlock).map factorBlockValue).prod) = 70018687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_19
      · exact prime_sixtyThreeBI_204733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 70018687) ^ 35009343 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 70018687) ^ 23339562 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 70018687) ^ 3685194 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 70018687) ^ 342 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_70102399 : Nat.Prime 70102399 := by
  apply lucas_primality 70102399 (3 : ZMod 70102399)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11683733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11683733, 1)] : List FactorBlock).map factorBlockValue).prod) = 70102399 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_11683733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 70102399) ^ 35051199 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 70102399) ^ 23367466 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 70102399) ^ 6 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_71330219 : Nat.Prime 71330219 := by
  apply lucas_primality 71330219 (2 : ZMod 71330219)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (1877111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (1877111, 1)] : List FactorBlock).map factorBlockValue).prod) = 71330219 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_19
      · exact prime_sixtyThreeBI_1877111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 71330219) ^ 35665109 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 71330219) ^ 3754222 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 71330219) ^ 38 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_72316711 : Nat.Prime 72316711 := by
  apply lucas_primality 72316711 (6 : ZMod 72316711)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (803519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (803519, 1)] : List FactorBlock).map factorBlockValue).prod) = 72316711 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_803519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 72316711) ^ 36158355 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (6 : ZMod 72316711) ^ 24105570 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (6 : ZMod 72316711) ^ 14463342 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (6 : ZMod 72316711) ^ 90 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_75033407 : Nat.Prime 75033407 := by
  apply lucas_primality 75033407 (5 : ZMod 75033407)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (23, 1), (33289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (23, 1), (33289, 1)] : List FactorBlock).map factorBlockValue).prod) = 75033407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_23
      · exact prime_sixtyThreeBI_33289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 75033407) ^ 37516703 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 75033407) ^ 10719058 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 75033407) ^ 3262322 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 75033407) ^ 2254 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_79854611 : Nat.Prime 79854611 := by
  apply lucas_primality 79854611 (2 : ZMod 79854611)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (17, 1), (42703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (17, 1), (42703, 1)] : List FactorBlock).map factorBlockValue).prod) = 79854611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_11
      · exact prime_sixtyThreeBI_17
      · exact prime_sixtyThreeBI_42703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 79854611) ^ 39927305 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 79854611) ^ 15970922 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 79854611) ^ 7259510 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 79854611) ^ 4697330 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 79854611) ^ 1870 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_84194447 : Nat.Prime 84194447 := by
  apply lucas_primality 84194447 (5 : ZMod 84194447)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (137, 1), (6271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (137, 1), (6271, 1)] : List FactorBlock).map factorBlockValue).prod) = 84194447 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_137
      · exact prime_sixtyThreeBI_6271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 84194447) ^ 42097223 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 84194447) ^ 12027778 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 84194447) ^ 614558 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 84194447) ^ 13426 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_101878597 : Nat.Prime 101878597 := by
  apply lucas_primality 101878597 (5 : ZMod 101878597)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (2829961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (2829961, 1)] : List FactorBlock).map factorBlockValue).prod) = 101878597 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_2829961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 101878597) ^ 50939298 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 101878597) ^ 33959532 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 101878597) ^ 36 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_102789431 : Nat.Prime 102789431 := by
  apply lucas_primality 102789431 (23 : ZMod 102789431)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (163, 1), (3319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (163, 1), (3319, 1)] : List FactorBlock).map factorBlockValue).prod) = 102789431 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_19
      · exact prime_sixtyThreeBI_163
      · exact prime_sixtyThreeBI_3319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 102789431) ^ 51394715 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (23 : ZMod 102789431) ^ 20557886 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (23 : ZMod 102789431) ^ 5409970 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (23 : ZMod 102789431) ^ 630610 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (23 : ZMod 102789431) ^ 30970 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_104124821 : Nat.Prime 104124821 := by
  apply lucas_primality 104124821 (3 : ZMod 104124821)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (5206241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (5206241, 1)] : List FactorBlock).map factorBlockValue).prod) = 104124821 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_5206241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 104124821) ^ 52062410 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 104124821) ^ 20824964 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 104124821) ^ 20 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_104130997 : Nat.Prime 104130997 := by
  apply lucas_primality 104130997 (5 : ZMod 104130997)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (73, 1), (4099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (73, 1), (4099, 1)] : List FactorBlock).map factorBlockValue).prod) = 104130997 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_29
      · exact prime_sixtyThreeBI_73
      · exact prime_sixtyThreeBI_4099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 104130997) ^ 52065498 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 104130997) ^ 34710332 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 104130997) ^ 3590724 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 104130997) ^ 1426452 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 104130997) ^ 25404 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_106427897 : Nat.Prime 106427897 := by
  apply lucas_primality 106427897 (3 : ZMod 106427897)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13303487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13303487, 1)] : List FactorBlock).map factorBlockValue).prod) = 106427897 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_13303487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 106427897) ^ 53213948 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 106427897) ^ 8 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_111616187 : Nat.Prime 111616187 := by
  apply lucas_primality 111616187 (2 : ZMod 111616187)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (17, 1), (29, 1), (41, 1), (251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (17, 1), (29, 1), (41, 1), (251, 1)] : List FactorBlock).map factorBlockValue).prod) = 111616187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_11
      · exact prime_sixtyThreeBI_17
      · exact prime_sixtyThreeBI_29
      · exact prime_sixtyThreeBI_41
      · exact prime_sixtyThreeBI_251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 111616187) ^ 55808093 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 111616187) ^ 10146926 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 111616187) ^ 6565658 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 111616187) ^ 3848834 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 111616187) ^ 2722346 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 111616187) ^ 444686 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_111728269 : Nat.Prime 111728269 := by
  apply lucas_primality 111728269 (2 : ZMod 111728269)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (727, 1), (1423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (727, 1), (1423, 1)] : List FactorBlock).map factorBlockValue).prod) = 111728269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_727
      · exact prime_sixtyThreeBI_1423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 111728269) ^ 55864134 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 111728269) ^ 37242756 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 111728269) ^ 153684 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 111728269) ^ 78516 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_112016123 : Nat.Prime 112016123 := by
  apply lucas_primality 112016123 (2 : ZMod 112016123)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (56008061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (56008061, 1)] : List FactorBlock).map factorBlockValue).prod) = 112016123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_56008061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 112016123) ^ 56008061 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 112016123) ^ 2 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_126251557 : Nat.Prime 126251557 := by
  apply lucas_primality 126251557 (2 : ZMod 126251557)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (10520963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (10520963, 1)] : List FactorBlock).map factorBlockValue).prod) = 126251557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_10520963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 126251557) ^ 63125778 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 126251557) ^ 42083852 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 126251557) ^ 12 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_129320047 : Nat.Prime 129320047 := by
  apply lucas_primality 129320047 (5 : ZMod 129320047)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7184447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7184447, 1)] : List FactorBlock).map factorBlockValue).prod) = 129320047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_7184447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 129320047) ^ 64660023 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 129320047) ^ 43106682 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 129320047) ^ 18 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_144328297 : Nat.Prime 144328297 := by
  apply lucas_primality 144328297 (5 : ZMod 144328297)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (43, 1), (19979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (43, 1), (19979, 1)] : List FactorBlock).map factorBlockValue).prod) = 144328297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_43
      · exact prime_sixtyThreeBI_19979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 144328297) ^ 72164148 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 144328297) ^ 48109432 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 144328297) ^ 20618328 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 144328297) ^ 3356472 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 144328297) ^ 7224 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_150774847 : Nat.Prime 150774847 := by
  apply lucas_primality 150774847 (3 : ZMod 150774847)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (499, 1), (50359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (499, 1), (50359, 1)] : List FactorBlock).map factorBlockValue).prod) = 150774847 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_499
      · exact prime_sixtyThreeBI_50359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 150774847) ^ 75387423 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 150774847) ^ 50258282 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 150774847) ^ 302154 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 150774847) ^ 2994 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_151251283 : Nat.Prime 151251283 := by
  apply lucas_primality 151251283 (3 : ZMod 151251283)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (13, 2), (7103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (13, 2), (7103, 1)] : List FactorBlock).map factorBlockValue).prod) = 151251283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_13
      · exact prime_sixtyThreeBI_7103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 151251283) ^ 75625641 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 151251283) ^ 50417094 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 151251283) ^ 21607326 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 151251283) ^ 11634714 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 151251283) ^ 21294 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_156121513 : Nat.Prime 156121513 := by
  apply lucas_primality 156121513 (5 : ZMod 156121513)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (6505063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (6505063, 1)] : List FactorBlock).map factorBlockValue).prod) = 156121513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_6505063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 156121513) ^ 78060756 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 156121513) ^ 52040504 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 156121513) ^ 24 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_156948313 : Nat.Prime 156948313 := by
  apply lucas_primality 156948313 (5 : ZMod 156948313)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (6539513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (6539513, 1)] : List FactorBlock).map factorBlockValue).prod) = 156948313 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_6539513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 156948313) ^ 78474156 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 156948313) ^ 52316104 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 156948313) ^ 24 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_164509159 : Nat.Prime 164509159 := by
  apply lucas_primality 164509159 (3 : ZMod 164509159)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (2492563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (2492563, 1)] : List FactorBlock).map factorBlockValue).prod) = 164509159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_11
      · exact prime_sixtyThreeBI_2492563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 164509159) ^ 82254579 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 164509159) ^ 54836386 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 164509159) ^ 14955378 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 164509159) ^ 66 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_171766531 : Nat.Prime 171766531 := by
  apply lucas_primality 171766531 (2 : ZMod 171766531)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (13, 2), (23, 1), (491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (13, 2), (23, 1), (491, 1)] : List FactorBlock).map factorBlockValue).prod) = 171766531 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_13
      · exact prime_sixtyThreeBI_23
      · exact prime_sixtyThreeBI_491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 171766531) ^ 85883265 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 171766531) ^ 57255510 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 171766531) ^ 34353306 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 171766531) ^ 13212810 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 171766531) ^ 7468110 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 171766531) ^ 349830 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_174042031 : Nat.Prime 174042031 := by
  apply lucas_primality 174042031 (3 : ZMod 174042031)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (5801401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (5801401, 1)] : List FactorBlock).map factorBlockValue).prod) = 174042031 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_5801401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 174042031) ^ 87021015 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 174042031) ^ 58014010 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 174042031) ^ 34808406 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 174042031) ^ 30 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_193872893 : Nat.Prime 193872893 := by
  apply lucas_primality 193872893 (2 : ZMod 193872893)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (48468223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (48468223, 1)] : List FactorBlock).map factorBlockValue).prod) = 193872893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_48468223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 193872893) ^ 96936446 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 193872893) ^ 4 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_200339837 : Nat.Prime 200339837 := by
  apply lucas_primality 200339837 (2 : ZMod 200339837)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (50084959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (50084959, 1)] : List FactorBlock).map factorBlockValue).prod) = 200339837 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_50084959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 200339837) ^ 100169918 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 200339837) ^ 4 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_229490111 : Nat.Prime 229490111 := by
  apply lucas_primality 229490111 (7 : ZMod 229490111)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (22949011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (22949011, 1)] : List FactorBlock).map factorBlockValue).prod) = 229490111 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_22949011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 229490111) ^ 114745055 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 229490111) ^ 45898022 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 229490111) ^ 10 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_233884247 : Nat.Prime 233884247 := by
  apply lucas_primality 233884247 (5 : ZMod 233884247)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (347, 1), (11621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (347, 1), (11621, 1)] : List FactorBlock).map factorBlockValue).prod) = 233884247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_29
      · exact prime_sixtyThreeBI_347
      · exact prime_sixtyThreeBI_11621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 233884247) ^ 116942123 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 233884247) ^ 8064974 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 233884247) ^ 674018 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 233884247) ^ 20126 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_246142033 : Nat.Prime 246142033 := by
  apply lucas_primality 246142033 (5 : ZMod 246142033)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (439, 1), (11681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (439, 1), (11681, 1)] : List FactorBlock).map factorBlockValue).prod) = 246142033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_439
      · exact prime_sixtyThreeBI_11681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 246142033) ^ 123071016 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 246142033) ^ 82047344 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 246142033) ^ 560688 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 246142033) ^ 21072 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_258407257 : Nat.Prime 258407257 := by
  apply lucas_primality 258407257 (5 : ZMod 258407257)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (41, 1), (59, 1), (4451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (41, 1), (59, 1), (4451, 1)] : List FactorBlock).map factorBlockValue).prod) = 258407257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_41
      · exact prime_sixtyThreeBI_59
      · exact prime_sixtyThreeBI_4451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 258407257) ^ 129203628 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 258407257) ^ 86135752 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 258407257) ^ 6302616 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 258407257) ^ 4379784 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 258407257) ^ 58056 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_258446687 : Nat.Prime 258446687 := by
  apply lucas_primality 258446687 (5 : ZMod 258446687)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (193, 1), (669551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (193, 1), (669551, 1)] : List FactorBlock).map factorBlockValue).prod) = 258446687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_193
      · exact prime_sixtyThreeBI_669551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 258446687) ^ 129223343 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 258446687) ^ 1339102 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 258446687) ^ 386 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_286665157 : Nat.Prime 286665157 := by
  apply lucas_primality 286665157 (2 : ZMod 286665157)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 5), (294923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 5), (294923, 1)] : List FactorBlock).map factorBlockValue).prod) = 286665157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_294923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 286665157) ^ 143332578 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 286665157) ^ 95555052 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 286665157) ^ 972 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_346061867 : Nat.Prime 346061867 := by
  apply lucas_primality 346061867 (2 : ZMod 346061867)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 2), (180053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 2), (180053, 1)] : List FactorBlock).map factorBlockValue).prod) = 346061867 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_31
      · exact prime_sixtyThreeBI_180053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 346061867) ^ 173030933 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 346061867) ^ 11163286 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 346061867) ^ 1922 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_403459883 : Nat.Prime 403459883 := by
  apply lucas_primality 403459883 (5 : ZMod 403459883)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (23, 1), (163, 1), (7687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (23, 1), (163, 1), (7687, 1)] : List FactorBlock).map factorBlockValue).prod) = 403459883 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_23
      · exact prime_sixtyThreeBI_163
      · exact prime_sixtyThreeBI_7687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 403459883) ^ 201729941 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 403459883) ^ 57637126 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 403459883) ^ 17541734 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 403459883) ^ 2475214 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 403459883) ^ 52486 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_411605231 : Nat.Prime 411605231 := by
  apply lucas_primality 411605231 (7 : ZMod 411605231)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (2689, 1), (15307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (2689, 1), (15307, 1)] : List FactorBlock).map factorBlockValue).prod) = 411605231 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_2689
      · exact prime_sixtyThreeBI_15307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 411605231) ^ 205802615 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 411605231) ^ 82321046 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 411605231) ^ 153070 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 411605231) ^ 26890 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_415733743 : Nat.Prime 415733743 := by
  apply lucas_primality 415733743 (3 : ZMod 415733743)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (17, 1), (452869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (17, 1), (452869, 1)] : List FactorBlock).map factorBlockValue).prod) = 415733743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_17
      · exact prime_sixtyThreeBI_452869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 415733743) ^ 207866871 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 415733743) ^ 138577914 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 415733743) ^ 24454926 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 415733743) ^ 918 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_468558613 : Nat.Prime 468558613 := by
  apply lucas_primality 468558613 (2 : ZMod 468558613)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13015517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13015517, 1)] : List FactorBlock).map factorBlockValue).prod) = 468558613 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_13015517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 468558613) ^ 234279306 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 468558613) ^ 156186204 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 468558613) ^ 36 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_486858187 : Nat.Prime 486858187 := by
  apply lucas_primality 486858187 (2 : ZMod 486858187)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (27047677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (27047677, 1)] : List FactorBlock).map factorBlockValue).prod) = 486858187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_27047677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 486858187) ^ 243429093 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 486858187) ^ 162286062 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 486858187) ^ 18 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_507169501 : Nat.Prime 507169501 := by
  apply lucas_primality 507169501 (2 : ZMod 507169501)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 3), (17, 1), (19889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 3), (17, 1), (19889, 1)] : List FactorBlock).map factorBlockValue).prod) = 507169501 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_17
      · exact prime_sixtyThreeBI_19889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 507169501) ^ 253584750 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 507169501) ^ 169056500 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 507169501) ^ 101433900 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 507169501) ^ 29833500 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 507169501) ^ 25500 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_561557063 : Nat.Prime 561557063 := by
  apply lucas_primality 561557063 (5 : ZMod 561557063)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (25525321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (25525321, 1)] : List FactorBlock).map factorBlockValue).prod) = 561557063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_11
      · exact prime_sixtyThreeBI_25525321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 561557063) ^ 280778531 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 561557063) ^ 51050642 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 561557063) ^ 22 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_672096739 : Nat.Prime 672096739 := by
  apply lucas_primality 672096739 (3 : ZMod 672096739)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (112016123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (112016123, 1)] : List FactorBlock).map factorBlockValue).prod) = 672096739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_112016123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 672096739) ^ 336048369 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 672096739) ^ 224032246 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 672096739) ^ 6 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_703318097 : Nat.Prime 703318097 := by
  apply lucas_primality 703318097 (3 : ZMod 703318097)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (83, 1), (40739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (83, 1), (40739, 1)] : List FactorBlock).map factorBlockValue).prod) = 703318097 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_13
      · exact prime_sixtyThreeBI_83
      · exact prime_sixtyThreeBI_40739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 703318097) ^ 351659048 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 703318097) ^ 54101392 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 703318097) ^ 8473712 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 703318097) ^ 17264 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_823210463 : Nat.Prime 823210463 := by
  apply lucas_primality 823210463 (5 : ZMod 823210463)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (411605231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (411605231, 1)] : List FactorBlock).map factorBlockValue).prod) = 823210463 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_411605231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 823210463) ^ 411605231 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 823210463) ^ 2 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_825427819 : Nat.Prime 825427819 := by
  apply lucas_primality 825427819 (3 : ZMod 825427819)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (23, 1), (47, 1), (59, 1), (719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (23, 1), (47, 1), (59, 1), (719, 1)] : List FactorBlock).map factorBlockValue).prod) = 825427819 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_23
      · exact prime_sixtyThreeBI_47
      · exact prime_sixtyThreeBI_59
      · exact prime_sixtyThreeBI_719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 825427819) ^ 412713909 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 825427819) ^ 275142606 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 825427819) ^ 35888166 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 825427819) ^ 17562294 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 825427819) ^ 13990302 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 825427819) ^ 1148022 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_829544977 : Nat.Prime 829544977 := by
  apply lucas_primality 829544977 (5 : ZMod 829544977)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (13, 1), (53, 1), (929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (13, 1), (53, 1), (929, 1)] : List FactorBlock).map factorBlockValue).prod) = 829544977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_13
      · exact prime_sixtyThreeBI_53
      · exact prime_sixtyThreeBI_929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 829544977) ^ 414772488 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 829544977) ^ 276514992 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 829544977) ^ 63811152 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 829544977) ^ 15651792 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 829544977) ^ 892944 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_1067176997 : Nat.Prime 1067176997 := by
  apply lucas_primality 1067176997 (2 : ZMod 1067176997)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (433, 1), (616153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (433, 1), (616153, 1)] : List FactorBlock).map factorBlockValue).prod) = 1067176997 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_433
      · exact prime_sixtyThreeBI_616153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1067176997) ^ 533588498 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1067176997) ^ 2464612 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1067176997) ^ 1732 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_1098731723 : Nat.Prime 1098731723 := by
  apply lucas_primality 1098731723 (2 : ZMod 1098731723)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (49942351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (49942351, 1)] : List FactorBlock).map factorBlockValue).prod) = 1098731723 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_11
      · exact prime_sixtyThreeBI_49942351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1098731723) ^ 549365861 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1098731723) ^ 99884702 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1098731723) ^ 22 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_1344071269 : Nat.Prime 1344071269 := by
  apply lucas_primality 1344071269 (2 : ZMod 1344071269)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (113, 1), (163, 1), (2027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (113, 1), (163, 1), (2027, 1)] : List FactorBlock).map factorBlockValue).prod) = 1344071269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_113
      · exact prime_sixtyThreeBI_163
      · exact prime_sixtyThreeBI_2027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1344071269) ^ 672035634 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1344071269) ^ 448023756 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1344071269) ^ 11894436 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1344071269) ^ 8245836 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1344071269) ^ 663084 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_2018947949 : Nat.Prime 2018947949 := by
  apply lucas_primality 2018947949 (2 : ZMod 2018947949)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (113, 1), (262747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (113, 1), (262747, 1)] : List FactorBlock).map factorBlockValue).prod) = 2018947949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_17
      · exact prime_sixtyThreeBI_113
      · exact prime_sixtyThreeBI_262747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2018947949) ^ 1009473974 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2018947949) ^ 118761644 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2018947949) ^ 17866796 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2018947949) ^ 7684 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_2258514943 : Nat.Prime 2258514943 := by
  apply lucas_primality 2258514943 (3 : ZMod 2258514943)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2729, 1), (137933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2729, 1), (137933, 1)] : List FactorBlock).map factorBlockValue).prod) = 2258514943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_2729
      · exact prime_sixtyThreeBI_137933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2258514943) ^ 1129257471 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2258514943) ^ 752838314 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2258514943) ^ 827598 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2258514943) ^ 16374 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_2520571019 : Nat.Prime 2520571019 := by
  apply lucas_primality 2520571019 (2 : ZMod 2520571019)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (29, 1), (6208303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (29, 1), (6208303, 1)] : List FactorBlock).map factorBlockValue).prod) = 2520571019 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_29
      · exact prime_sixtyThreeBI_6208303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2520571019) ^ 1260285509 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2520571019) ^ 360081574 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2520571019) ^ 86916242 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2520571019) ^ 406 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_2526377551 : Nat.Prime 2526377551 := by
  apply lucas_primality 2526377551 (3 : ZMod 2526377551)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (31, 1), (543307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (31, 1), (543307, 1)] : List FactorBlock).map factorBlockValue).prod) = 2526377551 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_31
      · exact prime_sixtyThreeBI_543307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2526377551) ^ 1263188775 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2526377551) ^ 842125850 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2526377551) ^ 505275510 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2526377551) ^ 81496050 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2526377551) ^ 4650 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_2745740579 : Nat.Prime 2745740579 := by
  apply lucas_primality 2745740579 (2 : ZMod 2745740579)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (19, 1), (53, 1), (27823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (19, 1), (53, 1), (27823, 1)] : List FactorBlock).map factorBlockValue).prod) = 2745740579 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_19
      · exact prime_sixtyThreeBI_53
      · exact prime_sixtyThreeBI_27823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2745740579) ^ 1372870289 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2745740579) ^ 392248654 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2745740579) ^ 144512662 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2745740579) ^ 51806426 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2745740579) ^ 98686 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_2819237329 : Nat.Prime 2819237329 := by
  apply lucas_primality 2819237329 (7 : ZMod 2819237329)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (19, 1), (23, 1), (71, 1), (631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (19, 1), (23, 1), (71, 1), (631, 1)] : List FactorBlock).map factorBlockValue).prod) = 2819237329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_19
      · exact prime_sixtyThreeBI_23
      · exact prime_sixtyThreeBI_71
      · exact prime_sixtyThreeBI_631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2819237329) ^ 1409618664 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 2819237329) ^ 939745776 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 2819237329) ^ 148380912 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 2819237329) ^ 122575536 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 2819237329) ^ 39707568 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 2819237329) ^ 4467888 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_3050698319 : Nat.Prime 3050698319 := by
  apply lucas_primality 3050698319 (7 : ZMod 3050698319)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (317, 1), (1811, 1), (2657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (317, 1), (1811, 1), (2657, 1)] : List FactorBlock).map factorBlockValue).prod) = 3050698319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_317
      · exact prime_sixtyThreeBI_1811
      · exact prime_sixtyThreeBI_2657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 3050698319) ^ 1525349159 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 3050698319) ^ 9623654 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 3050698319) ^ 1684538 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 3050698319) ^ 1148174 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_3281488673 : Nat.Prime 3281488673 := by
  apply lucas_primality 3281488673 (5 : ZMod 3281488673)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (11, 1), (1331773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (11, 1), (1331773, 1)] : List FactorBlock).map factorBlockValue).prod) = 3281488673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_11
      · exact prime_sixtyThreeBI_1331773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3281488673) ^ 1640744336 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 3281488673) ^ 468784096 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 3281488673) ^ 298317152 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 3281488673) ^ 2464 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_3343068541 : Nat.Prime 3343068541 := by
  apply lucas_primality 3343068541 (2 : ZMod 3343068541)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (7, 1), (43, 1), (61703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (7, 1), (43, 1), (61703, 1)] : List FactorBlock).map factorBlockValue).prod) = 3343068541 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_43
      · exact prime_sixtyThreeBI_61703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3343068541) ^ 1671534270 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3343068541) ^ 1114356180 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3343068541) ^ 668613708 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3343068541) ^ 477581220 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3343068541) ^ 77745780 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3343068541) ^ 54180 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_3822161009 : Nat.Prime 3822161009 := by
  apply lucas_primality 3822161009 (3 : ZMod 3822161009)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (1487, 1), (160649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (1487, 1), (160649, 1)] : List FactorBlock).map factorBlockValue).prod) = 3822161009 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_1487
      · exact prime_sixtyThreeBI_160649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3822161009) ^ 1911080504 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 3822161009) ^ 2570384 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 3822161009) ^ 23792 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_3892054669 : Nat.Prime 3892054669 := by
  apply lucas_primality 3892054669 (2 : ZMod 3892054669)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (163, 1), (1989803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (163, 1), (1989803, 1)] : List FactorBlock).map factorBlockValue).prod) = 3892054669 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_163
      · exact prime_sixtyThreeBI_1989803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3892054669) ^ 1946027334 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3892054669) ^ 1297351556 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3892054669) ^ 23877636 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3892054669) ^ 1956 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_3922744937 : Nat.Prime 3922744937 := by
  apply lucas_primality 3922744937 (3 : ZMod 3922744937)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (73, 1), (610639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (73, 1), (610639, 1)] : List FactorBlock).map factorBlockValue).prod) = 3922744937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_11
      · exact prime_sixtyThreeBI_73
      · exact prime_sixtyThreeBI_610639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3922744937) ^ 1961372468 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 3922744937) ^ 356613176 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 3922744937) ^ 53736232 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 3922744937) ^ 6424 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_4037895899 : Nat.Prime 4037895899 := by
  apply lucas_primality 4037895899 (2 : ZMod 4037895899)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2018947949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2018947949, 1)] : List FactorBlock).map factorBlockValue).prod) = 4037895899 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_2018947949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 4037895899) ^ 2018947949 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4037895899) ^ 2 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_4523245411 : Nat.Prime 4523245411 := by
  apply lucas_primality 4523245411 (2 : ZMod 4523245411)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (150774847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (150774847, 1)] : List FactorBlock).map factorBlockValue).prod) = 4523245411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_150774847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4523245411) ^ 2261622705 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4523245411) ^ 1507748470 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4523245411) ^ 904649082 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4523245411) ^ 30 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_4936890589 : Nat.Prime 4936890589 := by
  apply lucas_primality 4936890589 (2 : ZMod 4936890589)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (58772507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (58772507, 1)] : List FactorBlock).map factorBlockValue).prod) = 4936890589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_58772507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4936890589) ^ 2468445294 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4936890589) ^ 1645630196 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4936890589) ^ 705270084 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4936890589) ^ 84 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_5035141847 : Nat.Prime 5035141847 := by
  apply lucas_primality 5035141847 (10 : ZMod 5035141847)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (43, 1), (8364023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (43, 1), (8364023, 1)] : List FactorBlock).map factorBlockValue).prod) = 5035141847 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_43
      · exact prime_sixtyThreeBI_8364023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 5035141847) ^ 2517570923 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (10 : ZMod 5035141847) ^ 719305978 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (10 : ZMod 5035141847) ^ 117096322 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (10 : ZMod 5035141847) ^ 602 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_6625308577 : Nat.Prime 6625308577 := by
  apply lucas_primality 6625308577 (5 : ZMod 6625308577)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (61, 1), (197, 1), (5743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (61, 1), (197, 1), (5743, 1)] : List FactorBlock).map factorBlockValue).prod) = 6625308577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_61
      · exact prime_sixtyThreeBI_197
      · exact prime_sixtyThreeBI_5743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6625308577) ^ 3312654288 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 6625308577) ^ 2208436192 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 6625308577) ^ 108611616 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 6625308577) ^ 33631008 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 6625308577) ^ 1153632 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_6982713469 : Nat.Prime 6982713469 := by
  apply lucas_primality 6982713469 (2 : ZMod 6982713469)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (67, 1), (2894989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (67, 1), (2894989, 1)] : List FactorBlock).map factorBlockValue).prod) = 6982713469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_67
      · exact prime_sixtyThreeBI_2894989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6982713469) ^ 3491356734 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6982713469) ^ 2327571156 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6982713469) ^ 104219604 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6982713469) ^ 2412 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_9825613669 : Nat.Prime 9825613669 := by
  apply lucas_primality 9825613669 (2 : ZMod 9825613669)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (20994901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (20994901, 1)] : List FactorBlock).map factorBlockValue).prod) = 9825613669 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_13
      · exact prime_sixtyThreeBI_20994901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9825613669) ^ 4912806834 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9825613669) ^ 3275204556 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9825613669) ^ 755816436 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9825613669) ^ 468 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_10705646383 : Nat.Prime 10705646383 := by
  apply lucas_primality 10705646383 (5 : ZMod 10705646383)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (199, 1), (8966203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (199, 1), (8966203, 1)] : List FactorBlock).map factorBlockValue).prod) = 10705646383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_199
      · exact prime_sixtyThreeBI_8966203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 10705646383) ^ 5352823191 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 10705646383) ^ 3568548794 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 10705646383) ^ 53797218 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 10705646383) ^ 1194 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_12048897911 : Nat.Prime 12048897911 := by
  apply lucas_primality 12048897911 (7 : ZMod 12048897911)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (47, 1), (421, 1), (8699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (47, 1), (421, 1), (8699, 1)] : List FactorBlock).map factorBlockValue).prod) = 12048897911 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_47
      · exact prime_sixtyThreeBI_421
      · exact prime_sixtyThreeBI_8699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 12048897911) ^ 6024448955 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 12048897911) ^ 2409779582 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 12048897911) ^ 1721271130 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 12048897911) ^ 256359530 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 12048897911) ^ 28619710 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 12048897911) ^ 1385090 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_12558520841 : Nat.Prime 12558520841 := by
  apply lucas_primality 12558520841 (7 : ZMod 12558520841)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (17, 1), (83, 1), (222511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (17, 1), (83, 1), (222511, 1)] : List FactorBlock).map factorBlockValue).prod) = 12558520841 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_17
      · exact prime_sixtyThreeBI_83
      · exact prime_sixtyThreeBI_222511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 12558520841) ^ 6279260420 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 12558520841) ^ 2511704168 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 12558520841) ^ 738736520 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 12558520841) ^ 151307480 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 12558520841) ^ 56440 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_13173819907 : Nat.Prime 13173819907 := by
  apply lucas_primality 13173819907 (3 : ZMod 13173819907)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (79, 1), (2137913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (79, 1), (2137913, 1)] : List FactorBlock).map factorBlockValue).prod) = 13173819907 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_13
      · exact prime_sixtyThreeBI_79
      · exact prime_sixtyThreeBI_2137913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13173819907) ^ 6586909953 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 13173819907) ^ 4391273302 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 13173819907) ^ 1013370762 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 13173819907) ^ 166757214 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 13173819907) ^ 6162 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_13316000491 : Nat.Prime 13316000491 := by
  apply lucas_primality 13316000491 (2 : ZMod 13316000491)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (13, 1), (43, 1), (61, 1), (4339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (13, 1), (43, 1), (61, 1), (4339, 1)] : List FactorBlock).map factorBlockValue).prod) = 13316000491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_13
      · exact prime_sixtyThreeBI_43
      · exact prime_sixtyThreeBI_61
      · exact prime_sixtyThreeBI_4339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13316000491) ^ 6658000245 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 13316000491) ^ 4438666830 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 13316000491) ^ 2663200098 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 13316000491) ^ 1024307730 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 13316000491) ^ 309674430 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 13316000491) ^ 218295090 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 13316000491) ^ 3068910 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_14556856247 : Nat.Prime 14556856247 := by
  apply lucas_primality 14556856247 (5 : ZMod 14556856247)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (911, 1), (7989493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (911, 1), (7989493, 1)] : List FactorBlock).map factorBlockValue).prod) = 14556856247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_911
      · exact prime_sixtyThreeBI_7989493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 14556856247) ^ 7278428123 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 14556856247) ^ 15978986 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 14556856247) ^ 1822 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_14894851793 : Nat.Prime 14894851793 := by
  apply lucas_primality 14894851793 (3 : ZMod 14894851793)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (19, 1), (1033, 1), (47431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (19, 1), (1033, 1), (47431, 1)] : List FactorBlock).map factorBlockValue).prod) = 14894851793 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_19
      · exact prime_sixtyThreeBI_1033
      · exact prime_sixtyThreeBI_47431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 14894851793) ^ 7447425896 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 14894851793) ^ 783939568 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 14894851793) ^ 14419024 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 14894851793) ^ 314032 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_14970455251 : Nat.Prime 14970455251 := by
  apply lucas_primality 14970455251 (2 : ZMod 14970455251)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (269, 1), (74203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (269, 1), (74203, 1)] : List FactorBlock).map factorBlockValue).prod) = 14970455251 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_269
      · exact prime_sixtyThreeBI_74203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14970455251) ^ 7485227625 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 14970455251) ^ 4990151750 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 14970455251) ^ 2994091050 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 14970455251) ^ 55652250 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 14970455251) ^ 201750 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_14987665249 : Nat.Prime 14987665249 := by
  apply lucas_primality 14987665249 (13 : ZMod 14987665249)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (156121513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (156121513, 1)] : List FactorBlock).map factorBlockValue).prod) = 14987665249 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_156121513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 14987665249) ^ 7493832624 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (13 : ZMod 14987665249) ^ 4995888416 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (13 : ZMod 14987665249) ^ 96 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_16826145547 : Nat.Prime 16826145547 := by
  apply lucas_primality 16826145547 (2 : ZMod 16826145547)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (97, 1), (4130129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (97, 1), (4130129, 1)] : List FactorBlock).map factorBlockValue).prod) = 16826145547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_97
      · exact prime_sixtyThreeBI_4130129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16826145547) ^ 8413072773 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 16826145547) ^ 5608715182 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 16826145547) ^ 2403735078 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 16826145547) ^ 173465418 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 16826145547) ^ 4074 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_17829683503 : Nat.Prime 17829683503 := by
  apply lucas_primality 17829683503 (3 : ZMod 17829683503)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (109, 1), (27262513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (109, 1), (27262513, 1)] : List FactorBlock).map factorBlockValue).prod) = 17829683503 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_109
      · exact prime_sixtyThreeBI_27262513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 17829683503) ^ 8914841751 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 17829683503) ^ 5943227834 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 17829683503) ^ 163575078 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 17829683503) ^ 654 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_18946680341 : Nat.Prime 18946680341 := by
  apply lucas_primality 18946680341 (3 : ZMod 18946680341)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (1187, 1), (114013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (1187, 1), (114013, 1)] : List FactorBlock).map factorBlockValue).prod) = 18946680341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_1187
      · exact prime_sixtyThreeBI_114013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 18946680341) ^ 9473340170 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 18946680341) ^ 3789336068 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 18946680341) ^ 2706668620 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 18946680341) ^ 15961820 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 18946680341) ^ 166180 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_21343539941 : Nat.Prime 21343539941 := by
  apply lucas_primality 21343539941 (2 : ZMod 21343539941)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1067176997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1067176997, 1)] : List FactorBlock).map factorBlockValue).prod) = 21343539941 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_1067176997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 21343539941) ^ 10671769970 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 21343539941) ^ 4268707988 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 21343539941) ^ 20 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_23536469623 : Nat.Prime 23536469623 := by
  apply lucas_primality 23536469623 (3 : ZMod 23536469623)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3922744937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3922744937, 1)] : List FactorBlock).map factorBlockValue).prod) = 23536469623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_3922744937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 23536469623) ^ 11768234811 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 23536469623) ^ 7845489874 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 23536469623) ^ 6 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_23585396647 : Nat.Prime 23585396647 := by
  apply lucas_primality 23585396647 (7 : ZMod 23585396647)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (561557063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (561557063, 1)] : List FactorBlock).map factorBlockValue).prod) = 23585396647 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_561557063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 23585396647) ^ 11792698323 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 23585396647) ^ 7861798882 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 23585396647) ^ 3369342378 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 23585396647) ^ 42 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_26883869561 : Nat.Prime 26883869561 := by
  apply lucas_primality 26883869561 (3 : ZMod 26883869561)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (672096739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (672096739, 1)] : List FactorBlock).map factorBlockValue).prod) = 26883869561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_672096739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 26883869561) ^ 13441934780 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 26883869561) ^ 5376773912 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 26883869561) ^ 40 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_27139472467 : Nat.Prime 27139472467 := by
  apply lucas_primality 27139472467 (2 : ZMod 27139472467)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4523245411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4523245411, 1)] : List FactorBlock).map factorBlockValue).prod) = 27139472467 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_4523245411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 27139472467) ^ 13569736233 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 27139472467) ^ 9046490822 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 27139472467) ^ 6 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_28914409409 : Nat.Prime 28914409409 := by
  apply lucas_primality 28914409409 (3 : ZMod 28914409409)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (307, 1), (1471621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (307, 1), (1471621, 1)] : List FactorBlock).map factorBlockValue).prod) = 28914409409 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_307
      · exact prime_sixtyThreeBI_1471621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 28914409409) ^ 14457204704 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 28914409409) ^ 94183744 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 28914409409) ^ 19648 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_29049111577 : Nat.Prime 29049111577 := by
  apply lucas_primality 29049111577 (5 : ZMod 29049111577)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (403459883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (403459883, 1)] : List FactorBlock).map factorBlockValue).prod) = 29049111577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_403459883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 29049111577) ^ 14524555788 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 29049111577) ^ 9683037192 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 29049111577) ^ 72 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_30900284707 : Nat.Prime 30900284707 := by
  apply lucas_primality 30900284707 (3 : ZMod 30900284707)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (281, 1), (964609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (281, 1), (964609, 1)] : List FactorBlock).map factorBlockValue).prod) = 30900284707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_19
      · exact prime_sixtyThreeBI_281
      · exact prime_sixtyThreeBI_964609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 30900284707) ^ 15450142353 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 30900284707) ^ 10300094902 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 30900284707) ^ 1626330774 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 30900284707) ^ 109965426 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 30900284707) ^ 32034 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_31149414689 : Nat.Prime 31149414689 := by
  apply lucas_primality 31149414689 (3 : ZMod 31149414689)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (47, 1), (2958721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (47, 1), (2958721, 1)] : List FactorBlock).map factorBlockValue).prod) = 31149414689 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_47
      · exact prime_sixtyThreeBI_2958721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 31149414689) ^ 15574707344 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 31149414689) ^ 4449916384 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 31149414689) ^ 662753504 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 31149414689) ^ 10528 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_33418359659 : Nat.Prime 33418359659 := by
  apply lucas_primality 33418359659 (2 : ZMod 33418359659)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (157, 1), (106427897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (157, 1), (106427897, 1)] : List FactorBlock).map factorBlockValue).prod) = 33418359659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_157
      · exact prime_sixtyThreeBI_106427897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 33418359659) ^ 16709179829 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 33418359659) ^ 212855794 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 33418359659) ^ 314 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_39302454677 : Nat.Prime 39302454677 := by
  apply lucas_primality 39302454677 (2 : ZMod 39302454677)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (9825613669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (9825613669, 1)] : List FactorBlock).map factorBlockValue).prod) = 39302454677 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_9825613669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 39302454677) ^ 19651227338 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 39302454677) ^ 4 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_39784282477 : Nat.Prime 39784282477 := by
  apply lucas_primality 39784282477 (2 : ZMod 39784282477)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (23, 1), (7586629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (23, 1), (7586629, 1)] : List FactorBlock).map factorBlockValue).prod) = 39784282477 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_19
      · exact prime_sixtyThreeBI_23
      · exact prime_sixtyThreeBI_7586629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 39784282477) ^ 19892141238 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 39784282477) ^ 13261427492 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 39784282477) ^ 2093909604 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 39784282477) ^ 1729751412 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 39784282477) ^ 5244 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_60485356343 : Nat.Prime 60485356343 := by
  apply lucas_primality 60485356343 (5 : ZMod 60485356343)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (703318097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (703318097, 1)] : List FactorBlock).map factorBlockValue).prod) = 60485356343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_43
      · exact prime_sixtyThreeBI_703318097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 60485356343) ^ 30242678171 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 60485356343) ^ 1406636194 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 60485356343) ^ 86 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_61249593631 : Nat.Prime 61249593631 := by
  apply lucas_primality 61249593631 (3 : ZMod 61249593631)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (23, 1), (53, 1), (383, 1), (4373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (23, 1), (53, 1), (383, 1), (4373, 1)] : List FactorBlock).map factorBlockValue).prod) = 61249593631 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_23
      · exact prime_sixtyThreeBI_53
      · exact prime_sixtyThreeBI_383
      · exact prime_sixtyThreeBI_4373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 61249593631) ^ 30624796815 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 61249593631) ^ 20416531210 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 61249593631) ^ 12249918726 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 61249593631) ^ 2663025810 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 61249593631) ^ 1155652710 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 61249593631) ^ 159920610 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 61249593631) ^ 14006310 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_74687158187 : Nat.Prime 74687158187 := by
  apply lucas_primality 74687158187 (2 : ZMod 74687158187)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (227, 1), (164509159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (227, 1), (164509159, 1)] : List FactorBlock).map factorBlockValue).prod) = 74687158187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_227
      · exact prime_sixtyThreeBI_164509159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 74687158187) ^ 37343579093 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 74687158187) ^ 329018318 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 74687158187) ^ 454 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_83157263963 : Nat.Prime 83157263963 := by
  apply lucas_primality 83157263963 (2 : ZMod 83157263963)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (127, 1), (14563, 1), (22481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (127, 1), (14563, 1), (22481, 1)] : List FactorBlock).map factorBlockValue).prod) = 83157263963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_127
      · exact prime_sixtyThreeBI_14563
      · exact prime_sixtyThreeBI_22481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 83157263963) ^ 41578631981 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 83157263963) ^ 654781606 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 83157263963) ^ 5710174 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 83157263963) ^ 3699002 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_100431676487 : Nat.Prime 100431676487 := by
  apply lucas_primality 100431676487 (5 : ZMod 100431676487)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (823210463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (823210463, 1)] : List FactorBlock).map factorBlockValue).prod) = 100431676487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_61
      · exact prime_sixtyThreeBI_823210463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 100431676487) ^ 50215838243 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 100431676487) ^ 1646420926 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 100431676487) ^ 122 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_107628310121 : Nat.Prime 107628310121 := by
  apply lucas_primality 107628310121 (3 : ZMod 107628310121)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (1847, 1), (1456799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (1847, 1), (1456799, 1)] : List FactorBlock).map factorBlockValue).prod) = 107628310121 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_1847
      · exact prime_sixtyThreeBI_1456799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 107628310121) ^ 53814155060 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 107628310121) ^ 21525662024 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 107628310121) ^ 58271960 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 107628310121) ^ 73880 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_116349974693 : Nat.Prime 116349974693 := by
  apply lucas_primality 116349974693 (3 : ZMod 116349974693)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (83, 1), (4903, 1), (10211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (83, 1), (4903, 1), (10211, 1)] : List FactorBlock).map factorBlockValue).prod) = 116349974693 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_83
      · exact prime_sixtyThreeBI_4903
      · exact prime_sixtyThreeBI_10211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 116349974693) ^ 58174987346 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 116349974693) ^ 16621424956 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 116349974693) ^ 1401806924 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 116349974693) ^ 23730364 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 116349974693) ^ 11394572 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_132329858747 : Nat.Prime 132329858747 := by
  apply lucas_primality 132329858747 (2 : ZMod 132329858747)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (3892054669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (3892054669, 1)] : List FactorBlock).map factorBlockValue).prod) = 132329858747 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_17
      · exact prime_sixtyThreeBI_3892054669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 132329858747) ^ 66164929373 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 132329858747) ^ 7784109338 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 132329858747) ^ 34 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_137287028951 : Nat.Prime 137287028951 := by
  apply lucas_primality 137287028951 (7 : ZMod 137287028951)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (2745740579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (2745740579, 1)] : List FactorBlock).map factorBlockValue).prod) = 137287028951 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_2745740579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 137287028951) ^ 68643514475 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 137287028951) ^ 27457405790 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 137287028951) ^ 50 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_147661005553 : Nat.Prime 147661005553 := by
  apply lucas_primality 147661005553 (7 : ZMod 147661005553)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (173, 1), (2237, 1), (7949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (173, 1), (2237, 1), (7949, 1)] : List FactorBlock).map factorBlockValue).prod) = 147661005553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_173
      · exact prime_sixtyThreeBI_2237
      · exact prime_sixtyThreeBI_7949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 147661005553) ^ 73830502776 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 147661005553) ^ 49220335184 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 147661005553) ^ 853531824 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 147661005553) ^ 66008496 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 147661005553) ^ 18576048 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_220645056829 : Nat.Prime 220645056829 := by
  apply lucas_primality 220645056829 (2 : ZMod 220645056829)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (229, 1), (971, 1), (11813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (229, 1), (971, 1), (11813, 1)] : List FactorBlock).map factorBlockValue).prod) = 220645056829 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_229
      · exact prime_sixtyThreeBI_971
      · exact prime_sixtyThreeBI_11813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 220645056829) ^ 110322528414 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 220645056829) ^ 73548352276 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 220645056829) ^ 31520722404 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 220645056829) ^ 963515532 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 220645056829) ^ 227234868 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 220645056829) ^ 18678156 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_249253103251 : Nat.Prime 249253103251 := by
  apply lucas_primality 249253103251 (15 : ZMod 249253103251)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 3), (17, 1), (6516421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 3), (17, 1), (6516421, 1)] : List FactorBlock).map factorBlockValue).prod) = 249253103251 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_17
      · exact prime_sixtyThreeBI_6516421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 249253103251) ^ 124626551625 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (15 : ZMod 249253103251) ^ 83084367750 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (15 : ZMod 249253103251) ^ 49850620650 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (15 : ZMod 249253103251) ^ 14661947250 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (15 : ZMod 249253103251) ^ 38250 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_328913261267 : Nat.Prime 328913261267 := by
  apply lucas_primality 328913261267 (2 : ZMod 328913261267)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (13711, 1), (705559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (13711, 1), (705559, 1)] : List FactorBlock).map factorBlockValue).prod) = 328913261267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_17
      · exact prime_sixtyThreeBI_13711
      · exact prime_sixtyThreeBI_705559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 328913261267) ^ 164456630633 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 328913261267) ^ 19347838898 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 328913261267) ^ 23989006 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 328913261267) ^ 466174 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_368611796299 : Nat.Prime 368611796299 := by
  apply lucas_primality 368611796299 (2 : ZMod 368611796299)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (659, 1), (1553, 1), (60029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (659, 1), (1553, 1), (60029, 1)] : List FactorBlock).map factorBlockValue).prod) = 368611796299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_659
      · exact prime_sixtyThreeBI_1553
      · exact prime_sixtyThreeBI_60029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 368611796299) ^ 184305898149 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 368611796299) ^ 122870598766 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 368611796299) ^ 559350222 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 368611796299) ^ 237354666 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 368611796299) ^ 6140562 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_449292916939 : Nat.Prime 449292916939 := by
  apply lucas_primality 449292916939 (3 : ZMod 449292916939)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (16871, 1), (261089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (16871, 1), (261089, 1)] : List FactorBlock).map factorBlockValue).prod) = 449292916939 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_17
      · exact prime_sixtyThreeBI_16871
      · exact prime_sixtyThreeBI_261089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 449292916939) ^ 224646458469 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 449292916939) ^ 149764305646 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 449292916939) ^ 26428995114 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 449292916939) ^ 26631078 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 449292916939) ^ 1720842 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_501500364901 : Nat.Prime 501500364901 := by
  apply lucas_primality 501500364901 (2 : ZMod 501500364901)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (5953, 1), (280811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (5953, 1), (280811, 1)] : List FactorBlock).map factorBlockValue).prod) = 501500364901 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_5953
      · exact prime_sixtyThreeBI_280811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 501500364901) ^ 250750182450 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 501500364901) ^ 167166788300 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 501500364901) ^ 100300072980 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 501500364901) ^ 84243300 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 501500364901) ^ 1785900 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_533172207949 : Nat.Prime 533172207949 := by
  apply lucas_primality 533172207949 (7 : ZMod 533172207949)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (73, 1), (19717, 1), (30869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (73, 1), (19717, 1), (30869, 1)] : List FactorBlock).map factorBlockValue).prod) = 533172207949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_73
      · exact prime_sixtyThreeBI_19717
      · exact prime_sixtyThreeBI_30869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 533172207949) ^ 266586103974 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 533172207949) ^ 177724069316 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 533172207949) ^ 7303728876 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 533172207949) ^ 27041244 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 533172207949) ^ 17272092 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_665052233543 : Nat.Prime 665052233543 := by
  apply lucas_primality 665052233543 (5 : ZMod 665052233543)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (109, 1), (3050698319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (109, 1), (3050698319, 1)] : List FactorBlock).map factorBlockValue).prod) = 665052233543 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_109
      · exact prime_sixtyThreeBI_3050698319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 665052233543) ^ 332526116771 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 665052233543) ^ 6101396638 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 665052233543) ^ 218 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_668367193181 : Nat.Prime 668367193181 := by
  apply lucas_primality 668367193181 (2 : ZMod 668367193181)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (33418359659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (33418359659, 1)] : List FactorBlock).map factorBlockValue).prod) = 668367193181 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_33418359659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 668367193181) ^ 334183596590 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 668367193181) ^ 133673438636 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 668367193181) ^ 20 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_678477468577 : Nat.Prime 678477468577 := by
  apply lucas_primality 678477468577 (7 : ZMod 678477468577)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (17, 1), (415733743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (17, 1), (415733743, 1)] : List FactorBlock).map factorBlockValue).prod) = 678477468577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_17
      · exact prime_sixtyThreeBI_415733743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 678477468577) ^ 339238734288 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 678477468577) ^ 226159156192 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 678477468577) ^ 39910439328 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 678477468577) ^ 1632 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_773347774051 : Nat.Prime 773347774051 := by
  apply lucas_primality 773347774051 (10 : ZMod 773347774051)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 2), (10103, 1), (56701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 2), (10103, 1), (56701, 1)] : List FactorBlock).map factorBlockValue).prod) = 773347774051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_10103
      · exact prime_sixtyThreeBI_56701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 773347774051) ^ 386673887025 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (10 : ZMod 773347774051) ^ 257782591350 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (10 : ZMod 773347774051) ^ 154669554810 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (10 : ZMod 773347774051) ^ 76546350 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (10 : ZMod 773347774051) ^ 13639050 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_842312781517 : Nat.Prime 842312781517 := by
  apply lucas_primality 842312781517 (2 : ZMod 842312781517)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1597, 1), (43952869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1597, 1), (43952869, 1)] : List FactorBlock).map factorBlockValue).prod) = 842312781517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_1597
      · exact prime_sixtyThreeBI_43952869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 842312781517) ^ 421156390758 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 842312781517) ^ 280770927172 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 842312781517) ^ 527434428 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 842312781517) ^ 19164 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_852196850009 : Nat.Prime 852196850009 := by
  apply lucas_primality 852196850009 (3 : ZMod 852196850009)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (31, 1), (3889, 1), (126227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (31, 1), (3889, 1), (126227, 1)] : List FactorBlock).map factorBlockValue).prod) = 852196850009 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_31
      · exact prime_sixtyThreeBI_3889
      · exact prime_sixtyThreeBI_126227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 852196850009) ^ 426098425004 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 852196850009) ^ 121742407144 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 852196850009) ^ 27490220968 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 852196850009) ^ 219130072 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 852196850009) ^ 6751304 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_1264490511611 : Nat.Prime 1264490511611 := by
  apply lucas_primality 1264490511611 (2 : ZMod 1264490511611)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (29, 1), (229490111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (29, 1), (229490111, 1)] : List FactorBlock).map factorBlockValue).prod) = 1264490511611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_19
      · exact prime_sixtyThreeBI_29
      · exact prime_sixtyThreeBI_229490111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1264490511611) ^ 632245255805 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1264490511611) ^ 252898102322 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1264490511611) ^ 66552132190 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1264490511611) ^ 43603121090 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1264490511611) ^ 5510 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_1612865308013 : Nat.Prime 1612865308013 := by
  apply lucas_primality 1612865308013 (2 : ZMod 1612865308013)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (5351, 1), (10764779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (5351, 1), (10764779, 1)] : List FactorBlock).map factorBlockValue).prod) = 1612865308013 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_5351
      · exact prime_sixtyThreeBI_10764779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1612865308013) ^ 806432654006 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1612865308013) ^ 230409329716 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1612865308013) ^ 301413812 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1612865308013) ^ 149828 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_1626640913239 : Nat.Prime 1626640913239 := by
  apply lucas_primality 1626640913239 (6 : ZMod 1626640913239)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (67733, 1), (363871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (67733, 1), (363871, 1)] : List FactorBlock).map factorBlockValue).prod) = 1626640913239 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_11
      · exact prime_sixtyThreeBI_67733
      · exact prime_sixtyThreeBI_363871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1626640913239) ^ 813320456619 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (6 : ZMod 1626640913239) ^ 542213637746 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (6 : ZMod 1626640913239) ^ 147876446658 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (6 : ZMod 1626640913239) ^ 24015486 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (6 : ZMod 1626640913239) ^ 4470378 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_1927701968839 : Nat.Prime 1927701968839 := by
  apply lucas_primality 1927701968839 (3 : ZMod 1927701968839)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (14533, 1), (22107181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (14533, 1), (22107181, 1)] : List FactorBlock).map factorBlockValue).prod) = 1927701968839 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_14533
      · exact prime_sixtyThreeBI_22107181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1927701968839) ^ 963850984419 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1927701968839) ^ 642567322946 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1927701968839) ^ 132643086 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1927701968839) ^ 87198 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_2582427313633 : Nat.Prime 2582427313633 := by
  apply lucas_primality 2582427313633 (11 : ZMod 2582427313633)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (613, 1), (43883009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (613, 1), (43883009, 1)] : List FactorBlock).map factorBlockValue).prod) = 2582427313633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_613
      · exact prime_sixtyThreeBI_43883009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 2582427313633) ^ 1291213656816 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (11 : ZMod 2582427313633) ^ 860809104544 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (11 : ZMod 2582427313633) ^ 4212768864 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (11 : ZMod 2582427313633) ^ 58848 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_2610632463559 : Nat.Prime 2610632463559 := by
  apply lucas_primality 2610632463559 (3 : ZMod 2610632463559)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (18269, 1), (486053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (18269, 1), (486053, 1)] : List FactorBlock).map factorBlockValue).prod) = 2610632463559 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_18269
      · exact prime_sixtyThreeBI_486053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2610632463559) ^ 1305316231779 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2610632463559) ^ 870210821186 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2610632463559) ^ 372947494794 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2610632463559) ^ 142899582 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2610632463559) ^ 5371086 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_3135369137867 : Nat.Prime 3135369137867 := by
  apply lucas_primality 3135369137867 (2 : ZMod 3135369137867)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 1), (13173819907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 1), (13173819907, 1)] : List FactorBlock).map factorBlockValue).prod) = 3135369137867 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_17
      · exact prime_sixtyThreeBI_13173819907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3135369137867) ^ 1567684568933 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3135369137867) ^ 447909876838 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3135369137867) ^ 184433478698 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3135369137867) ^ 238 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_3771204545561 : Nat.Prime 3771204545561 := by
  apply lucas_primality 3771204545561 (3 : ZMod 3771204545561)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (109, 1), (433, 1), (1997587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (109, 1), (433, 1), (1997587, 1)] : List FactorBlock).map factorBlockValue).prod) = 3771204545561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_109
      · exact prime_sixtyThreeBI_433
      · exact prime_sixtyThreeBI_1997587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3771204545561) ^ 1885602272780 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 3771204545561) ^ 754240909112 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 3771204545561) ^ 34598206840 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 3771204545561) ^ 8709479320 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 3771204545561) ^ 1887880 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_3989652261701 : Nat.Prime 3989652261701 := by
  apply lucas_primality 3989652261701 (2 : ZMod 3989652261701)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 1), (241, 1), (23649391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 1), (241, 1), (23649391, 1)] : List FactorBlock).map factorBlockValue).prod) = 3989652261701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_241
      · exact prime_sixtyThreeBI_23649391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3989652261701) ^ 1994826130850 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3989652261701) ^ 797930452340 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3989652261701) ^ 569950323100 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3989652261701) ^ 16554573700 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3989652261701) ^ 168700 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_5106398546429 : Nat.Prime 5106398546429 := by
  apply lucas_primality 5106398546429 (3 : ZMod 5106398546429)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (991, 1), (5573, 1), (13597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (991, 1), (5573, 1), (13597, 1)] : List FactorBlock).map factorBlockValue).prod) = 5106398546429 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_17
      · exact prime_sixtyThreeBI_991
      · exact prime_sixtyThreeBI_5573
      · exact prime_sixtyThreeBI_13597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5106398546429) ^ 2553199273214 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5106398546429) ^ 300376385084 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5106398546429) ^ 5152773508 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5106398546429) ^ 916274636 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5106398546429) ^ 375553324 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_7542409091123 : Nat.Prime 7542409091123 := by
  apply lucas_primality 7542409091123 (2 : ZMod 7542409091123)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3771204545561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3771204545561, 1)] : List FactorBlock).map factorBlockValue).prod) = 7542409091123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3771204545561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 7542409091123) ^ 3771204545561 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 7542409091123) ^ 2 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_8163546666479 : Nat.Prime 8163546666479 := by
  apply lucas_primality 8163546666479 (14 : ZMod 8163546666479)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (23, 1), (103, 1), (246142033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (23, 1), (103, 1), (246142033, 1)] : List FactorBlock).map factorBlockValue).prod) = 8163546666479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_23
      · exact prime_sixtyThreeBI_103
      · exact prime_sixtyThreeBI_246142033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 8163546666479) ^ 4081773333239 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (14 : ZMod 8163546666479) ^ 1166220952354 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (14 : ZMod 8163546666479) ^ 354936811586 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (14 : ZMod 8163546666479) ^ 79257734626 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (14 : ZMod 8163546666479) ^ 33166 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_12324666126419 : Nat.Prime 12324666126419 := by
  apply lucas_primality 12324666126419 (2 : ZMod 12324666126419)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (107, 1), (317, 1), (853, 1), (212987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (107, 1), (317, 1), (853, 1), (212987, 1)] : List FactorBlock).map factorBlockValue).prod) = 12324666126419 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_107
      · exact prime_sixtyThreeBI_317
      · exact prime_sixtyThreeBI_853
      · exact prime_sixtyThreeBI_212987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12324666126419) ^ 6162333063209 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 12324666126419) ^ 115183795574 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 12324666126419) ^ 38879072954 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 12324666126419) ^ 14448612106 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 12324666126419) ^ 57865814 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_14308866497693 : Nat.Prime 14308866497693 := by
  apply lucas_primality 14308866497693 (3 : ZMod 14308866497693)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (17, 1), (47, 1), (53, 1), (131, 1), (49603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (17, 1), (47, 1), (53, 1), (131, 1), (49603, 1)] : List FactorBlock).map factorBlockValue).prod) = 14308866497693 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_13
      · exact prime_sixtyThreeBI_17
      · exact prime_sixtyThreeBI_47
      · exact prime_sixtyThreeBI_53
      · exact prime_sixtyThreeBI_131
      · exact prime_sixtyThreeBI_49603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 14308866497693) ^ 7154433248846 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 14308866497693) ^ 1100682038284 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 14308866497693) ^ 841698029276 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 14308866497693) ^ 304443968036 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 14308866497693) ^ 269978613164 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 14308866497693) ^ 109227988532 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 14308866497693) ^ 288467764 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_18265816887757 : Nat.Prime 18265816887757 := by
  apply lucas_primality 18265816887757 (5 : ZMod 18265816887757)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (101, 1), (179, 1), (84194447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (101, 1), (179, 1), (84194447, 1)] : List FactorBlock).map factorBlockValue).prod) = 18265816887757 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_101
      · exact prime_sixtyThreeBI_179
      · exact prime_sixtyThreeBI_84194447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 18265816887757) ^ 9132908443878 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 18265816887757) ^ 6088605629252 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 18265816887757) ^ 180849672156 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 18265816887757) ^ 102043669764 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 18265816887757) ^ 216948 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_18690948590087 : Nat.Prime 18690948590087 := by
  apply lucas_primality 18690948590087 (5 : ZMod 18690948590087)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (397, 1), (85819, 1), (274301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (397, 1), (85819, 1), (274301, 1)] : List FactorBlock).map factorBlockValue).prod) = 18690948590087 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_397
      · exact prime_sixtyThreeBI_85819
      · exact prime_sixtyThreeBI_274301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 18690948590087) ^ 9345474295043 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 18690948590087) ^ 47080475038 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 18690948590087) ^ 217794994 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 18690948590087) ^ 68140286 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_18841527461389 : Nat.Prime 18841527461389 := by
  apply lucas_primality 18841527461389 (2 : ZMod 18841527461389)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1087, 1), (2777, 1), (520151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1087, 1), (2777, 1), (520151, 1)] : List FactorBlock).map factorBlockValue).prod) = 18841527461389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_1087
      · exact prime_sixtyThreeBI_2777
      · exact prime_sixtyThreeBI_520151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18841527461389) ^ 9420763730694 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 18841527461389) ^ 6280509153796 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 18841527461389) ^ 17333511924 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 18841527461389) ^ 6784849644 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 18841527461389) ^ 36223188 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_20415477499913 : Nat.Prime 20415477499913 := by
  apply lucas_primality 20415477499913 (5 : ZMod 20415477499913)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (6421, 1), (36130519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (6421, 1), (36130519, 1)] : List FactorBlock).map factorBlockValue).prod) = 20415477499913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_11
      · exact prime_sixtyThreeBI_6421
      · exact prime_sixtyThreeBI_36130519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 20415477499913) ^ 10207738749956 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 20415477499913) ^ 1855952499992 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 20415477499913) ^ 3179485672 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 20415477499913) ^ 565048 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_24102759904621 : Nat.Prime 24102759904621 := by
  apply lucas_primality 24102759904621 (6 : ZMod 24102759904621)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (31, 1), (127, 1), (1103, 1), (92507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (31, 1), (127, 1), (1103, 1), (92507, 1)] : List FactorBlock).map factorBlockValue).prod) = 24102759904621 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_31
      · exact prime_sixtyThreeBI_127
      · exact prime_sixtyThreeBI_1103
      · exact prime_sixtyThreeBI_92507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 24102759904621) ^ 12051379952310 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (6 : ZMod 24102759904621) ^ 8034253301540 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (6 : ZMod 24102759904621) ^ 4820551980924 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (6 : ZMod 24102759904621) ^ 777508384020 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (6 : ZMod 24102759904621) ^ 189785511060 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (6 : ZMod 24102759904621) ^ 21852003540 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (6 : ZMod 24102759904621) ^ 260550660 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_29546860823027 : Nat.Prime 29546860823027 := by
  apply lucas_primality 29546860823027 (2 : ZMod 29546860823027)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (79, 1), (1021, 1), (1811, 1), (5323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (79, 1), (1021, 1), (1811, 1), (5323, 1)] : List FactorBlock).map factorBlockValue).prod) = 29546860823027 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_19
      · exact prime_sixtyThreeBI_79
      · exact prime_sixtyThreeBI_1021
      · exact prime_sixtyThreeBI_1811
      · exact prime_sixtyThreeBI_5323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 29546860823027) ^ 14773430411513 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 29546860823027) ^ 1555097938054 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 29546860823027) ^ 374010896494 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 29546860823027) ^ 28939138906 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 29546860823027) ^ 16315218566 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 29546860823027) ^ 5550791062 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_32584783811693 : Nat.Prime 32584783811693 := by
  apply lucas_primality 32584783811693 (2 : ZMod 32584783811693)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (19, 1), (61249593631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (19, 1), (61249593631, 1)] : List FactorBlock).map factorBlockValue).prod) = 32584783811693 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_19
      · exact prime_sixtyThreeBI_61249593631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32584783811693) ^ 16292391905846 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 32584783811693) ^ 4654969115956 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 32584783811693) ^ 1714988621668 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 32584783811693) ^ 532 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_36464372538967 : Nat.Prime 36464372538967 := by
  apply lucas_primality 36464372538967 (3 : ZMod 36464372538967)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (3467, 1), (4937, 1), (39451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (3467, 1), (4937, 1), (39451, 1)] : List FactorBlock).map factorBlockValue).prod) = 36464372538967 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_3467
      · exact prime_sixtyThreeBI_4937
      · exact prime_sixtyThreeBI_39451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 36464372538967) ^ 18232186269483 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 36464372538967) ^ 12154790846322 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 36464372538967) ^ 10517557698 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 36464372538967) ^ 7385937318 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 36464372538967) ^ 924295266 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_50750813513291 : Nat.Prime 50750813513291 := by
  apply lucas_primality 50750813513291 (2 : ZMod 50750813513291)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (17, 1), (27139472467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (17, 1), (27139472467, 1)] : List FactorBlock).map factorBlockValue).prod) = 50750813513291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_11
      · exact prime_sixtyThreeBI_17
      · exact prime_sixtyThreeBI_27139472467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 50750813513291) ^ 25375406756645 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 50750813513291) ^ 10150162702658 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 50750813513291) ^ 4613710319390 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 50750813513291) ^ 2985341971370 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 50750813513291) ^ 1870 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_52260907760839 : Nat.Prime 52260907760839 := by
  apply lucas_primality 52260907760839 (3 : ZMod 52260907760839)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (23, 1), (641, 1), (28133291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (23, 1), (641, 1), (28133291, 1)] : List FactorBlock).map factorBlockValue).prod) = 52260907760839 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_23
      · exact prime_sixtyThreeBI_641
      · exact prime_sixtyThreeBI_28133291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 52260907760839) ^ 26130453880419 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 52260907760839) ^ 17420302586946 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 52260907760839) ^ 7465843965834 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 52260907760839) ^ 2272213380906 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 52260907760839) ^ 81530277318 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 52260907760839) ^ 1857618 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_53716248719941 : Nat.Prime 53716248719941 := by
  apply lucas_primality 53716248719941 (2 : ZMod 53716248719941)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (19, 1), (23, 1), (859, 1), (2384953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (19, 1), (23, 1), (859, 1), (2384953, 1)] : List FactorBlock).map factorBlockValue).prod) = 53716248719941 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_19
      · exact prime_sixtyThreeBI_23
      · exact prime_sixtyThreeBI_859
      · exact prime_sixtyThreeBI_2384953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 53716248719941) ^ 26858124359970 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 53716248719941) ^ 17905416239980 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 53716248719941) ^ 10743249743988 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 53716248719941) ^ 2827170985260 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 53716248719941) ^ 2335489074780 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 53716248719941) ^ 62533467660 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 53716248719941) ^ 22522980 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_87397626824359 : Nat.Prime 87397626824359 := by
  apply lucas_primality 87397626824359 (6 : ZMod 87397626824359)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1327, 1), (24671, 1), (444929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1327, 1), (24671, 1), (444929, 1)] : List FactorBlock).map factorBlockValue).prod) = 87397626824359 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_1327
      · exact prime_sixtyThreeBI_24671
      · exact prime_sixtyThreeBI_444929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 87397626824359) ^ 43698813412179 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (6 : ZMod 87397626824359) ^ 29132542274786 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (6 : ZMod 87397626824359) ^ 65861060154 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (6 : ZMod 87397626824359) ^ 3542524698 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (6 : ZMod 87397626824359) ^ 196430502 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_129282225965887 : Nat.Prime 129282225965887 := by
  apply lucas_primality 129282225965887 (3 : ZMod 129282225965887)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (13901, 1), (31633369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (13901, 1), (31633369, 1)] : List FactorBlock).map factorBlockValue).prod) = 129282225965887 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_13901
      · exact prime_sixtyThreeBI_31633369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 129282225965887) ^ 64641112982943 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 129282225965887) ^ 43094075321962 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 129282225965887) ^ 18468889423698 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 129282225965887) ^ 9300210486 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 129282225965887) ^ 4086894 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_160707692966881 : Nat.Prime 160707692966881 := by
  apply lucas_primality 160707692966881 (17 : ZMod 160707692966881)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (23, 1), (14556856247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (23, 1), (14556856247, 1)] : List FactorBlock).map factorBlockValue).prod) = 160707692966881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_23
      · exact prime_sixtyThreeBI_14556856247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 160707692966881) ^ 80353846483440 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (17 : ZMod 160707692966881) ^ 53569230988960 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (17 : ZMod 160707692966881) ^ 32141538593376 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (17 : ZMod 160707692966881) ^ 6987290998560 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (17 : ZMod 160707692966881) ^ 11040 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_288568665759821 : Nat.Prime 288568665759821 := by
  apply lucas_primality 288568665759821 (3 : ZMod 288568665759821)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (383, 1), (18947, 1), (1988291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (383, 1), (18947, 1), (1988291, 1)] : List FactorBlock).map factorBlockValue).prod) = 288568665759821 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_383
      · exact prime_sixtyThreeBI_18947
      · exact prime_sixtyThreeBI_1988291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 288568665759821) ^ 144284332879910 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 288568665759821) ^ 57713733151964 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 288568665759821) ^ 753442991540 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 288568665759821) ^ 15230309060 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 288568665759821) ^ 145134020 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_295740220814411 : Nat.Prime 295740220814411 := by
  apply lucas_primality 295740220814411 (2 : ZMod 295740220814411)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37, 1), (173, 1), (229, 1), (2239, 1), (9011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37, 1), (173, 1), (229, 1), (2239, 1), (9011, 1)] : List FactorBlock).map factorBlockValue).prod) = 295740220814411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_37
      · exact prime_sixtyThreeBI_173
      · exact prime_sixtyThreeBI_229
      · exact prime_sixtyThreeBI_2239
      · exact prime_sixtyThreeBI_9011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 295740220814411) ^ 147870110407205 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 295740220814411) ^ 59148044162882 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 295740220814411) ^ 7992978940930 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 295740220814411) ^ 1709481045170 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 295740220814411) ^ 1291442012290 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 295740220814411) ^ 132085851190 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 295740220814411) ^ 32819911310 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_343216726153333 : Nat.Prime 343216726153333 := by
  apply lucas_primality 343216726153333 (2 : ZMod 343216726153333)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (89, 1), (181, 1), (16063, 1), (110533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (89, 1), (181, 1), (16063, 1), (110533, 1)] : List FactorBlock).map factorBlockValue).prod) = 343216726153333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_89
      · exact prime_sixtyThreeBI_181
      · exact prime_sixtyThreeBI_16063
      · exact prime_sixtyThreeBI_110533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 343216726153333) ^ 171608363076666 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 343216726153333) ^ 114405575384444 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 343216726153333) ^ 3856367709588 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 343216726153333) ^ 1896225006372 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 343216726153333) ^ 21366913164 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 343216726153333) ^ 3105106404 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_497848259560361 : Nat.Prime 497848259560361 := by
  apply lucas_primality 497848259560361 (3 : ZMod 497848259560361)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (4079, 1), (23459, 1), (130069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (4079, 1), (23459, 1), (130069, 1)] : List FactorBlock).map factorBlockValue).prod) = 497848259560361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_4079
      · exact prime_sixtyThreeBI_23459
      · exact prime_sixtyThreeBI_130069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 497848259560361) ^ 248924129780180 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 497848259560361) ^ 99569651912072 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 497848259560361) ^ 122051546840 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 497848259560361) ^ 21222058040 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 497848259560361) ^ 3827570440 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_845353649335649 : Nat.Prime 845353649335649 := by
  apply lucas_primality 845353649335649 (3 : ZMod 845353649335649)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5351, 1), (4936890589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5351, 1), (4936890589, 1)] : List FactorBlock).map factorBlockValue).prod) = 845353649335649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_5351
      · exact prime_sixtyThreeBI_4936890589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 845353649335649) ^ 422676824667824 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 845353649335649) ^ 157980498848 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 845353649335649) ^ 171232 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_852229247004203 : Nat.Prime 852229247004203 := by
  apply lucas_primality 852229247004203 (2 : ZMod 852229247004203)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (29, 1), (773347774051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (29, 1), (773347774051, 1)] : List FactorBlock).map factorBlockValue).prod) = 852229247004203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_19
      · exact prime_sixtyThreeBI_29
      · exact prime_sixtyThreeBI_773347774051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 852229247004203) ^ 426114623502101 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 852229247004203) ^ 44854170894958 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 852229247004203) ^ 29387215413938 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 852229247004203) ^ 1102 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_1127637802048357 : Nat.Prime 1127637802048357 := by
  apply lucas_primality 1127637802048357 (2 : ZMod 1127637802048357)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 5), (433, 1), (15907, 1), (168433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 5), (433, 1), (15907, 1), (168433, 1)] : List FactorBlock).map factorBlockValue).prod) = 1127637802048357 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_433
      · exact prime_sixtyThreeBI_15907
      · exact prime_sixtyThreeBI_168433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1127637802048357) ^ 563818901024178 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1127637802048357) ^ 375879267349452 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1127637802048357) ^ 2604244346532 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1127637802048357) ^ 70889407308 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1127637802048357) ^ 6694874532 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_1204288618134463 : Nat.Prime 1204288618134463 := by
  apply lucas_primality 1204288618134463 (7 : ZMod 1204288618134463)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (17, 1), (53, 1), (27953, 1), (162641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (17, 1), (53, 1), (27953, 1), (162641, 1)] : List FactorBlock).map factorBlockValue).prod) = 1204288618134463 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_17
      · exact prime_sixtyThreeBI_53
      · exact prime_sixtyThreeBI_27953
      · exact prime_sixtyThreeBI_162641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1204288618134463) ^ 602144309067231 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1204288618134463) ^ 401429539378154 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1204288618134463) ^ 172041231162066 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1204288618134463) ^ 70840506949086 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1204288618134463) ^ 22722426757254 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1204288618134463) ^ 43082625054 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1204288618134463) ^ 7404581982 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_1355713273906091 : Nat.Prime 1355713273906091 := by
  apply lucas_primality 1355713273906091 (2 : ZMod 1355713273906091)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (12324666126419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (12324666126419, 1)] : List FactorBlock).map factorBlockValue).prod) = 1355713273906091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_11
      · exact prime_sixtyThreeBI_12324666126419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1355713273906091) ^ 677856636953045 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1355713273906091) ^ 271142654781218 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1355713273906091) ^ 123246661264190 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1355713273906091) ^ 110 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_2420793545735093 : Nat.Prime 2420793545735093 := by
  apply lucas_primality 2420793545735093 (2 : ZMod 2420793545735093)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (521, 1), (106217, 1), (994199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (521, 1), (106217, 1), (994199, 1)] : List FactorBlock).map factorBlockValue).prod) = 2420793545735093 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_11
      · exact prime_sixtyThreeBI_521
      · exact prime_sixtyThreeBI_106217
      · exact prime_sixtyThreeBI_994199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2420793545735093) ^ 1210396772867546 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2420793545735093) ^ 220072140521372 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2420793545735093) ^ 4646436748052 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2420793545735093) ^ 22791017876 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2420793545735093) ^ 2434918508 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_2830640417612081 : Nat.Prime 2830640417612081 := by
  apply lucas_primality 2830640417612081 (3 : ZMod 2830640417612081)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (283, 1), (3709, 1), (33709433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (283, 1), (3709, 1), (33709433, 1)] : List FactorBlock).map factorBlockValue).prod) = 2830640417612081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_283
      · exact prime_sixtyThreeBI_3709
      · exact prime_sixtyThreeBI_33709433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2830640417612081) ^ 1415320208806040 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2830640417612081) ^ 566128083522416 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2830640417612081) ^ 10002262959760 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2830640417612081) ^ 763181563120 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2830640417612081) ^ 83971760 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_3881898188875849 : Nat.Prime 3881898188875849 := by
  apply lucas_primality 3881898188875849 (11 : ZMod 3881898188875849)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (109, 1), (917789, 1), (1616827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (109, 1), (917789, 1), (1616827, 1)] : List FactorBlock).map factorBlockValue).prod) = 3881898188875849 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_109
      · exact prime_sixtyThreeBI_917789
      · exact prime_sixtyThreeBI_1616827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 3881898188875849) ^ 1940949094437924 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (11 : ZMod 3881898188875849) ^ 1293966062958616 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (11 : ZMod 3881898188875849) ^ 35613744852072 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (11 : ZMod 3881898188875849) ^ 4229619432 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (11 : ZMod 3881898188875849) ^ 2400936024 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_5536376143588321 : Nat.Prime 5536376143588321 := by
  apply lucas_primality 5536376143588321 (13 : ZMod 5536376143588321)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (17, 1), (678477468577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (17, 1), (678477468577, 1)] : List FactorBlock).map factorBlockValue).prod) = 5536376143588321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_17
      · exact prime_sixtyThreeBI_678477468577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 5536376143588321) ^ 2768188071794160 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (13 : ZMod 5536376143588321) ^ 1845458714529440 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (13 : ZMod 5536376143588321) ^ 1107275228717664 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (13 : ZMod 5536376143588321) ^ 325669184916960 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (13 : ZMod 5536376143588321) ^ 8160 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_5661280835224163 : Nat.Prime 5661280835224163 := by
  apply lucas_primality 5661280835224163 (2 : ZMod 5661280835224163)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2830640417612081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2830640417612081, 1)] : List FactorBlock).map factorBlockValue).prod) = 5661280835224163 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_2830640417612081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 5661280835224163) ^ 2830640417612081 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5661280835224163) ^ 2 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_5767223769463327 : Nat.Prime 5767223769463327 := by
  apply lucas_primality 5767223769463327 (3 : ZMod 5767223769463327)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (151243, 1), (171766531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (151243, 1), (171766531, 1)] : List FactorBlock).map factorBlockValue).prod) = 5767223769463327 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_37
      · exact prime_sixtyThreeBI_151243
      · exact prime_sixtyThreeBI_171766531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5767223769463327) ^ 2883611884731663 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5767223769463327) ^ 1922407923154442 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5767223769463327) ^ 155870912688198 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5767223769463327) ^ 38132169882 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5767223769463327) ^ 33575946 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_6591439687013989 : Nat.Prime 6591439687013989 := by
  apply lucas_primality 6591439687013989 (2 : ZMod 6591439687013989)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (337, 1), (1109, 1), (22271, 1), (65993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (337, 1), (1109, 1), (22271, 1), (65993, 1)] : List FactorBlock).map factorBlockValue).prod) = 6591439687013989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_337
      · exact prime_sixtyThreeBI_1109
      · exact prime_sixtyThreeBI_22271
      · exact prime_sixtyThreeBI_65993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6591439687013989) ^ 3295719843506994 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6591439687013989) ^ 2197146562337996 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6591439687013989) ^ 19559168210724 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6591439687013989) ^ 5943588536532 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6591439687013989) ^ 295965142428 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6591439687013989) ^ 99880891716 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_9145509033221747 : Nat.Prime 9145509033221747 := by
  apply lucas_primality 9145509033221747 (2 : ZMod 9145509033221747)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (337, 1), (1019, 1), (13316000491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (337, 1), (1019, 1), (13316000491, 1)] : List FactorBlock).map factorBlockValue).prod) = 9145509033221747 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_337
      · exact prime_sixtyThreeBI_1019
      · exact prime_sixtyThreeBI_13316000491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9145509033221747) ^ 4572754516610873 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9145509033221747) ^ 27138009000658 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9145509033221747) ^ 8974984330934 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9145509033221747) ^ 686806 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_9795692134747243 : Nat.Prime 9795692134747243 := by
  apply lucas_primality 9795692134747243 (2 : ZMod 9795692134747243)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (107, 1), (1543, 1), (1098731723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (107, 1), (1543, 1), (1098731723, 1)] : List FactorBlock).map factorBlockValue).prod) = 9795692134747243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_107
      · exact prime_sixtyThreeBI_1543
      · exact prime_sixtyThreeBI_1098731723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9795692134747243) ^ 4897846067373621 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9795692134747243) ^ 3265230711582414 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9795692134747243) ^ 91548524623806 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9795692134747243) ^ 6348471895494 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9795692134747243) ^ 8915454 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_14014466429079869 : Nat.Prime 14014466429079869 := by
  apply lucas_primality 14014466429079869 (2 : ZMod 14014466429079869)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1493, 1), (91961, 1), (25518379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1493, 1), (91961, 1), (25518379, 1)] : List FactorBlock).map factorBlockValue).prod) = 14014466429079869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_1493
      · exact prime_sixtyThreeBI_91961
      · exact prime_sixtyThreeBI_25518379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14014466429079869) ^ 7007233214539934 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 14014466429079869) ^ 9386782604876 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 14014466429079869) ^ 152395759388 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 14014466429079869) ^ 549191092 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_17188234619635903 : Nat.Prime 17188234619635903 := by
  apply lucas_primality 17188234619635903 (3 : ZMod 17188234619635903)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (179, 1), (842312781517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (179, 1), (842312781517, 1)] : List FactorBlock).map factorBlockValue).prod) = 17188234619635903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_19
      · exact prime_sixtyThreeBI_179
      · exact prime_sixtyThreeBI_842312781517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 17188234619635903) ^ 8594117309817951 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 17188234619635903) ^ 5729411539878634 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 17188234619635903) ^ 904643927349258 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 17188234619635903) ^ 96023657092938 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 17188234619635903) ^ 20406 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_19881408637134911 : Nat.Prime 19881408637134911 := by
  apply lucas_primality 19881408637134911 (11 : ZMod 19881408637134911)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (61, 1), (6473, 1), (5035141847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (61, 1), (6473, 1), (5035141847, 1)] : List FactorBlock).map factorBlockValue).prod) = 19881408637134911 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_61
      · exact prime_sixtyThreeBI_6473
      · exact prime_sixtyThreeBI_5035141847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 19881408637134911) ^ 9940704318567455 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (11 : ZMod 19881408637134911) ^ 3976281727426982 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (11 : ZMod 19881408637134911) ^ 325924731756310 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (11 : ZMod 19881408637134911) ^ 3071436526670 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (11 : ZMod 19881408637134911) ^ 3948530 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_20561365494974201 : Nat.Prime 20561365494974201 := by
  apply lucas_primality 20561365494974201 (6 : ZMod 20561365494974201)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (13, 1), (59, 1), (351223, 1), (381631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (13, 1), (59, 1), (351223, 1), (381631, 1)] : List FactorBlock).map factorBlockValue).prod) = 20561365494974201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_13
      · exact prime_sixtyThreeBI_59
      · exact prime_sixtyThreeBI_351223
      · exact prime_sixtyThreeBI_381631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 20561365494974201) ^ 10280682747487100 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (6 : ZMod 20561365494974201) ^ 4112273098994840 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (6 : ZMod 20561365494974201) ^ 1581643499613400 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (6 : ZMod 20561365494974201) ^ 348497720253800 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (6 : ZMod 20561365494974201) ^ 58542195400 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (6 : ZMod 20561365494974201) ^ 53877608200 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_30096369610248091 : Nat.Prime 30096369610248091 := by
  apply lucas_primality 30096369610248091 (2 : ZMod 30096369610248091)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (37, 1), (127, 1), (12558520841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (37, 1), (127, 1), (12558520841, 1)] : List FactorBlock).map factorBlockValue).prod) = 30096369610248091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_17
      · exact prime_sixtyThreeBI_37
      · exact prime_sixtyThreeBI_127
      · exact prime_sixtyThreeBI_12558520841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30096369610248091) ^ 15048184805124045 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 30096369610248091) ^ 10032123203416030 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 30096369610248091) ^ 6019273922049618 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 30096369610248091) ^ 1770374682955770 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 30096369610248091) ^ 813415394871570 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 30096369610248091) ^ 236979288269670 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 30096369610248091) ^ 2396490 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_33359558322754529 : Nat.Prime 33359558322754529 := by
  apply lucas_primality 33359558322754529 (3 : ZMod 33359558322754529)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7607, 1), (32983, 1), (4154959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7607, 1), (32983, 1), (4154959, 1)] : List FactorBlock).map factorBlockValue).prod) = 33359558322754529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_7607
      · exact prime_sixtyThreeBI_32983
      · exact prime_sixtyThreeBI_4154959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 33359558322754529) ^ 16679779161377264 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 33359558322754529) ^ 4385376406304 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 33359558322754529) ^ 1011416739616 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 33359558322754529) ^ 8028853792 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_33854602778938111 : Nat.Prime 33854602778938111 := by
  apply lucas_primality 33854602778938111 (3 : ZMod 33854602778938111)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (1156907, 1), (75033407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (1156907, 1), (75033407, 1)] : List FactorBlock).map factorBlockValue).prod) = 33854602778938111 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_13
      · exact prime_sixtyThreeBI_1156907
      · exact prime_sixtyThreeBI_75033407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 33854602778938111) ^ 16927301389469055 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 33854602778938111) ^ 11284867592979370 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 33854602778938111) ^ 6770920555787622 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 33854602778938111) ^ 2604200213764470 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 33854602778938111) ^ 29263028730 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 33854602778938111) ^ 451193730 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_34434640514865469 : Nat.Prime 34434640514865469 := by
  apply lucas_primality 34434640514865469 (2 : ZMod 34434640514865469)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (191461, 1), (14987665249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (191461, 1), (14987665249, 1)] : List FactorBlock).map factorBlockValue).prod) = 34434640514865469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_191461
      · exact prime_sixtyThreeBI_14987665249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 34434640514865469) ^ 17217320257432734 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 34434640514865469) ^ 11478213504955156 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 34434640514865469) ^ 179851982988 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 34434640514865469) ^ 2297532 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_37332979997090461 : Nat.Prime 37332979997090461 := by
  apply lucas_primality 37332979997090461 (6 : ZMod 37332979997090461)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (1873, 1), (14983, 1), (22171999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (1873, 1), (14983, 1), (22171999, 1)] : List FactorBlock).map factorBlockValue).prod) = 37332979997090461 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_1873
      · exact prime_sixtyThreeBI_14983
      · exact prime_sixtyThreeBI_22171999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 37332979997090461) ^ 18666489998545230 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (6 : ZMod 37332979997090461) ^ 12444326665696820 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (6 : ZMod 37332979997090461) ^ 7466595999418092 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (6 : ZMod 37332979997090461) ^ 19932183661020 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (6 : ZMod 37332979997090461) ^ 2491689247620 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (6 : ZMod 37332979997090461) ^ 1683789540 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_41122730989948403 : Nat.Prime 41122730989948403 := by
  apply lucas_primality 41122730989948403 (2 : ZMod 41122730989948403)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (20561365494974201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (20561365494974201, 1)] : List FactorBlock).map factorBlockValue).prod) = 41122730989948403 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_20561365494974201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 41122730989948403) ^ 20561365494974201 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 41122730989948403) ^ 2 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_42044012497890467 : Nat.Prime 42044012497890467 := by
  apply lucas_primality 42044012497890467 (2 : ZMod 42044012497890467)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (23, 1), (31, 1), (524827, 1), (8025469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (23, 1), (31, 1), (524827, 1), (8025469, 1)] : List FactorBlock).map factorBlockValue).prod) = 42044012497890467 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_23
      · exact prime_sixtyThreeBI_31
      · exact prime_sixtyThreeBI_524827
      · exact prime_sixtyThreeBI_8025469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 42044012497890467) ^ 21022006248945233 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 42044012497890467) ^ 6006287499698638 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 42044012497890467) ^ 1828000543386542 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 42044012497890467) ^ 1356258467673886 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 42044012497890467) ^ 80110231558 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 42044012497890467) ^ 5238823114 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_66719116645509059 : Nat.Prime 66719116645509059 := by
  apply lucas_primality 66719116645509059 (2 : ZMod 66719116645509059)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (33359558322754529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (33359558322754529, 1)] : List FactorBlock).map factorBlockValue).prod) = 66719116645509059 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_33359558322754529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 66719116645509059) ^ 33359558322754529 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 66719116645509059) ^ 2 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_75464750806651517 : Nat.Prime 75464750806651517 := by
  apply lucas_primality 75464750806651517 (2 : ZMod 75464750806651517)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 2), (52260907760839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 2), (52260907760839, 1)] : List FactorBlock).map factorBlockValue).prod) = 75464750806651517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_19
      · exact prime_sixtyThreeBI_52260907760839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 75464750806651517) ^ 37732375403325758 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 75464750806651517) ^ 3971828989823764 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 75464750806651517) ^ 1444 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_124050761219139373 : Nat.Prime 124050761219139373 := by
  apply lucas_primality 124050761219139373 (2 : ZMod 124050761219139373)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (37, 1), (6221, 1), (14970455251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (37, 1), (6221, 1), (14970455251, 1)] : List FactorBlock).map factorBlockValue).prod) = 124050761219139373 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_37
      · exact prime_sixtyThreeBI_6221
      · exact prime_sixtyThreeBI_14970455251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 124050761219139373) ^ 62025380609569686 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 124050761219139373) ^ 41350253739713124 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 124050761219139373) ^ 3352723276192956 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 124050761219139373) ^ 19940646394332 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 124050761219139373) ^ 8286372 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_208188244933217999 : Nat.Prime 208188244933217999 := by
  apply lucas_primality 208188244933217999 (7 : ZMod 208188244933217999)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (2420793545735093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (2420793545735093, 1)] : List FactorBlock).map factorBlockValue).prod) = 208188244933217999 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_43
      · exact prime_sixtyThreeBI_2420793545735093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 208188244933217999) ^ 104094122466608999 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 208188244933217999) ^ 4841587091470186 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 208188244933217999) ^ 86 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_241496620161628147 : Nat.Prime 241496620161628147 := by
  apply lucas_primality 241496620161628147 (2 : ZMod 241496620161628147)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (103, 1), (137, 1), (7583, 1), (53735701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (103, 1), (137, 1), (7583, 1), (53735701, 1)] : List FactorBlock).map factorBlockValue).prod) = 241496620161628147 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_103
      · exact prime_sixtyThreeBI_137
      · exact prime_sixtyThreeBI_7583
      · exact prime_sixtyThreeBI_53735701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 241496620161628147) ^ 120748310080814073 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 241496620161628147) ^ 80498873387209382 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 241496620161628147) ^ 34499517165946878 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 241496620161628147) ^ 2344627380209982 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 241496620161628147) ^ 1762749052274658 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 241496620161628147) ^ 31847108026062 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 241496620161628147) ^ 4494155946 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_267034445698862041 : Nat.Prime 267034445698862041 := by
  apply lucas_primality 267034445698862041 (11 : ZMod 267034445698862041)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (109, 1), (20415477499913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (109, 1), (20415477499913, 1)] : List FactorBlock).map factorBlockValue).prod) = 267034445698862041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_109
      · exact prime_sixtyThreeBI_20415477499913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 267034445698862041) ^ 133517222849431020 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (11 : ZMod 267034445698862041) ^ 89011481899620680 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (11 : ZMod 267034445698862041) ^ 53406889139772408 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (11 : ZMod 267034445698862041) ^ 2449857299989560 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (11 : ZMod 267034445698862041) ^ 13080 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_484771770678955633 : Nat.Prime 484771770678955633 := by
  apply lucas_primality 484771770678955633 (5 : ZMod 484771770678955633)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (199, 1), (50750813513291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (199, 1), (50750813513291, 1)] : List FactorBlock).map factorBlockValue).prod) = 484771770678955633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_199
      · exact prime_sixtyThreeBI_50750813513291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 484771770678955633) ^ 242385885339477816 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 484771770678955633) ^ 161590590226318544 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 484771770678955633) ^ 2436039048637968 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 484771770678955633) ^ 9552 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_519908084933067827 : Nat.Prime 519908084933067827 := by
  apply lucas_primality 519908084933067827 (2 : ZMod 519908084933067827)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (29, 1), (31517, 1), (42569, 1), (393017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (29, 1), (31517, 1), (42569, 1), (393017, 1)] : List FactorBlock).map factorBlockValue).prod) = 519908084933067827 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_17
      · exact prime_sixtyThreeBI_29
      · exact prime_sixtyThreeBI_31517
      · exact prime_sixtyThreeBI_42569
      · exact prime_sixtyThreeBI_393017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 519908084933067827) ^ 259954042466533913 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 519908084933067827) ^ 30582828525474578 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 519908084933067827) ^ 17927864997691994 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 519908084933067827) ^ 16496115903578 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 519908084933067827) ^ 12213302753954 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 519908084933067827) ^ 1322864112578 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_701006956721534923 : Nat.Prime 701006956721534923 := by
  apply lucas_primality 701006956721534923 (2 : ZMod 701006956721534923)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (727, 1), (160707692966881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (727, 1), (160707692966881, 1)] : List FactorBlock).map factorBlockValue).prod) = 701006956721534923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_727
      · exact prime_sixtyThreeBI_160707692966881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 701006956721534923) ^ 350503478360767461 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 701006956721534923) ^ 233668985573844974 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 701006956721534923) ^ 964246157801286 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 701006956721534923) ^ 4362 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_1199172829602141899 : Nat.Prime 1199172829602141899 := by
  apply lucas_primality 1199172829602141899 (2 : ZMod 1199172829602141899)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (307, 1), (7013, 1), (39784282477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (307, 1), (7013, 1), (39784282477, 1)] : List FactorBlock).map factorBlockValue).prod) = 1199172829602141899 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_307
      · exact prime_sixtyThreeBI_7013
      · exact prime_sixtyThreeBI_39784282477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1199172829602141899) ^ 599586414801070949 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1199172829602141899) ^ 171310404228877414 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1199172829602141899) ^ 3906100422156814 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1199172829602141899) ^ 170992846086146 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1199172829602141899) ^ 30141874 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_1233914021859248759 : Nat.Prime 1233914021859248759 := by
  apply lucas_primality 1233914021859248759 (7 : ZMod 1233914021859248759)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (37, 1), (61, 1), (11681, 1), (3343068541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (37, 1), (61, 1), (11681, 1), (3343068541, 1)] : List FactorBlock).map factorBlockValue).prod) = 1233914021859248759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_37
      · exact prime_sixtyThreeBI_61
      · exact prime_sixtyThreeBI_11681
      · exact prime_sixtyThreeBI_3343068541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1233914021859248759) ^ 616957010929624379 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1233914021859248759) ^ 176273431694178394 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1233914021859248759) ^ 33349027617817534 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1233914021859248759) ^ 20228098719004078 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1233914021859248759) ^ 105634279758518 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1233914021859248759) ^ 369096238 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_1331084885868471581 : Nat.Prime 1331084885868471581 := by
  apply lucas_primality 1331084885868471581 (2 : ZMod 1331084885868471581)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (11, 1), (263399, 1), (3281488673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (11, 1), (263399, 1), (3281488673, 1)] : List FactorBlock).map factorBlockValue).prod) = 1331084885868471581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_11
      · exact prime_sixtyThreeBI_263399
      · exact prime_sixtyThreeBI_3281488673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1331084885868471581) ^ 665542442934235790 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1331084885868471581) ^ 266216977173694316 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1331084885868471581) ^ 190154983695495940 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1331084885868471581) ^ 121007716897133780 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1331084885868471581) ^ 5053492556420 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1331084885868471581) ^ 405634460 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_1661214521791731001 : Nat.Prime 1661214521791731001 := by
  apply lucas_primality 1661214521791731001 (11 : ZMod 1661214521791731001)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 3), (389, 1), (4783, 1), (14327, 1), (20773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 3), (389, 1), (4783, 1), (14327, 1), (20773, 1)] : List FactorBlock).map factorBlockValue).prod) = 1661214521791731001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_389
      · exact prime_sixtyThreeBI_4783
      · exact prime_sixtyThreeBI_14327
      · exact prime_sixtyThreeBI_20773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1661214521791731001) ^ 830607260895865500 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (11 : ZMod 1661214521791731001) ^ 553738173930577000 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (11 : ZMod 1661214521791731001) ^ 332242904358346200 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (11 : ZMod 1661214521791731001) ^ 4270474349079000 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (11 : ZMod 1661214521791731001) ^ 347316437757000 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (11 : ZMod 1661214521791731001) ^ 115949921253000 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (11 : ZMod 1661214521791731001) ^ 79969889847000 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_2175175096714616371 : Nat.Prime 2175175096714616371 := by
  apply lucas_primality 2175175096714616371 (3 : ZMod 2175175096714616371)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (6591439687013989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (6591439687013989, 1)] : List FactorBlock).map factorBlockValue).prod) = 2175175096714616371 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_11
      · exact prime_sixtyThreeBI_6591439687013989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2175175096714616371) ^ 1087587548357308185 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2175175096714616371) ^ 725058365571538790 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2175175096714616371) ^ 435035019342923274 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2175175096714616371) ^ 197743190610419670 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2175175096714616371) ^ 330 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_3239603052866308333 : Nat.Prime 3239603052866308333 := by
  apply lucas_primality 3239603052866308333 (2 : ZMod 3239603052866308333)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (643, 1), (149333, 1), (104130997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (643, 1), (149333, 1), (104130997, 1)] : List FactorBlock).map factorBlockValue).prod) = 3239603052866308333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_643
      · exact prime_sixtyThreeBI_149333
      · exact prime_sixtyThreeBI_104130997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3239603052866308333) ^ 1619801526433154166 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3239603052866308333) ^ 1079867684288769444 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3239603052866308333) ^ 5038262912700324 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3239603052866308333) ^ 21693818867004 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3239603052866308333) ^ 31110842556 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_3503332992154976119 : Nat.Prime 3503332992154976119 := by
  apply lucas_primality 3503332992154976119 (3 : ZMod 3503332992154976119)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 9), (2857, 1), (31149414689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 9), (2857, 1), (31149414689, 1)] : List FactorBlock).map factorBlockValue).prod) = 3503332992154976119 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_2857
      · exact prime_sixtyThreeBI_31149414689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3503332992154976119) ^ 1751666496077488059 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 3503332992154976119) ^ 1167777664051658706 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 3503332992154976119) ^ 1226227858647174 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 3503332992154976119) ^ 112468662 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_6713142467534088109 : Nat.Prime 6713142467534088109 := by
  apply lucas_primality 6713142467534088109 (2 : ZMod 6713142467534088109)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (73243, 1), (449292916939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (73243, 1), (449292916939, 1)] : List FactorBlock).map factorBlockValue).prod) = 6713142467534088109 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_17
      · exact prime_sixtyThreeBI_73243
      · exact prime_sixtyThreeBI_449292916939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6713142467534088109) ^ 3356571233767044054 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6713142467534088109) ^ 2237714155844696036 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6713142467534088109) ^ 394890733384358124 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6713142467534088109) ^ 91655755055556 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6713142467534088109) ^ 14941572 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_6761905364525588117 : Nat.Prime 6761905364525588117 := by
  apply lucas_primality 6761905364525588117 (2 : ZMod 6761905364525588117)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (241496620161628147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (241496620161628147, 1)] : List FactorBlock).map factorBlockValue).prod) = 6761905364525588117 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_241496620161628147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6761905364525588117) ^ 3380952682262794058 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6761905364525588117) ^ 965986480646512588 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6761905364525588117) ^ 28 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_11086404698353855061 : Nat.Prime 11086404698353855061 := by
  apply lucas_primality 11086404698353855061 (2 : ZMod 11086404698353855061)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (3659, 1), (17207, 1), (19553, 1), (450277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (3659, 1), (17207, 1), (19553, 1), (450277, 1)] : List FactorBlock).map factorBlockValue).prod) = 11086404698353855061 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_3659
      · exact prime_sixtyThreeBI_17207
      · exact prime_sixtyThreeBI_19553
      · exact prime_sixtyThreeBI_450277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11086404698353855061) ^ 5543202349176927530 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 11086404698353855061) ^ 2217280939670771012 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 11086404698353855061) ^ 3029900163529340 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 11086404698353855061) ^ 644296199125580 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 11086404698353855061) ^ 566992517688020 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 11086404698353855061) ^ 24621299107780 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_11852538994599197281 : Nat.Prime 11852538994599197281 := by
  apply lucas_primality 11852538994599197281 (17 : ZMod 11852538994599197281)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (337, 1), (3433, 1), (21343539941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (337, 1), (3433, 1), (21343539941, 1)] : List FactorBlock).map factorBlockValue).prod) = 11852538994599197281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_337
      · exact prime_sixtyThreeBI_3433
      · exact prime_sixtyThreeBI_21343539941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 11852538994599197281) ^ 5926269497299598640 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (17 : ZMod 11852538994599197281) ^ 3950846331533065760 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (17 : ZMod 11852538994599197281) ^ 2370507798919839456 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (17 : ZMod 11852538994599197281) ^ 35170738856377440 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (17 : ZMod 11852538994599197281) ^ 3452531020856160 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (17 : ZMod 11852538994599197281) ^ 555322080 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_29574290822026163573 : Nat.Prime 29574290822026163573 := by
  apply lucas_primality 29574290822026163573 (2 : ZMod 29574290822026163573)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (9109, 1), (5366419, 1), (151251283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (9109, 1), (5366419, 1), (151251283, 1)] : List FactorBlock).map factorBlockValue).prod) = 29574290822026163573 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_9109
      · exact prime_sixtyThreeBI_5366419
      · exact prime_sixtyThreeBI_151251283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 29574290822026163573) ^ 14787145411013081786 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 29574290822026163573) ^ 3246711035462308 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 29574290822026163573) ^ 5510991747388 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 29574290822026163573) ^ 195530842684 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_37624872285977230769 : Nat.Prime 37624872285977230769 := by
  apply lucas_primality 37624872285977230769 (3 : ZMod 37624872285977230769)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (137, 1), (911, 1), (18841527461389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (137, 1), (911, 1), (18841527461389, 1)] : List FactorBlock).map factorBlockValue).prod) = 37624872285977230769 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_137
      · exact prime_sixtyThreeBI_911
      · exact prime_sixtyThreeBI_18841527461389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 37624872285977230769) ^ 18812436142988615384 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 37624872285977230769) ^ 274634104277206064 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 37624872285977230769) ^ 41300628195364688 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 37624872285977230769) ^ 1996912 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_97676786769025262377 : Nat.Prime 97676786769025262377 := by
  apply lucas_primality 97676786769025262377 (7 : ZMod 97676786769025262377)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (61, 1), (66719116645509059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (61, 1), (66719116645509059, 1)] : List FactorBlock).map factorBlockValue).prod) = 97676786769025262377 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_61
      · exact prime_sixtyThreeBI_66719116645509059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 97676786769025262377) ^ 48838393384512631188 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 97676786769025262377) ^ 32558928923008420792 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 97676786769025262377) ^ 1601258799492217416 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 97676786769025262377) ^ 1464 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_106153385209219618873 : Nat.Prime 106153385209219618873 := by
  apply lucas_primality 106153385209219618873 (10 : ZMod 106153385209219618873)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (1429, 1), (6315073, 1), (70018687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (1429, 1), (6315073, 1), (70018687, 1)] : List FactorBlock).map factorBlockValue).prod) = 106153385209219618873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_1429
      · exact prime_sixtyThreeBI_6315073
      · exact prime_sixtyThreeBI_70018687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 106153385209219618873) ^ 53076692604609809436 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (10 : ZMod 106153385209219618873) ^ 35384461736406539624 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (10 : ZMod 106153385209219618873) ^ 15164769315602802696 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (10 : ZMod 106153385209219618873) ^ 74285084121217368 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (10 : ZMod 106153385209219618873) ^ 16809526225464 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (10 : ZMod 106153385209219618873) ^ 1516072205256 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_288246522157200231587 : Nat.Prime 288246522157200231587 := by
  apply lucas_primality 288246522157200231587 (2 : ZMod 288246522157200231587)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (11086404698353855061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (11086404698353855061, 1)] : List FactorBlock).map factorBlockValue).prod) = 288246522157200231587 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_13
      · exact prime_sixtyThreeBI_11086404698353855061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 288246522157200231587) ^ 144123261078600115793 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 288246522157200231587) ^ 22172809396707710122 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 288246522157200231587) ^ 26 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_365517915091932547283 : Nat.Prime 365517915091932547283 := by
  apply lucas_primality 365517915091932547283 (2 : ZMod 365517915091932547283)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (29, 1), (484771770678955633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (29, 1), (484771770678955633, 1)] : List FactorBlock).map factorBlockValue).prod) = 365517915091932547283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_13
      · exact prime_sixtyThreeBI_29
      · exact prime_sixtyThreeBI_484771770678955633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 365517915091932547283) ^ 182758957545966273641 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 365517915091932547283) ^ 28116762699379426714 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 365517915091932547283) ^ 12604066037652846458 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 365517915091932547283) ^ 754 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_388752366343956999961 : Nat.Prime 388752366343956999961 := by
  apply lucas_primality 388752366343956999961 (7 : ZMod 388752366343956999961)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (3239603052866308333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (3239603052866308333, 1)] : List FactorBlock).map factorBlockValue).prod) = 388752366343956999961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_3239603052866308333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 388752366343956999961) ^ 194376183171978499980 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 388752366343956999961) ^ 129584122114652333320 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 388752366343956999961) ^ 77750473268791399992 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 388752366343956999961) ^ 120 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_424462304839999935337 : Nat.Prime 424462304839999935337 := by
  apply lucas_primality 424462304839999935337 (5 : ZMod 424462304839999935337)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (101, 1), (157, 1), (5752939, 1), (193872893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (101, 1), (157, 1), (5752939, 1), (193872893, 1)] : List FactorBlock).map factorBlockValue).prod) = 424462304839999935337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_101
      · exact prime_sixtyThreeBI_157
      · exact prime_sixtyThreeBI_5752939
      · exact prime_sixtyThreeBI_193872893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 424462304839999935337) ^ 212231152419999967668 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 424462304839999935337) ^ 141487434946666645112 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 424462304839999935337) ^ 4202597077623761736 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 424462304839999935337) ^ 2703581559490445448 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 424462304839999935337) ^ 73781819143224 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 424462304839999935337) ^ 2189384489352 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_544023875862398683421 : Nat.Prime 544023875862398683421 := by
  apply lucas_primality 544023875862398683421 (2 : ZMod 544023875862398683421)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (83, 1), (13597, 1), (24102759904621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (83, 1), (13597, 1), (24102759904621, 1)] : List FactorBlock).map factorBlockValue).prod) = 544023875862398683421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_83
      · exact prime_sixtyThreeBI_13597
      · exact prime_sixtyThreeBI_24102759904621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 544023875862398683421) ^ 272011937931199341710 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 544023875862398683421) ^ 108804775172479736684 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 544023875862398683421) ^ 6554504528462634740 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 544023875862398683421) ^ 40010581441670860 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 544023875862398683421) ^ 22571020 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_732694647676733050313 : Nat.Prime 732694647676733050313 := by
  apply lucas_primality 732694647676733050313 (3 : ZMod 732694647676733050313)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (233, 1), (174042031, 1), (2258514943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (233, 1), (174042031, 1), (2258514943, 1)] : List FactorBlock).map factorBlockValue).prod) = 732694647676733050313 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_233
      · exact prime_sixtyThreeBI_174042031
      · exact prime_sixtyThreeBI_2258514943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 732694647676733050313) ^ 366347323838366525156 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 732694647676733050313) ^ 3144612221788553864 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 732694647676733050313) ^ 4209871853752 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 732694647676733050313) ^ 324414345784 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_1088047751724797366843 : Nat.Prime 1088047751724797366843 := by
  apply lucas_primality 1088047751724797366843 (2 : ZMod 1088047751724797366843)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (544023875862398683421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (544023875862398683421, 1)] : List FactorBlock).map factorBlockValue).prod) = 1088047751724797366843 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_544023875862398683421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1088047751724797366843) ^ 544023875862398683421 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1088047751724797366843) ^ 2 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_1678456136902353239411 : Nat.Prime 1678456136902353239411 := by
  apply lucas_primality 1678456136902353239411 (7 : ZMod 1678456136902353239411)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (825427819, 1), (29049111577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (825427819, 1), (29049111577, 1)] : List FactorBlock).map factorBlockValue).prod) = 1678456136902353239411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_825427819
      · exact prime_sixtyThreeBI_29049111577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1678456136902353239411) ^ 839228068451176619705 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1678456136902353239411) ^ 335691227380470647882 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1678456136902353239411) ^ 239779448128907605630 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1678456136902353239411) ^ 2033437810390 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1678456136902353239411) ^ 57779947330 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_2474038892245021576877 : Nat.Prime 2474038892245021576877 := by
  apply lucas_primality 2474038892245021576877 (2 : ZMod 2474038892245021576877)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (307, 1), (124427, 1), (852196850009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (307, 1), (124427, 1), (852196850009, 1)] : List FactorBlock).map factorBlockValue).prod) = 2474038892245021576877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_19
      · exact prime_sixtyThreeBI_307
      · exact prime_sixtyThreeBI_124427
      · exact prime_sixtyThreeBI_852196850009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2474038892245021576877) ^ 1237019446122510788438 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2474038892245021576877) ^ 130212573276053767204 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2474038892245021576877) ^ 8058758606661308068 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2474038892245021576877) ^ 19883456904409988 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2474038892245021576877) ^ 2903130764 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_4267059584444760912943 : Nat.Prime 4267059584444760912943 := by
  apply lucas_primality 4267059584444760912943 (19 : ZMod 4267059584444760912943)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (29, 1), (3503332992154976119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (29, 1), (3503332992154976119, 1)] : List FactorBlock).map factorBlockValue).prod) = 4267059584444760912943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_29
      · exact prime_sixtyThreeBI_3503332992154976119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 4267059584444760912943) ^ 2133529792222380456471 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (19 : ZMod 4267059584444760912943) ^ 1422353194814920304314 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (19 : ZMod 4267059584444760912943) ^ 609579940634965844706 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (19 : ZMod 4267059584444760912943) ^ 147139985670508996998 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (19 : ZMod 4267059584444760912943) ^ 1218 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_4665028396127483999533 : Nat.Prime 4665028396127483999533 := by
  apply lucas_primality 4665028396127483999533 (5 : ZMod 4665028396127483999533)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (388752366343956999961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (388752366343956999961, 1)] : List FactorBlock).map factorBlockValue).prod) = 4665028396127483999533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_388752366343956999961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 4665028396127483999533) ^ 2332514198063741999766 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 4665028396127483999533) ^ 1555009465375827999844 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 4665028396127483999533) ^ 12 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_4799252103893040261821 : Nat.Prime 4799252103893040261821 := by
  apply lucas_primality 4799252103893040261821 (2 : ZMod 4799252103893040261821)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (16091, 1), (1355713273906091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (16091, 1), (1355713273906091, 1)] : List FactorBlock).map factorBlockValue).prod) = 4799252103893040261821 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_11
      · exact prime_sixtyThreeBI_16091
      · exact prime_sixtyThreeBI_1355713273906091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4799252103893040261821) ^ 2399626051946520130910 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4799252103893040261821) ^ 959850420778608052364 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4799252103893040261821) ^ 436295645808458205620 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4799252103893040261821) ^ 298256920259340020 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4799252103893040261821) ^ 3540020 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_9719100638539293676327 : Nat.Prime 9719100638539293676327 := by
  apply lucas_primality 9719100638539293676327 (3 : ZMod 9719100638539293676327)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 2), (109, 1), (6299, 1), (8163546666479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 2), (109, 1), (6299, 1), (8163546666479, 1)] : List FactorBlock).map factorBlockValue).prod) = 9719100638539293676327 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_17
      · exact prime_sixtyThreeBI_109
      · exact prime_sixtyThreeBI_6299
      · exact prime_sixtyThreeBI_8163546666479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9719100638539293676327) ^ 4859550319269646838163 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 9719100638539293676327) ^ 3239700212846431225442 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 9719100638539293676327) ^ 571711802267017275078 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 9719100638539293676327) ^ 89166060904030217214 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 9719100638539293676327) ^ 1542959301244529874 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 9719100638539293676327) ^ 1190548794 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_10295075703333582691051 : Nat.Prime 10295075703333582691051 := by
  apply lucas_primality 10295075703333582691051 (7 : ZMod 10295075703333582691051)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (1669, 1), (41122730989948403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (1669, 1), (41122730989948403, 1)] : List FactorBlock).map factorBlockValue).prod) = 10295075703333582691051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_1669
      · exact prime_sixtyThreeBI_41122730989948403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 10295075703333582691051) ^ 5147537851666791345525 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 10295075703333582691051) ^ 3431691901111194230350 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 10295075703333582691051) ^ 2059015140666716538210 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 10295075703333582691051) ^ 6168409648492260450 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 10295075703333582691051) ^ 250350 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_13835833063545611116177 : Nat.Prime 13835833063545611116177 := by
  apply lucas_primality 13835833063545611116177 (5 : ZMod 13835833063545611116177)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (288246522157200231587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (288246522157200231587, 1)] : List FactorBlock).map factorBlockValue).prod) = 13835833063545611116177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_288246522157200231587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 13835833063545611116177) ^ 6917916531772805558088 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 13835833063545611116177) ^ 4611944354515203705392 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 13835833063545611116177) ^ 48 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_19584742804424439629633 : Nat.Prime 19584742804424439629633 := by
  apply lucas_primality 19584742804424439629633 (3 : ZMod 19584742804424439629633)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (59, 1), (2753, 1), (70079, 1), (26883869561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (59, 1), (2753, 1), (70079, 1), (26883869561, 1)] : List FactorBlock).map factorBlockValue).prod) = 19584742804424439629633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_59
      · exact prime_sixtyThreeBI_2753
      · exact prime_sixtyThreeBI_70079
      · exact prime_sixtyThreeBI_26883869561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 19584742804424439629633) ^ 9792371402212219814816 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 19584742804424439629633) ^ 331944793295329485248 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 19584742804424439629633) ^ 7113963968189044544 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 19584742804424439629633) ^ 279466641995811008 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 19584742804424439629633) ^ 728494190912 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_23099514487661021864693 : Nat.Prime 23099514487661021864693 := by
  apply lucas_primality 23099514487661021864693 (2 : ZMod 23099514487661021864693)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (507169501, 1), (1626640913239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (507169501, 1), (1626640913239, 1)] : List FactorBlock).map factorBlockValue).prod) = 23099514487661021864693 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_507169501
      · exact prime_sixtyThreeBI_1626640913239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 23099514487661021864693) ^ 11549757243830510932346 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 23099514487661021864693) ^ 3299930641094431694956 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 23099514487661021864693) ^ 45545945570692 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 23099514487661021864693) ^ 14200746028 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_25633019677444243595761 : Nat.Prime 25633019677444243595761 := by
  apply lucas_primality 25633019677444243595761 (7 : ZMod 25633019677444243595761)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (7621, 1), (14014466429079869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (7621, 1), (14014466429079869, 1)] : List FactorBlock).map factorBlockValue).prod) = 25633019677444243595761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_7621
      · exact prime_sixtyThreeBI_14014466429079869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 25633019677444243595761) ^ 12816509838722121797880 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 25633019677444243595761) ^ 8544339892481414531920 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 25633019677444243595761) ^ 5126603935488848719152 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 25633019677444243595761) ^ 3363471942979168560 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 25633019677444243595761) ^ 1829040 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_58620928406526293462861 : Nat.Prime 58620928406526293462861 := by
  apply lucas_primality 58620928406526293462861 (2 : ZMod 58620928406526293462861)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (22671689, 1), (129282225965887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (22671689, 1), (129282225965887, 1)] : List FactorBlock).map factorBlockValue).prod) = 58620928406526293462861 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_22671689
      · exact prime_sixtyThreeBI_129282225965887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 58620928406526293462861) ^ 29310464203263146731430 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 58620928406526293462861) ^ 11724185681305258692572 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 58620928406526293462861) ^ 2585644519317740 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 58620928406526293462861) ^ 453433780 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_101822585083825207592681 : Nat.Prime 101822585083825207592681 := by
  apply lucas_primality 101822585083825207592681 (3 : ZMod 101822585083825207592681)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (2063, 1), (1233914021859248759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (2063, 1), (1233914021859248759, 1)] : List FactorBlock).map factorBlockValue).prod) = 101822585083825207592681 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_2063
      · exact prime_sixtyThreeBI_1233914021859248759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 101822585083825207592681) ^ 50911292541912603796340 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 101822585083825207592681) ^ 20364517016765041518536 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 101822585083825207592681) ^ 49356560874369950360 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 101822585083825207592681) ^ 82520 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_128723808508926859456843 : Nat.Prime 128723808508926859456843 := by
  apply lucas_primality 128723808508926859456843 (3 : ZMod 128723808508926859456843)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (775757, 1), (10971929, 1), (2520571019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (775757, 1), (10971929, 1), (2520571019, 1)] : List FactorBlock).map factorBlockValue).prod) = 128723808508926859456843 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_775757
      · exact prime_sixtyThreeBI_10971929
      · exact prime_sixtyThreeBI_2520571019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 128723808508926859456843) ^ 64361904254463429728421 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 128723808508926859456843) ^ 42907936169642286485614 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 128723808508926859456843) ^ 165933157559553906 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 128723808508926859456843) ^ 11732103671918298 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 128723808508926859456843) ^ 51069304351518 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_137542705689447032091253 : Nat.Prime 137542705689447032091253 := by
  apply lucas_primality 137542705689447032091253 (2 : ZMod 137542705689447032091253)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (103, 1), (379, 1), (683, 1), (18690948590087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (103, 1), (379, 1), (683, 1), (18690948590087, 1)] : List FactorBlock).map factorBlockValue).prod) = 137542705689447032091253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_23
      · exact prime_sixtyThreeBI_103
      · exact prime_sixtyThreeBI_379
      · exact prime_sixtyThreeBI_683
      · exact prime_sixtyThreeBI_18690948590087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 137542705689447032091253) ^ 68771352844723516045626 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 137542705689447032091253) ^ 45847568563149010697084 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 137542705689447032091253) ^ 5980117638671610090924 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 137542705689447032091253) ^ 1335366074654825554284 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 137542705689447032091253) ^ 362909513692472380188 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 137542705689447032091253) ^ 201380242590698436444 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 137542705689447032091253) ^ 7358786796 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_189974707635373046069207 : Nat.Prime 189974707635373046069207 := by
  apply lucas_primality 189974707635373046069207 (5 : ZMod 189974707635373046069207)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (647, 1), (10433, 1), (343216726153333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (647, 1), (10433, 1), (343216726153333, 1)] : List FactorBlock).map factorBlockValue).prod) = 189974707635373046069207 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_41
      · exact prime_sixtyThreeBI_647
      · exact prime_sixtyThreeBI_10433
      · exact prime_sixtyThreeBI_343216726153333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 189974707635373046069207) ^ 94987353817686523034603 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 189974707635373046069207) ^ 4633529454521293806566 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 189974707635373046069207) ^ 293623968524533301498 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 189974707635373046069207) ^ 18209020189338928982 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 189974707635373046069207) ^ 553512382 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_224025980072059180727563 : Nat.Prime 224025980072059180727563 := by
  apply lucas_primality 224025980072059180727563 (2 : ZMod 224025980072059180727563)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (126251557, 1), (295740220814411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (126251557, 1), (295740220814411, 1)] : List FactorBlock).map factorBlockValue).prod) = 224025980072059180727563 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_126251557
      · exact prime_sixtyThreeBI_295740220814411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 224025980072059180727563) ^ 112012990036029590363781 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 224025980072059180727563) ^ 74675326690686393575854 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 224025980072059180727563) ^ 1774441324886466 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 224025980072059180727563) ^ 757509342 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_228099154761873245767603 : Nat.Prime 228099154761873245767603 := by
  apply lucas_primality 228099154761873245767603 (2 : ZMod 228099154761873245767603)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (809, 1), (6713142467534088109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (809, 1), (6713142467534088109, 1)] : List FactorBlock).map factorBlockValue).prod) = 228099154761873245767603 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_809
      · exact prime_sixtyThreeBI_6713142467534088109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 228099154761873245767603) ^ 114049577380936622883801 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 228099154761873245767603) ^ 76033051587291081922534 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 228099154761873245767603) ^ 32585593537410463681086 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 228099154761873245767603) ^ 281951983636431700578 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 228099154761873245767603) ^ 33978 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_322830527737228148879653 : Nat.Prime 322830527737228148879653 := by
  apply lucas_primality 322830527737228148879653 (2 : ZMod 322830527737228148879653)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (38377, 1), (701006956721534923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (38377, 1), (701006956721534923, 1)] : List FactorBlock).map factorBlockValue).prod) = 322830527737228148879653 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_38377
      · exact prime_sixtyThreeBI_701006956721534923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 322830527737228148879653) ^ 161415263868614074439826 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 322830527737228148879653) ^ 107610175912409382959884 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 322830527737228148879653) ^ 8412083480658419076 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 322830527737228148879653) ^ 460524 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_344615647302715476365089 : Nat.Prime 344615647302715476365089 := by
  apply lucas_primality 344615647302715476365089 (7 : ZMod 344615647302715476365089)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (23, 1), (37, 2), (229, 1), (497848259560361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (23, 1), (37, 2), (229, 1), (497848259560361, 1)] : List FactorBlock).map factorBlockValue).prod) = 344615647302715476365089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_23
      · exact prime_sixtyThreeBI_37
      · exact prime_sixtyThreeBI_229
      · exact prime_sixtyThreeBI_497848259560361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 344615647302715476365089) ^ 172307823651357738182544 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 344615647302715476365089) ^ 114871882434238492121696 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 344615647302715476365089) ^ 14983289013161542450656 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 344615647302715476365089) ^ 9313936413586904766624 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 344615647302715476365089) ^ 1504871822282600333472 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 344615647302715476365089) ^ 692210208 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_716877098898717062274091 : Nat.Prime 716877098898717062274091 := by
  apply lucas_primality 716877098898717062274091 (2 : ZMod 716877098898717062274091)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (83, 1), (173, 1), (111728269, 1), (14894851793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (83, 1), (173, 1), (111728269, 1), (14894851793, 1)] : List FactorBlock).map factorBlockValue).prod) = 716877098898717062274091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_83
      · exact prime_sixtyThreeBI_173
      · exact prime_sixtyThreeBI_111728269
      · exact prime_sixtyThreeBI_14894851793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 716877098898717062274091) ^ 358438549449358531137045 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 716877098898717062274091) ^ 238959032966239020758030 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 716877098898717062274091) ^ 143375419779743412454818 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 716877098898717062274091) ^ 8637073480707434485230 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 716877098898717062274091) ^ 4143798259530156429330 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 716877098898717062274091) ^ 6416255306870610 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 716877098898717062274091) ^ 48129186437130 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_834719029244072172823523 : Nat.Prime 834719029244072172823523 := by
  apply lucas_primality 834719029244072172823523 (2 : ZMod 834719029244072172823523)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (1344071269, 1), (18265816887757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (1344071269, 1), (18265816887757, 1)] : List FactorBlock).map factorBlockValue).prod) = 834719029244072172823523 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_17
      · exact prime_sixtyThreeBI_1344071269
      · exact prime_sixtyThreeBI_18265816887757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 834719029244072172823523) ^ 417359514622036086411761 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 834719029244072172823523) ^ 49101119367298363107266 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 834719029244072172823523) ^ 621037774183738 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 834719029244072172823523) ^ 45698423146 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_1968882201915881682612101 : Nat.Prime 1968882201915881682612101 := by
  apply lucas_primality 1968882201915881682612101 (3 : ZMod 1968882201915881682612101)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (23, 1), (31, 1), (2819, 1), (9795692134747243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (23, 1), (31, 1), (2819, 1), (9795692134747243, 1)] : List FactorBlock).map factorBlockValue).prod) = 1968882201915881682612101 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_23
      · exact prime_sixtyThreeBI_31
      · exact prime_sixtyThreeBI_2819
      · exact prime_sixtyThreeBI_9795692134747243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1968882201915881682612101) ^ 984441100957940841306050 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1968882201915881682612101) ^ 393776440383176336522420 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1968882201915881682612101) ^ 85603573996342681852700 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1968882201915881682612101) ^ 63512329094060699439100 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1968882201915881682612101) ^ 698432849207478425900 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1968882201915881682612101) ^ 200994700 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_2716467183284503594340267 : Nat.Prime 2716467183284503594340267 := by
  apply lucas_primality 2716467183284503594340267 (2 : ZMod 2716467183284503594340267)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (7993, 1), (10247, 1), (377183, 1), (829544977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (7993, 1), (10247, 1), (377183, 1), (829544977, 1)] : List FactorBlock).map factorBlockValue).prod) = 2716467183284503594340267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_53
      · exact prime_sixtyThreeBI_7993
      · exact prime_sixtyThreeBI_10247
      · exact prime_sixtyThreeBI_377183
      · exact prime_sixtyThreeBI_829544977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2716467183284503594340267) ^ 1358233591642251797170133 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2716467183284503594340267) ^ 51254097797820822534722 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2716467183284503594340267) ^ 339855771710809907962 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2716467183284503594340267) ^ 265098778499512403078 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2716467183284503594340267) ^ 7201987319907057302 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2716467183284503594340267) ^ 3274647256750858 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_3606042783755884969896673 : Nat.Prime 3606042783755884969896673 := by
  apply lucas_primality 3606042783755884969896673 (5 : ZMod 3606042783755884969896673)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (13, 1), (89, 1), (911, 1), (997, 1), (5106398546429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (13, 1), (89, 1), (911, 1), (997, 1), (5106398546429, 1)] : List FactorBlock).map factorBlockValue).prod) = 3606042783755884969896673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_13
      · exact prime_sixtyThreeBI_89
      · exact prime_sixtyThreeBI_911
      · exact prime_sixtyThreeBI_997
      · exact prime_sixtyThreeBI_5106398546429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3606042783755884969896673) ^ 1803021391877942484948336 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 3606042783755884969896673) ^ 1202014261251961656632224 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 3606042783755884969896673) ^ 515148969107983567128096 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 3606042783755884969896673) ^ 277387906442760382299744 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 3606042783755884969896673) ^ 40517334648942527751648 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 3606042783755884969896673) ^ 3958334559556405016352 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 3606042783755884969896673) ^ 3616893464148329959776 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 3606042783755884969896673) ^ 706181225568 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_4553017525428070423205317 : Nat.Prime 4553017525428070423205317 := by
  apply lucas_primality 4553017525428070423205317 (5 : ZMod 4553017525428070423205317)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (17, 1), (181, 1), (111616187, 1), (100431676487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (17, 1), (181, 1), (111616187, 1), (100431676487, 1)] : List FactorBlock).map factorBlockValue).prod) = 4553017525428070423205317 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_11
      · exact prime_sixtyThreeBI_17
      · exact prime_sixtyThreeBI_181
      · exact prime_sixtyThreeBI_111616187
      · exact prime_sixtyThreeBI_100431676487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4553017525428070423205317) ^ 2276508762714035211602658 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 4553017525428070423205317) ^ 1517672508476023474401772 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 4553017525428070423205317) ^ 413910684129824583927756 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 4553017525428070423205317) ^ 267824560319298260188548 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 4553017525428070423205317) ^ 25154792958166134934836 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 4553017525428070423205317) ^ 40791731448665868 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 4553017525428070423205317) ^ 45334476976668 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_4679450505652937365911653 : Nat.Prime 4679450505652937365911653 := by
  apply lucas_primality 4679450505652937365911653 (2 : ZMod 4679450505652937365911653)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (2819237329, 1), (14308866497693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (2819237329, 1), (14308866497693, 1)] : List FactorBlock).map factorBlockValue).prod) = 4679450505652937365911653 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_29
      · exact prime_sixtyThreeBI_2819237329
      · exact prime_sixtyThreeBI_14308866497693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4679450505652937365911653) ^ 2339725252826468682955826 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4679450505652937365911653) ^ 161360362263894391927988 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4679450505652937365911653) ^ 1659828513732388 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4679450505652937365911653) ^ 327031530164 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_10471364220227443280362123 : Nat.Prime 10471364220227443280362123 := by
  apply lucas_primality 10471364220227443280362123 (2 : ZMod 10471364220227443280362123)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (409, 1), (4267059584444760912943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (409, 1), (4267059584444760912943, 1)] : List FactorBlock).map factorBlockValue).prod) = 10471364220227443280362123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_409
      · exact prime_sixtyThreeBI_4267059584444760912943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10471364220227443280362123) ^ 5235682110113721640181061 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 10471364220227443280362123) ^ 3490454740075814426787374 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 10471364220227443280362123) ^ 25602357506668565477658 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 10471364220227443280362123) ^ 2454 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_12354090844000299229261201 : Nat.Prime 12354090844000299229261201 := by
  apply lucas_primality 12354090844000299229261201 (11 : ZMod 12354090844000299229261201)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 2), (10295075703333582691051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 2), (10295075703333582691051, 1)] : List FactorBlock).map factorBlockValue).prod) = 12354090844000299229261201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_10295075703333582691051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 12354090844000299229261201) ^ 6177045422000149614630600 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (11 : ZMod 12354090844000299229261201) ^ 4118030281333433076420400 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (11 : ZMod 12354090844000299229261201) ^ 2470818168800059845852240 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (11 : ZMod 12354090844000299229261201) ^ 1200 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_15517252853849542511086621 : Nat.Prime 15517252853849542511086621 := by
  apply lucas_primality 15517252853849542511086621 (7 : ZMod 15517252853849542511086621)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (66622273, 1), (3881898188875849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (66622273, 1), (3881898188875849, 1)] : List FactorBlock).map factorBlockValue).prod) = 15517252853849542511086621 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_66622273
      · exact prime_sixtyThreeBI_3881898188875849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 15517252853849542511086621) ^ 7758626426924771255543310 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 15517252853849542511086621) ^ 5172417617949847503695540 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 15517252853849542511086621) ^ 3103450570769908502217324 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 15517252853849542511086621) ^ 232913891332550940 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (7 : ZMod 15517252853849542511086621) ^ 3997336380 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_47081424588165489287747017 : Nat.Prime 47081424588165489287747017 := by
  apply lucas_primality 47081424588165489287747017 (17 : ZMod 47081424588165489287747017)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (353, 1), (509, 1), (519908084933067827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (353, 1), (509, 1), (519908084933067827, 1)] : List FactorBlock).map factorBlockValue).prod) = 47081424588165489287747017 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_353
      · exact prime_sixtyThreeBI_509
      · exact prime_sixtyThreeBI_519908084933067827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 47081424588165489287747017) ^ 23540712294082744643873508 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (17 : ZMod 47081424588165489287747017) ^ 15693808196055163095915672 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (17 : ZMod 47081424588165489287747017) ^ 6725917798309355612535288 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (17 : ZMod 47081424588165489287747017) ^ 133375140476389488067272 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (17 : ZMod 47081424588165489287747017) ^ 92497887206611963237224 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (17 : ZMod 47081424588165489287747017) ^ 90557208 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_49196046035982697525241599 : Nat.Prime 49196046035982697525241599 := by
  apply lucas_primality 49196046035982697525241599 (3 : ZMod 49196046035982697525241599)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1259, 1), (4037895899, 1), (1612865308013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1259, 1), (4037895899, 1), (1612865308013, 1)] : List FactorBlock).map factorBlockValue).prod) = 49196046035982697525241599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_1259
      · exact prime_sixtyThreeBI_4037895899
      · exact prime_sixtyThreeBI_1612865308013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 49196046035982697525241599) ^ 24598023017991348762620799 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 49196046035982697525241599) ^ 16398682011994232508413866 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 49196046035982697525241599) ^ 39075493277190387232122 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 49196046035982697525241599) ^ 12183584536730202 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 49196046035982697525241599) ^ 30502265621046 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_50634135756952959927407057 : Nat.Prime 50634135756952959927407057 := by
  apply lucas_primality 50634135756952959927407057 (3 : ZMod 50634135756952959927407057)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (137, 1), (23099514487661021864693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (137, 1), (23099514487661021864693, 1)] : List FactorBlock).map factorBlockValue).prod) = 50634135756952959927407057 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_137
      · exact prime_sixtyThreeBI_23099514487661021864693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 50634135756952959927407057) ^ 25317067878476479963703528 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 50634135756952959927407057) ^ 369592231802576349835088 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 50634135756952959927407057) ^ 2192 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_102452288443573320568384843 : Nat.Prime 102452288443573320568384843 := by
  apply lucas_primality 102452288443573320568384843 (2 : ZMod 102452288443573320568384843)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (241, 1), (7681, 1), (486858187, 1), (18946680341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (241, 1), (7681, 1), (486858187, 1), (18946680341, 1)] : List FactorBlock).map factorBlockValue).prod) = 102452288443573320568384843 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_241
      · exact prime_sixtyThreeBI_7681
      · exact prime_sixtyThreeBI_486858187
      · exact prime_sixtyThreeBI_18946680341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 102452288443573320568384843) ^ 51226144221786660284192421 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 102452288443573320568384843) ^ 34150762814524440189461614 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 102452288443573320568384843) ^ 425113230056320832233962 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 102452288443573320568384843) ^ 13338404952945361355082 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 102452288443573320568384843) ^ 210435587157073566 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 102452288443573320568384843) ^ 5407400483865762 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_104317666244366672343439469 : Nat.Prime 104317666244366672343439469 := by
  apply lucas_primality 104317666244366672343439469 (3 : ZMod 104317666244366672343439469)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (2179, 1), (1088047751724797366843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (2179, 1), (1088047751724797366843, 1)] : List FactorBlock).map factorBlockValue).prod) = 104317666244366672343439469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_11
      · exact prime_sixtyThreeBI_2179
      · exact prime_sixtyThreeBI_1088047751724797366843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 104317666244366672343439469) ^ 52158833122183336171719734 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 104317666244366672343439469) ^ 9483424204033333849403588 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 104317666244366672343439469) ^ 47874101075891084141092 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 104317666244366672343439469) ^ 95876 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_264123452831481574656793549 : Nat.Prime 264123452831481574656793549 := by
  apply lucas_primality 264123452831481574656793549 (2 : ZMod 264123452831481574656793549)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (1225327, 1), (7256369, 1), (107628310121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (1225327, 1), (7256369, 1), (107628310121, 1)] : List FactorBlock).map factorBlockValue).prod) = 264123452831481574656793549 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_23
      · exact prime_sixtyThreeBI_1225327
      · exact prime_sixtyThreeBI_7256369
      · exact prime_sixtyThreeBI_107628310121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 264123452831481574656793549) ^ 132061726415740787328396774 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 264123452831481574656793549) ^ 88041150943827191552264516 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 264123452831481574656793549) ^ 11483628383977459767686676 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 264123452831481574656793549) ^ 215553442331297339124 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 264123452831481574656793549) ^ 36398845322155140492 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 264123452831481574656793549) ^ 2454033260714988 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_266963489958701806642350469 : Nat.Prime 266963489958701806642350469 := by
  apply lucas_primality 266963489958701806642350469 (10 : ZMod 266963489958701806642350469)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (7, 1), (260723, 1), (37469867, 1), (12048897911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (7, 1), (260723, 1), (37469867, 1), (12048897911, 1)] : List FactorBlock).map factorBlockValue).prod) = 266963489958701806642350469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_260723
      · exact prime_sixtyThreeBI_37469867
      · exact prime_sixtyThreeBI_12048897911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 266963489958701806642350469) ^ 133481744979350903321175234 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (10 : ZMod 266963489958701806642350469) ^ 88987829986233935547450156 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (10 : ZMod 266963489958701806642350469) ^ 38137641422671686663192924 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (10 : ZMod 266963489958701806642350469) ^ 1023935325838924094316 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (10 : ZMod 266963489958701806642350469) ^ 7124751469192613004 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (10 : ZMod 266963489958701806642350469) ^ 22156672911551388 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_836885547173907910710289673 : Nat.Prime 836885547173907910710289673 := by
  apply lucas_primality 836885547173907910710289673 (3 : ZMod 836885547173907910710289673)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (79, 1), (19139, 1), (468558613, 1), (147661005553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (79, 1), (19139, 1), (468558613, 1), (147661005553, 1)] : List FactorBlock).map factorBlockValue).prod) = 836885547173907910710289673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_79
      · exact prime_sixtyThreeBI_19139
      · exact prime_sixtyThreeBI_468558613
      · exact prime_sixtyThreeBI_147661005553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 836885547173907910710289673) ^ 418442773586953955355144836 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 836885547173907910710289673) ^ 10593487938910226717851768 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 836885547173907910710289673) ^ 43726712324254554089048 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 836885547173907910710289673) ^ 1786085078696243944 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 836885547173907910710289673) ^ 5667613761938824 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_856124295384802345439261849 : Nat.Prime 856124295384802345439261849 := by
  apply lucas_primality 856124295384802345439261849 (3 : ZMod 856124295384802345439261849)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1051, 1), (101822585083825207592681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1051, 1), (101822585083825207592681, 1)] : List FactorBlock).map factorBlockValue).prod) = 856124295384802345439261849 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_1051
      · exact prime_sixtyThreeBI_101822585083825207592681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 856124295384802345439261849) ^ 428062147692401172719630924 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 856124295384802345439261849) ^ 814580680670601660741448 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 856124295384802345439261849) ^ 8408 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_1551725285384954251108662101 : Nat.Prime 1551725285384954251108662101 := by
  apply lucas_primality 1551725285384954251108662101 (2 : ZMod 1551725285384954251108662101)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (15517252853849542511086621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (15517252853849542511086621, 1)] : List FactorBlock).map factorBlockValue).prod) = 1551725285384954251108662101 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_15517252853849542511086621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1551725285384954251108662101) ^ 775862642692477125554331050 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1551725285384954251108662101) ^ 310345057076990850221732420 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1551725285384954251108662101) ^ 100 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_1960074044696784317189888969 : Nat.Prime 1960074044696784317189888969 := by
  apply lucas_primality 1960074044696784317189888969 (3 : ZMod 1960074044696784317189888969)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (37, 1), (4974793, 1), (1331084885868471581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (37, 1), (4974793, 1), (1331084885868471581, 1)] : List FactorBlock).map factorBlockValue).prod) = 1960074044696784317189888969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_37
      · exact prime_sixtyThreeBI_4974793
      · exact prime_sixtyThreeBI_1331084885868471581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1960074044696784317189888969) ^ 980037022348392158594944484 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1960074044696784317189888969) ^ 52974974180994170734861864 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1960074044696784317189888969) ^ 394001126217067587976 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1960074044696784317189888969) ^ 1472538728 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_4137934094359878002956432267 : Nat.Prime 4137934094359878002956432267 := by
  apply lucas_primality 4137934094359878002956432267 (5 : ZMod 4137934094359878002956432267)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31883, 1), (428693, 1), (19972319, 1), (2526377551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31883, 1), (428693, 1), (19972319, 1), (2526377551, 1)] : List FactorBlock).map factorBlockValue).prod) = 4137934094359878002956432267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_31883
      · exact prime_sixtyThreeBI_428693
      · exact prime_sixtyThreeBI_19972319
      · exact prime_sixtyThreeBI_2526377551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4137934094359878002956432267) ^ 2068967047179939001478216133 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 4137934094359878002956432267) ^ 1379311364786626000985477422 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 4137934094359878002956432267) ^ 129784966733365053569502 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 4137934094359878002956432267) ^ 9652441477607234088162 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 4137934094359878002956432267) ^ 207183456981629324214 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (5 : ZMod 4137934094359878002956432267) ^ 1637892203689818966 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_5320200978462700289515412917 : Nat.Prime 5320200978462700289515412917 := by
  apply lucas_primality 5320200978462700289515412917 (2 : ZMod 5320200978462700289515412917)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (2521, 1), (58620928406526293462861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (2521, 1), (58620928406526293462861, 1)] : List FactorBlock).map factorBlockValue).prod) = 5320200978462700289515412917 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_2521
      · exact prime_sixtyThreeBI_58620928406526293462861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5320200978462700289515412917) ^ 2660100489231350144757706458 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5320200978462700289515412917) ^ 1773400326154233429838470972 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5320200978462700289515412917) ^ 2110353422634946564662996 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5320200978462700289515412917) ^ 90756 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_8275868188719756005912864537 : Nat.Prime 8275868188719756005912864537 := by
  apply lucas_primality 8275868188719756005912864537 (3 : ZMod 8275868188719756005912864537)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (2521, 1), (58620928406526293462861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (2521, 1), (58620928406526293462861, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719756005912864537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_2521
      · exact prime_sixtyThreeBI_58620928406526293462861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8275868188719756005912864537) ^ 4137934094359878002956432268 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 8275868188719756005912864537) ^ 1182266884102822286558980648 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 8275868188719756005912864537) ^ 3282771990765472433920216 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 8275868188719756005912864537) ^ 141176 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_9310351712309725506651972611 : Nat.Prime 9310351712309725506651972611 := by
  apply lucas_primality 9310351712309725506651972611 (2 : ZMod 9310351712309725506651972611)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (227, 1), (229, 1), (365517915091932547283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (227, 1), (229, 1), (365517915091932547283, 1)] : List FactorBlock).map factorBlockValue).prod) = 9310351712309725506651972611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_227
      · exact prime_sixtyThreeBI_229
      · exact prime_sixtyThreeBI_365517915091932547283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9310351712309725506651972611) ^ 4655175856154862753325986305 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9310351712309725506651972611) ^ 1862070342461945101330394522 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9310351712309725506651972611) ^ 1330050244615675072378853230 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9310351712309725506651972611) ^ 41014765252465751130625430 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9310351712309725506651972611) ^ 40656557695675657234288090 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9310351712309725506651972611) ^ 25471670 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_10640401956925400579030825837 : Nat.Prime 10640401956925400579030825837 := by
  apply lucas_primality 10640401956925400579030825837 (2 : ZMod 10640401956925400579030825837)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (149, 1), (603667, 1), (29574290822026163573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (149, 1), (603667, 1), (29574290822026163573, 1)] : List FactorBlock).map factorBlockValue).prod) = 10640401956925400579030825837 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_149
      · exact prime_sixtyThreeBI_603667
      · exact prime_sixtyThreeBI_29574290822026163573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10640401956925400579030825837) ^ 5320200978462700289515412918 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 10640401956925400579030825837) ^ 71412093670640272342488764 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 10640401956925400579030825837) ^ 17626277329927593489508 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 10640401956925400579030825837) ^ 359785532 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_18620703424619451013303945219 : Nat.Prime 18620703424619451013303945219 := by
  apply lucas_primality 18620703424619451013303945219 (3 : ZMod 18620703424619451013303945219)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (109, 1), (331, 1), (12721, 1), (6761905364525588117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (109, 1), (331, 1), (12721, 1), (6761905364525588117, 1)] : List FactorBlock).map factorBlockValue).prod) = 18620703424619451013303945219 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_109
      · exact prime_sixtyThreeBI_331
      · exact prime_sixtyThreeBI_12721
      · exact prime_sixtyThreeBI_6761905364525588117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 18620703424619451013303945219) ^ 9310351712309725506651972609 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 18620703424619451013303945219) ^ 6206901141539817004434648406 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 18620703424619451013303945219) ^ 170832141510270192782605002 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 18620703424619451013303945219) ^ 56255901584953024209377478 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 18620703424619451013303945219) ^ 1463776701880312162039458 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (3 : ZMod 18620703424619451013303945219) ^ 2753765754 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_74482813698477804053215780807 : Nat.Prime 74482813698477804053215780807 := by
  apply lucas_primality 74482813698477804053215780807 (19 : ZMod 74482813698477804053215780807)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (4137934094359878002956432267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (4137934094359878002956432267, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_3
      · exact prime_sixtyThreeBI_4137934094359878002956432267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (19 : ZMod 74482813698477804053215780807) ^ 37241406849238902026607890403 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (19 : ZMod 74482813698477804053215780807) ^ 24827604566159268017738593602 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (19 : ZMod 74482813698477804053215780807) ^ 18 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_74482813698477804053215780853 : Nat.Prime 74482813698477804053215780853 := by
  apply lucas_primality 74482813698477804053215780853 (2 : ZMod 74482813698477804053215780853)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (149, 1), (603667, 1), (29574290822026163573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (149, 1), (603667, 1), (29574290822026163573, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_7
      · exact prime_sixtyThreeBI_149
      · exact prime_sixtyThreeBI_603667
      · exact prime_sixtyThreeBI_29574290822026163573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 74482813698477804053215780853) ^ 37241406849238902026607890426 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 74482813698477804053215780853) ^ 10640401956925400579030825836 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 74482813698477804053215780853) ^ 499884655694481906397421348 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 74482813698477804053215780853) ^ 123383941309493154426556 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (2 : ZMod 74482813698477804053215780853) ^ 2518498724 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem prime_sixtyThreeBI_74482813698477804053215780871 : Nat.Prime 74482813698477804053215780871 := by
  apply lucas_primality 74482813698477804053215780871 (13 : ZMod 74482813698477804053215780871)
  · rw [← sixtyThreeBIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (479, 1), (3374473, 1), (258446687, 1), (17829683503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (479, 1), (3374473, 1), (258446687, 1), (17829683503, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyThreeBI_2
      · exact prime_sixtyThreeBI_5
      · exact prime_sixtyThreeBI_479
      · exact prime_sixtyThreeBI_3374473
      · exact prime_sixtyThreeBI_258446687
      · exact prime_sixtyThreeBI_17829683503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 74482813698477804053215780871) ^ 37241406849238902026607890435 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (13 : ZMod 74482813698477804053215780871) ^ 14896562739695560810643156174 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (13 : ZMod 74482813698477804053215780871) ^ 155496479537531950006713530 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (13 : ZMod 74482813698477804053215780871) ^ 22072428405406652847190 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (13 : ZMod 74482813698477804053215780871) ^ 288194112925416622010 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide
    · change (13 : ZMod 74482813698477804053215780871) ^ 4177461348988355290 ≠ 1
      rw [← sixtyThreeBIFastPow_eq_pow]
      decide

private theorem phi_sixtyThreeBI_74482813698477804053215780800 : Nat.totient 74482813698477804053215780800 = 19862083652927414414190873600 := by
  rw [← show ((([(2, 6), (3, 1), (5, 2), (15517252853849542511086621, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780800 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_3, prime_sixtyThreeBI_5, prime_sixtyThreeBI_15517252853849542511086621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780801 : Nat.totient 74482813698477804053215780801 = 67664854311741474311082487920 := by
  rw [← show ((([(11, 1), (1447, 1), (4679450505652937365911653, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780801 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_11, prime_sixtyThreeBI_1447, prime_sixtyThreeBI_4679450505652937365911653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780802 : Nat.totient 74482813698477804053215780802 = 36493663096806549054089011200 := by
  rw [← show ((([(2, 1), (53, 1), (1213, 1), (4441, 1), (8167, 1), (17623, 1), (198221, 1), (4572109, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780802 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_53, prime_sixtyThreeBI_1213, prime_sixtyThreeBI_4441, prime_sixtyThreeBI_8167, prime_sixtyThreeBI_17623, prime_sixtyThreeBI_198221, prime_sixtyThreeBI_4572109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780803 : Nat.totient 74482813698477804053215780803 = 39338071419698528456493930240 := by
  rw [← show ((([(3, 1), (7, 1), (19, 1), (41, 1), (4553017525428070423205317, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780803 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_3, prime_sixtyThreeBI_7, prime_sixtyThreeBI_19, prime_sixtyThreeBI_41, prime_sixtyThreeBI_4553017525428070423205317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780804 : Nat.totient 74482813698477804053215780804 = 34376680901208411721449043200 := by
  rw [← show ((([(2, 2), (13, 1), (14664301, 1), (97676786769025262377, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780804 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_13, prime_sixtyThreeBI_14664301, prime_sixtyThreeBI_97676786769025262377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780805 : Nat.totient 74482813698477804053215780805 = 57530398593424955396458917888 := by
  rw [← show ((([(5, 1), (29, 1), (59729, 1), (570967, 1), (638629, 1), (23585396647, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780805 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_5, prime_sixtyThreeBI_29, prime_sixtyThreeBI_59729, prime_sixtyThreeBI_570967, prime_sixtyThreeBI_638629, prime_sixtyThreeBI_23585396647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780806 : Nat.totient 74482813698477804053215780806 = 24827604566159268017738593596 := by
  rw [← show ((([(2, 1), (3, 2), (4137934094359878002956432267, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780806 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_3, prime_sixtyThreeBI_4137934094359878002956432267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780807 : Nat.totient 74482813698477804053215780807 = 74482813698477804053215780806 := by
  rw [← show ((([(74482813698477804053215780807, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780807 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_74482813698477804053215780807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780808 : Nat.totient 74482813698477804053215780808 = 36354950907280774228264476672 := by
  rw [← show ((([(2, 3), (79, 1), (89, 1), (19139, 1), (468558613, 1), (147661005553, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780808 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_79, prime_sixtyThreeBI_89, prime_sixtyThreeBI_19139, prime_sixtyThreeBI_468558613, prime_sixtyThreeBI_147661005553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780809 : Nat.totient 74482813698477804053215780809 = 48730437674739191025143541840 := by
  rw [← show ((([(3, 1), (59, 1), (587, 1), (716877098898717062274091, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780809 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_3, prime_sixtyThreeBI_59, prime_sixtyThreeBI_587, prime_sixtyThreeBI_716877098898717062274091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780810 : Nat.totient 74482813698477804053215780810 = 25536964695794529275710377792 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (30900284707, 1), (34434640514865469, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780810 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_5, prime_sixtyThreeBI_7, prime_sixtyThreeBI_30900284707, prime_sixtyThreeBI_34434640514865469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780811 : Nat.totient 74482813698477804053215780811 = 74482585599323042179969686672 := by
  rw [← show ((([(326537, 1), (228099154761873245767603, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780811 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_326537, prime_sixtyThreeBI_228099154761873245767603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780812 : Nat.totient 74482813698477804053215780812 = 21476992593713606641622937600 := by
  rw [← show ((([(2, 2), (3, 1), (11, 1), (23, 1), (193, 1), (58439, 1), (2175175096714616371, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780812 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_3, prime_sixtyThreeBI_11, prime_sixtyThreeBI_23, prime_sixtyThreeBI_193, prime_sixtyThreeBI_58439, prime_sixtyThreeBI_2175175096714616371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780813 : Nat.totient 74482813698477804053215780813 = 74481978979448559981042868060 := by
  rw [← show ((([(89231, 1), (834719029244072172823523, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780813 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_89231, prime_sixtyThreeBI_834719029244072172823523]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780814 : Nat.totient 74482813698477804053215780814 = 37241403471024492590899428600 := by
  rw [← show ((([(2, 1), (12789611, 1), (79854611, 1), (36464372538967, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780814 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_12789611, prime_sixtyThreeBI_79854611, prime_sixtyThreeBI_36464372538967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780815 : Nat.totient 74482813698477804053215780815 = 37387451581981015367888695296 := by
  rw [← show ((([(3, 5), (5, 1), (17, 1), (3606042783755884969896673, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780815 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_3, prime_sixtyThreeBI_5, prime_sixtyThreeBI_17, prime_sixtyThreeBI_3606042783755884969896673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780816 : Nat.totient 74482813698477804053215780816 = 37085585063239545250115798016 := by
  rw [← show ((([(2, 4), (239, 1), (2582427313633, 1), (7542409091123, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780816 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_239, prime_sixtyThreeBI_2582427313633, prime_sixtyThreeBI_7542409091123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780817 : Nat.totient 74482813698477804053215780817 = 58931404238187585866695289472 := by
  rw [← show ((([(7, 1), (13, 1), (1117099, 1), (732694647676733050313, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780817 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_7, prime_sixtyThreeBI_13, prime_sixtyThreeBI_1117099, prime_sixtyThreeBI_732694647676733050313]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780818 : Nat.totient 74482813698477804053215780818 = 24299357660496304868425006416 := by
  rw [← show ((([(2, 1), (3, 1), (47, 1), (264123452831481574656793549, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780818 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_3, prime_sixtyThreeBI_47, prime_sixtyThreeBI_264123452831481574656793549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780819 : Nat.totient 74482813698477804053215780819 = 73944952200567439142558400000 := by
  rw [← show ((([(211, 1), (401, 1), (220645056829, 1), (3989652261701, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780819 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_211, prime_sixtyThreeBI_401, prime_sixtyThreeBI_220645056829, prime_sixtyThreeBI_3989652261701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780820 : Nat.totient 74482813698477804053215780820 = 28832056516848309870002400000 := by
  rw [← show ((([(2, 2), (5, 1), (31, 1), (72316711, 1), (1661214521791731001, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780820 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_5, prime_sixtyThreeBI_31, prime_sixtyThreeBI_72316711, prime_sixtyThreeBI_1661214521791731001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780821 : Nat.totient 74482813698477804053215780821 = 48313176452651435221594482624 := by
  rw [← show ((([(3, 1), (37, 1), (116349974693, 1), (5767223769463327, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780821 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_3, prime_sixtyThreeBI_37, prime_sixtyThreeBI_116349974693, prime_sixtyThreeBI_5767223769463327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780822 : Nat.totient 74482813698477804053215780822 = 35281332804542117709418001424 := by
  rw [← show ((([(2, 1), (19, 1), (1960074044696784317189888969, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780822 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_19, prime_sixtyThreeBI_1960074044696784317189888969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780823 : Nat.totient 74482813698477804053215780823 = 67711089396405750267841663200 := by
  rw [← show ((([(11, 1), (134669, 1), (1195891, 1), (42044012497890467, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780823 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_11, prime_sixtyThreeBI_134669, prime_sixtyThreeBI_1195891, prime_sixtyThreeBI_42044012497890467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780824 : Nat.totient 74482813698477804053215780824 = 21272362500160261371802636800 := by
  rw [← show ((([(2, 3), (3, 2), (7, 1), (2521, 1), (58620928406526293462861, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780824 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_3, prime_sixtyThreeBI_7, prime_sixtyThreeBI_2521, prime_sixtyThreeBI_58620928406526293462861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780825 : Nat.totient 74482813698477804053215780825 = 59583500104668454301930366400 := by
  rw [← show ((([(5, 2), (21661, 1), (137542705689447032091253, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780825 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_5, prime_sixtyThreeBI_21661, prime_sixtyThreeBI_137542705689447032091253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780826 : Nat.totient 74482813698477804053215780826 = 36789001156098140512513841280 := by
  rw [← show ((([(2, 1), (83, 1), (9907, 1), (156948313, 1), (288568665759821, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780826 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_83, prime_sixtyThreeBI_9907, prime_sixtyThreeBI_156948313, prime_sixtyThreeBI_288568665759821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780827 : Nat.totient 74482813698477804053215780827 = 49383120516687823647045288960 := by
  rw [← show ((([(3, 1), (293, 1), (499, 1), (14327, 1), (11852538994599197281, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780827 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_3, prime_sixtyThreeBI_293, prime_sixtyThreeBI_499, prime_sixtyThreeBI_14327, prime_sixtyThreeBI_11852538994599197281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780828 : Nat.totient 74482813698477804053215780828 = 36607576209277948852896000000 := by
  rw [← show ((([(2, 2), (61, 1), (1801, 1), (12301, 1), (104124821, 1), (132329858747, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780828 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_61, prime_sixtyThreeBI_1801, prime_sixtyThreeBI_12301, prime_sixtyThreeBI_104124821, prime_sixtyThreeBI_132329858747]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780829 : Nat.totient 74482813698477804053215780829 = 74470459607633803753986513600 := by
  rw [← show ((([(6029, 1), (12354090844000299229261201, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780829 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_6029, prime_sixtyThreeBI_12354090844000299229261201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780830 : Nat.totient 74482813698477804053215780830 = 18145218372856765586953113600 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (13, 1), (97, 1), (1968882201915881682612101, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780830 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_3, prime_sixtyThreeBI_5, prime_sixtyThreeBI_13, prime_sixtyThreeBI_97, prime_sixtyThreeBI_1968882201915881682612101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780831 : Nat.totient 74482813698477804053215780831 = 63842389827755617956277354752 := by
  rw [← show ((([(7, 2), (2914673, 1), (6982713469, 1), (74687158187, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780831 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_7, prime_sixtyThreeBI_2914673, prime_sixtyThreeBI_6982713469, prime_sixtyThreeBI_74687158187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780832 : Nat.totient 74482813698477804053215780832 = 35045722163949269250848686080 := by
  rw [← show ((([(2, 5), (17, 1), (6991, 1), (19584742804424439629633, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780832 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_17, prime_sixtyThreeBI_6991, prime_sixtyThreeBI_19584742804424439629633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780833 : Nat.totient 74482813698477804053215780833 = 49655209132318536035477187216 := by
  rw [← show ((([(3, 2), (8275868188719756005912864537, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780833 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_3, prime_sixtyThreeBI_8275868188719756005912864537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780834 : Nat.totient 74482813698477804053215780834 = 32547350621137860303181478400 := by
  rw [← show ((([(2, 1), (11, 2), (29, 1), (311, 1), (907, 1), (37624872285977230769, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780834 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_11, prime_sixtyThreeBI_29, prime_sixtyThreeBI_311, prime_sixtyThreeBI_907, prime_sixtyThreeBI_37624872285977230769]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780835 : Nat.totient 74482813698477804053215780835 = 55669894239008289695275408896 := by
  rw [← show ((([(5, 1), (23, 2), (43, 1), (367163, 1), (2681929, 1), (665052233543, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780835 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_5, prime_sixtyThreeBI_23, prime_sixtyThreeBI_43, prime_sixtyThreeBI_367163, prime_sixtyThreeBI_2681929, prime_sixtyThreeBI_665052233543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780836 : Nat.totient 74482813698477804053215780836 = 24457043303969158296823864224 := by
  rw [← show ((([(2, 2), (3, 1), (67, 1), (3135369137867, 1), (29546860823027, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780836 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_3, prime_sixtyThreeBI_67, prime_sixtyThreeBI_3135369137867, prime_sixtyThreeBI_29546860823027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780837 : Nat.totient 74482813698477804053215780837 = 74482469082830501337739199616 := by
  rw [← show ((([(216133, 1), (344615647302715476365089, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780837 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_216133, prime_sixtyThreeBI_344615647302715476365089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780838 : Nat.totient 74482813698477804053215780838 = 31921205870776201737092477496 := by
  rw [← show ((([(2, 1), (7, 1), (5320200978462700289515412917, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780838 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_7, prime_sixtyThreeBI_5320200978462700289515412917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780839 : Nat.totient 74482813698477804053215780839 = 48835098124515887031813611520 := by
  rw [← show ((([(3, 1), (73, 2), (509, 1), (1291, 1), (8387, 1), (845353649335649, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780839 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_3, prime_sixtyThreeBI_73, prime_sixtyThreeBI_509, prime_sixtyThreeBI_1291, prime_sixtyThreeBI_8387, prime_sixtyThreeBI_845353649335649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780840 : Nat.totient 74482813698477804053215780840 = 29793125479300535865310545472 := by
  rw [← show ((([(2, 3), (5, 1), (328913261267, 1), (5661280835224163, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780840 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_5, prime_sixtyThreeBI_328913261267, prime_sixtyThreeBI_5661280835224163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780841 : Nat.totient 74482813698477804053215780841 = 70000670165573733071379828480 := by
  rw [← show ((([(19, 1), (131, 1), (2999, 1), (3822161009, 1), (2610632463559, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780841 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_19, prime_sixtyThreeBI_131, prime_sixtyThreeBI_2999, prime_sixtyThreeBI_3822161009, prime_sixtyThreeBI_2610632463559]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780842 : Nat.totient 74482813698477804053215780842 = 24827604562411879489685115264 := by
  rw [← show ((([(2, 1), (3, 3), (6625308577, 1), (208188244933217999, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780842 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_3, prime_sixtyThreeBI_6625308577, prime_sixtyThreeBI_208188244933217999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780843 : Nat.totient 74482813698477804053215780843 = 67692339582702913615533552000 := by
  rw [← show ((([(13, 1), (101, 1), (179, 1), (10529899, 1), (30096369610248091, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780843 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_13, prime_sixtyThreeBI_101, prime_sixtyThreeBI_179, prime_sixtyThreeBI_10529899, prime_sixtyThreeBI_30096369610248091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780844 : Nat.totient 74482813698477804053215780844 = 36089839859961779217216000000 := by
  rw [← show ((([(2, 2), (41, 1), (233, 1), (419, 1), (37501, 1), (124050761219139373, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780844 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_41, prime_sixtyThreeBI_233, prime_sixtyThreeBI_419, prime_sixtyThreeBI_37501, prime_sixtyThreeBI_124050761219139373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780845 : Nat.totient 74482813698477804053215780845 = 30703090315280942522589050880 := by
  rw [← show ((([(3, 1), (5, 1), (7, 1), (11, 1), (139, 1), (1093, 1), (424462304839999935337, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780845 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_3, prime_sixtyThreeBI_5, prime_sixtyThreeBI_7, prime_sixtyThreeBI_11, prime_sixtyThreeBI_139, prime_sixtyThreeBI_1093, prime_sixtyThreeBI_424462304839999935337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780846 : Nat.totient 74482813698477804053215780846 = 36674647215561000688694400000 := by
  rw [← show ((([(2, 1), (71, 1), (1201, 1), (4451, 1), (10729, 1), (9145509033221747, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780846 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_71, prime_sixtyThreeBI_1201, prime_sixtyThreeBI_4451, prime_sixtyThreeBI_10729, prime_sixtyThreeBI_9145509033221747]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780847 : Nat.totient 74482813698477804053215780847 = 74432179562720851093288372320 := by
  rw [← show ((([(1471, 1), (50634135756952959927407057, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780847 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_1471, prime_sixtyThreeBI_50634135756952959927407057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780848 : Nat.totient 74482813698477804053215780848 = 24827604566159268017738593600 := by
  rw [← show ((([(2, 4), (3, 1), (1551725285384954251108662101, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780848 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_3, prime_sixtyThreeBI_1551725285384954251108662101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780849 : Nat.totient 74482813698477804053215780849 = 69416256461593859372690150400 := by
  rw [← show ((([(17, 1), (107, 1), (2311, 1), (9407179, 1), (26405261, 1), (71330219, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780849 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_17, prime_sixtyThreeBI_107, prime_sixtyThreeBI_2311, prime_sixtyThreeBI_9407179, prime_sixtyThreeBI_26405261, prime_sixtyThreeBI_71330219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780850 : Nat.totient 74482813698477804053215780850 = 29792931097378350835409720400 := by
  rw [← show ((([(2, 1), (5, 2), (153271, 1), (9719100638539293676327, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780850 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_5, prime_sixtyThreeBI_153271, prime_sixtyThreeBI_9719100638539293676327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780851 : Nat.totient 74482813698477804053215780851 = 48053428192566325195623084240 := by
  rw [← show ((([(3, 2), (31, 1), (266963489958701806642350469, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780851 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_3, prime_sixtyThreeBI_31, prime_sixtyThreeBI_266963489958701806642350469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780852 : Nat.totient 74482813698477804053215780852 = 31706917065823781000526394752 := by
  rw [← show ((([(2, 2), (7, 1), (149, 1), (603667, 1), (29574290822026163573, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780852 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_7, prime_sixtyThreeBI_149, prime_sixtyThreeBI_603667, prime_sixtyThreeBI_29574290822026163573]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780853 : Nat.totient 74482813698477804053215780853 = 74482813698477804053215780852 := by
  rw [← show ((([(74482813698477804053215780853, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780853 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_74482813698477804053215780853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780854 : Nat.totient 74482813698477804053215780854 = 24826958905103793561440757408 := by
  rw [← show ((([(2, 1), (3, 1), (38453, 1), (322830527737228148879653, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780854 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_3, prime_sixtyThreeBI_38453, prime_sixtyThreeBI_322830527737228148879653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780855 : Nat.totient 74482813698477804053215780855 = 58461982072532883428637456000 := by
  rw [← show ((([(5, 1), (53, 1), (249253103251, 1), (1127637802048357, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780855 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_5, prime_sixtyThreeBI_53, prime_sixtyThreeBI_249253103251, prime_sixtyThreeBI_1127637802048357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780856 : Nat.totient 74482813698477804053215780856 = 31251523145280816226275840000 := by
  rw [← show ((([(2, 3), (11, 1), (13, 1), (4613729, 1), (102789431, 1), (137287028951, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780856 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_11, prime_sixtyThreeBI_13, prime_sixtyThreeBI_4613729, prime_sixtyThreeBI_102789431, prime_sixtyThreeBI_137287028951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780857 : Nat.totient 74482813698477804053215780857 = 49436867070706065968526566400 := by
  rw [← show ((([(3, 1), (241, 1), (4019, 1), (25633019677444243595761, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780857 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_3, prime_sixtyThreeBI_241, prime_sixtyThreeBI_4019, prime_sixtyThreeBI_25633019677444243595761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780858 : Nat.totient 74482813698477804053215780858 = 34635069664736799652042176000 := by
  rw [← show ((([(2, 1), (23, 1), (37, 1), (1571, 1), (15161, 1), (953131, 1), (1927701968839, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780858 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_23, prime_sixtyThreeBI_37, prime_sixtyThreeBI_1571, prime_sixtyThreeBI_15161, prime_sixtyThreeBI_953131, prime_sixtyThreeBI_1927701968839]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780859 : Nat.totient 74482813698477804053215780859 = 63842411741552403474184955016 := by
  rw [← show ((([(7, 1), (10640401956925400579030825837, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780859 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_7, prime_sixtyThreeBI_10640401956925400579030825837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780860 : Nat.totient 74482813698477804053215780860 = 18816710829060398722554723840 := by
  rw [← show ((([(2, 2), (3, 2), (5, 1), (19, 1), (668367193181, 1), (32584783811693, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780860 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_3, prime_sixtyThreeBI_5, prime_sixtyThreeBI_19, prime_sixtyThreeBI_668367193181, prime_sixtyThreeBI_32584783811693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780861 : Nat.totient 74482813698477804053215780861 = 74380361410034230732647395292 := by
  rw [← show ((([(727, 1), (102452288443573320568384843, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780861 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_727, prime_sixtyThreeBI_102452288443573320568384843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780862 : Nat.totient 74482813698477804053215780862 = 37241182823258829967426996632 := by
  rw [← show ((([(2, 1), (166237, 1), (224025980072059180727563, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780862 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_166237, prime_sixtyThreeBI_224025980072059180727563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780863 : Nat.totient 74482813698477804053215780863 = 47942960541548931344598663488 := by
  rw [← show ((([(3, 1), (29, 1), (856124295384802345439261849, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780863 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_3, prime_sixtyThreeBI_29, prime_sixtyThreeBI_856124295384802345439261849]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780864 : Nat.totient 74482813698477804053215780864 = 37222298892928363852137824256 := by
  rw [← show ((([(2, 13), (1949, 1), (4665028396127483999533, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780864 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_1949, prime_sixtyThreeBI_4665028396127483999533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780865 : Nat.totient 74482813698477804053215780865 = 57659453791307563958632638720 := by
  rw [← show ((([(5, 1), (47, 1), (163, 1), (197, 1), (8231, 1), (1199172829602141899, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780865 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_5, prime_sixtyThreeBI_47, prime_sixtyThreeBI_163, prime_sixtyThreeBI_197, prime_sixtyThreeBI_8231, prime_sixtyThreeBI_1199172829602141899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780866 : Nat.totient 74482813698477804053215780866 = 20028991918918401089940377856 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (17, 1), (104317666244366672343439469, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780866 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_3, prime_sixtyThreeBI_7, prime_sixtyThreeBI_17, prime_sixtyThreeBI_104317666244366672343439469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780867 : Nat.totient 74482813698477804053215780867 = 67495317434968433935942667520 := by
  rw [← show ((([(11, 1), (313, 1), (286665157, 1), (75464750806651517, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780867 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_11, prime_sixtyThreeBI_313, prime_sixtyThreeBI_286665157, prime_sixtyThreeBI_75464750806651517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780868 : Nat.totient 74482813698477804053215780868 = 36598709209857621947683219440 := by
  rw [← show ((([(2, 2), (59, 2), (3187, 1), (1678456136902353239411, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780868 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_59, prime_sixtyThreeBI_3187, prime_sixtyThreeBI_1678456136902353239411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780869 : Nat.totient 74482813698477804053215780869 = 45794543123752484993258521536 := by
  rw [← show ((([(3, 3), (13, 1), (1117, 1), (189974707635373046069207, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780869 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_3, prime_sixtyThreeBI_13, prime_sixtyThreeBI_1117, prime_sixtyThreeBI_189974707635373046069207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780870 : Nat.totient 74482813698477804053215780870 = 29730917960332393714039588608 := by
  rw [← show ((([(2, 1), (5, 1), (479, 1), (3374473, 1), (258446687, 1), (17829683503, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780870 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_5, prime_sixtyThreeBI_479, prime_sixtyThreeBI_3374473, prime_sixtyThreeBI_258446687, prime_sixtyThreeBI_17829683503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780871 : Nat.totient 74482813698477804053215780871 = 74482813698477804053215780870 := by
  rw [← show ((([(74482813698477804053215780871, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780871 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_74482813698477804053215780871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780872 : Nat.totient 74482813698477804053215780872 = 24523580699826573895823462400 := by
  rw [← show ((([(2, 3), (3, 1), (109, 1), (331, 1), (12721, 1), (6761905364525588117, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780872 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_3, prime_sixtyThreeBI_109, prime_sixtyThreeBI_331, prime_sixtyThreeBI_12721, prime_sixtyThreeBI_6761905364525588117]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780873 : Nat.totient 74482813698477804053215780873 = 63826112938452696452618889936 := by
  rw [← show ((([(7, 1), (3917, 1), (2716467183284503594340267, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780873 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_7, prime_sixtyThreeBI_3917, prime_sixtyThreeBI_2716467183284503594340267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780874 : Nat.totient 74482813698477804053215780874 = 36879506426039339648043041472 := by
  rw [← show ((([(2, 1), (103, 1), (110629, 1), (39302454677, 1), (83157263963, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780874 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_103, prime_sixtyThreeBI_110629, prime_sixtyThreeBI_39302454677, prime_sixtyThreeBI_83157263963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780875 : Nat.totient 74482813698477804053215780875 = 39698422544153043456490072800 := by
  rw [← show ((([(3, 1), (5, 3), (1543, 1), (128723808508926859456843, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780875 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_3, prime_sixtyThreeBI_5, prime_sixtyThreeBI_1543, prime_sixtyThreeBI_128723808508926859456843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780876 : Nat.totient 74482813698477804053215780876 = 37241406849238902026607890436 := by
  rw [← show ((([(2, 2), (18620703424619451013303945219, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780876 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_18620703424619451013303945219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780877 : Nat.totient 74482813698477804053215780877 = 74482813698476864426341952316 := by
  rw [← show ((([(87397626824359, 1), (852229247004203, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780877 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_87397626824359, prime_sixtyThreeBI_852229247004203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780878 : Nat.totient 74482813698477804053215780878 = 22045653017829936429293923200 := by
  rw [← show ((([(2, 1), (3, 2), (11, 1), (43, 1), (258407257, 1), (33854602778938111, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780878 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_3, prime_sixtyThreeBI_11, prime_sixtyThreeBI_43, prime_sixtyThreeBI_258407257, prime_sixtyThreeBI_33854602778938111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780879 : Nat.totient 74482813698477804053215780879 = 70290459429392039065731256320 := by
  rw [← show ((([(19, 1), (421, 1), (673, 1), (13835833063545611116177, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780879 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_19, prime_sixtyThreeBI_421, prime_sixtyThreeBI_673, prime_sixtyThreeBI_13835833063545611116177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780880 : Nat.totient 74482813698477804053215780880 = 25313443181183942798290228224 := by
  rw [← show ((([(2, 4), (5, 1), (7, 2), (227, 1), (229, 1), (365517915091932547283, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780880 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_5, prime_sixtyThreeBI_7, prime_sixtyThreeBI_227, prime_sixtyThreeBI_229, prime_sixtyThreeBI_365517915091932547283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780881 : Nat.totient 74482813698477804053215780881 = 47496286994488121207046097920 := by
  rw [← show ((([(3, 1), (23, 1), (28914409409, 1), (37332979997090461, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780881 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_3, prime_sixtyThreeBI_23, prime_sixtyThreeBI_28914409409, prime_sixtyThreeBI_37332979997090461]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780882 : Nat.totient 74482813698477804053215780882 = 33267757883336593790027990400 := by
  rw [← show ((([(2, 1), (13, 1), (31, 1), (346061867, 1), (267034445698862041, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780882 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_13, prime_sixtyThreeBI_31, prime_sixtyThreeBI_346061867, prime_sixtyThreeBI_267034445698862041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780883 : Nat.totient 74482813698477804053215780883 = 69187529065354579938040934400 := by
  rw [← show ((([(17, 1), (137, 1), (173, 1), (368611796299, 1), (501500364901, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780883 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_17, prime_sixtyThreeBI_137, prime_sixtyThreeBI_173, prime_sixtyThreeBI_368611796299, prime_sixtyThreeBI_501500364901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780884 : Nat.totient 74482813698477804053215780884 = 24775089866985917177774392320 := by
  rw [← show ((([(2, 2), (3, 1), (647, 1), (1753, 1), (101878597, 1), (53716248719941, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780884 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_3, prime_sixtyThreeBI_647, prime_sixtyThreeBI_1753, prime_sixtyThreeBI_101878597, prime_sixtyThreeBI_53716248719941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780885 : Nat.totient 74482813698477804053215780885 = 58011204573143793212871006720 := by
  rw [← show ((([(5, 1), (41, 1), (883, 1), (1039, 1), (16826145547, 1), (23536469623, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780885 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_5, prime_sixtyThreeBI_41, prime_sixtyThreeBI_883, prime_sixtyThreeBI_1039, prime_sixtyThreeBI_16826145547, prime_sixtyThreeBI_23536469623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780886 : Nat.totient 74482813698477804053215780886 = 37192210803202919329082648088 := by
  rw [← show ((([(2, 1), (757, 1), (49196046035982697525241599, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780886 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_757, prime_sixtyThreeBI_49196046035982697525241599]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780887 : Nat.totient 74482813698477804053215780887 = 42019932278631081350488663296 := by
  rw [← show ((([(3, 2), (7, 1), (79, 1), (23549, 1), (36973, 1), (17188234619635903, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780887 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_3, prime_sixtyThreeBI_7, prime_sixtyThreeBI_79, prime_sixtyThreeBI_23549, prime_sixtyThreeBI_36973, prime_sixtyThreeBI_17188234619635903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780888 : Nat.totient 74482813698477804053215780888 = 37241406849238902026607890440 := by
  rw [← show ((([(2, 3), (9310351712309725506651972611, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780888 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_9310351712309725506651972611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780889 : Nat.totient 74482813698477804053215780889 = 66600137363679082840871169600 := by
  rw [← show ((([(11, 1), (61, 1), (44867, 1), (2474038892245021576877, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780889 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_11, prime_sixtyThreeBI_61, prime_sixtyThreeBI_44867, prime_sixtyThreeBI_2474038892245021576877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780890 : Nat.totient 74482813698477804053215780890 = 19858978463646661033900308480 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (6397, 1), (70102399, 1), (5536376143588321, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780890 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_3, prime_sixtyThreeBI_5, prime_sixtyThreeBI_6397, prime_sixtyThreeBI_70102399, prime_sixtyThreeBI_5536376143588321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780891 : Nat.totient 74482813698477804053215780891 = 74284475006780216378300026080 := by
  rw [← show ((([(379, 1), (40949, 1), (4799252103893040261821, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780891 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_379, prime_sixtyThreeBI_40949, prime_sixtyThreeBI_4799252103893040261821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780892 : Nat.totient 74482813698477804053215780892 = 35957220406094228488189822656 := by
  rw [← show ((([(2, 2), (29, 1), (533172207949, 1), (1204288618134463, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780892 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_29, prime_sixtyThreeBI_533172207949, prime_sixtyThreeBI_1204288618134463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780893 : Nat.totient 74482813698477804053215780893 = 49655208920011765616570181024 := by
  rw [← show ((([(3, 1), (233884247, 1), (106153385209219618873, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780893 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_3, prime_sixtyThreeBI_233884247, prime_sixtyThreeBI_106153385209219618873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780894 : Nat.totient 74482813698477804053215780894 = 31638717323247208801365994752 := by
  rw [← show ((([(2, 1), (7, 1), (113, 1), (47081424588165489287747017, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780894 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_7, prime_sixtyThreeBI_113, prime_sixtyThreeBI_47081424588165489287747017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780895 : Nat.totient 74482813698477804053215780895 = 53514647424744076860745236480 := by
  rw [← show ((([(5, 1), (13, 1), (37, 1), (37123, 1), (2343349, 1), (2466661, 1), (144328297, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780895 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_5, prime_sixtyThreeBI_13, prime_sixtyThreeBI_37, prime_sixtyThreeBI_37123, prime_sixtyThreeBI_2343349, prime_sixtyThreeBI_2466661, prime_sixtyThreeBI_144328297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780896 : Nat.totient 74482813698477804053215780896 = 24592067651939407801860957696 := by
  rw [← show ((([(2, 5), (3, 4), (199, 1), (223, 1), (10705646383, 1), (60485356343, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780896 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_3, prime_sixtyThreeBI_199, prime_sixtyThreeBI_223, prime_sixtyThreeBI_10705646383, prime_sixtyThreeBI_60485356343]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780897 : Nat.totient 74482813698477804053215780897 = 73645928151303896142505491136 := by
  rw [← show ((([(89, 1), (836885547173907910710289673, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780897 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_89, prime_sixtyThreeBI_836885547173907910710289673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780898 : Nat.totient 74482813698477804053215780898 = 35281329588260898623969322960 := by
  rw [← show ((([(2, 1), (19, 1), (11986463, 1), (129320047, 1), (1264490511611, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780898 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_19, prime_sixtyThreeBI_11986463, prime_sixtyThreeBI_129320047, prime_sixtyThreeBI_1264490511611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780899 : Nat.totient 74482813698477804053215780899 = 49634266403878081148916458280 := by
  rw [← show ((([(3, 1), (2371, 1), (10471364220227443280362123, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780899 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_3, prime_sixtyThreeBI_2371, prime_sixtyThreeBI_10471364220227443280362123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyThreeBI_74482813698477804053215780900 : Nat.totient 74482813698477804053215780900 = 25491444133200584827358464000 := by
  rw [← show ((([(2, 2), (5, 2), (11, 1), (17, 1), (200339837, 1), (19881408637134911, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477804053215780900 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyThreeBI_2, prime_sixtyThreeBI_5, prime_sixtyThreeBI_11, prime_sixtyThreeBI_17, prime_sixtyThreeBI_200339837, prime_sixtyThreeBI_19881408637134911]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64SixtyThreeBI : certifiedKill 1 74482813698477804053215780799 100 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_sixtyThreeBI_74482813698477804053215780800, phi_sixtyThreeBI_74482813698477804053215780801, phi_sixtyThreeBI_74482813698477804053215780802,
    phi_sixtyThreeBI_74482813698477804053215780803, phi_sixtyThreeBI_74482813698477804053215780804, phi_sixtyThreeBI_74482813698477804053215780805,
    phi_sixtyThreeBI_74482813698477804053215780806, phi_sixtyThreeBI_74482813698477804053215780807, phi_sixtyThreeBI_74482813698477804053215780808,
    phi_sixtyThreeBI_74482813698477804053215780809, phi_sixtyThreeBI_74482813698477804053215780810, phi_sixtyThreeBI_74482813698477804053215780811,
    phi_sixtyThreeBI_74482813698477804053215780812, phi_sixtyThreeBI_74482813698477804053215780813, phi_sixtyThreeBI_74482813698477804053215780814,
    phi_sixtyThreeBI_74482813698477804053215780815, phi_sixtyThreeBI_74482813698477804053215780816, phi_sixtyThreeBI_74482813698477804053215780817,
    phi_sixtyThreeBI_74482813698477804053215780818, phi_sixtyThreeBI_74482813698477804053215780819, phi_sixtyThreeBI_74482813698477804053215780820,
    phi_sixtyThreeBI_74482813698477804053215780821, phi_sixtyThreeBI_74482813698477804053215780822, phi_sixtyThreeBI_74482813698477804053215780823,
    phi_sixtyThreeBI_74482813698477804053215780824, phi_sixtyThreeBI_74482813698477804053215780825, phi_sixtyThreeBI_74482813698477804053215780826,
    phi_sixtyThreeBI_74482813698477804053215780827, phi_sixtyThreeBI_74482813698477804053215780828, phi_sixtyThreeBI_74482813698477804053215780829,
    phi_sixtyThreeBI_74482813698477804053215780830, phi_sixtyThreeBI_74482813698477804053215780831, phi_sixtyThreeBI_74482813698477804053215780832,
    phi_sixtyThreeBI_74482813698477804053215780833, phi_sixtyThreeBI_74482813698477804053215780834, phi_sixtyThreeBI_74482813698477804053215780835,
    phi_sixtyThreeBI_74482813698477804053215780836, phi_sixtyThreeBI_74482813698477804053215780837, phi_sixtyThreeBI_74482813698477804053215780838,
    phi_sixtyThreeBI_74482813698477804053215780839, phi_sixtyThreeBI_74482813698477804053215780840, phi_sixtyThreeBI_74482813698477804053215780841,
    phi_sixtyThreeBI_74482813698477804053215780842, phi_sixtyThreeBI_74482813698477804053215780843, phi_sixtyThreeBI_74482813698477804053215780844,
    phi_sixtyThreeBI_74482813698477804053215780845, phi_sixtyThreeBI_74482813698477804053215780846, phi_sixtyThreeBI_74482813698477804053215780847,
    phi_sixtyThreeBI_74482813698477804053215780848, phi_sixtyThreeBI_74482813698477804053215780849, phi_sixtyThreeBI_74482813698477804053215780850,
    phi_sixtyThreeBI_74482813698477804053215780851, phi_sixtyThreeBI_74482813698477804053215780852, phi_sixtyThreeBI_74482813698477804053215780853,
    phi_sixtyThreeBI_74482813698477804053215780854, phi_sixtyThreeBI_74482813698477804053215780855, phi_sixtyThreeBI_74482813698477804053215780856,
    phi_sixtyThreeBI_74482813698477804053215780857, phi_sixtyThreeBI_74482813698477804053215780858, phi_sixtyThreeBI_74482813698477804053215780859,
    phi_sixtyThreeBI_74482813698477804053215780860, phi_sixtyThreeBI_74482813698477804053215780861, phi_sixtyThreeBI_74482813698477804053215780862,
    phi_sixtyThreeBI_74482813698477804053215780863, phi_sixtyThreeBI_74482813698477804053215780864, phi_sixtyThreeBI_74482813698477804053215780865,
    phi_sixtyThreeBI_74482813698477804053215780866, phi_sixtyThreeBI_74482813698477804053215780867, phi_sixtyThreeBI_74482813698477804053215780868,
    phi_sixtyThreeBI_74482813698477804053215780869, phi_sixtyThreeBI_74482813698477804053215780870, phi_sixtyThreeBI_74482813698477804053215780871,
    phi_sixtyThreeBI_74482813698477804053215780872, phi_sixtyThreeBI_74482813698477804053215780873, phi_sixtyThreeBI_74482813698477804053215780874,
    phi_sixtyThreeBI_74482813698477804053215780875, phi_sixtyThreeBI_74482813698477804053215780876, phi_sixtyThreeBI_74482813698477804053215780877,
    phi_sixtyThreeBI_74482813698477804053215780878, phi_sixtyThreeBI_74482813698477804053215780879, phi_sixtyThreeBI_74482813698477804053215780880,
    phi_sixtyThreeBI_74482813698477804053215780881, phi_sixtyThreeBI_74482813698477804053215780882, phi_sixtyThreeBI_74482813698477804053215780883,
    phi_sixtyThreeBI_74482813698477804053215780884, phi_sixtyThreeBI_74482813698477804053215780885, phi_sixtyThreeBI_74482813698477804053215780886,
    phi_sixtyThreeBI_74482813698477804053215780887, phi_sixtyThreeBI_74482813698477804053215780888, phi_sixtyThreeBI_74482813698477804053215780889,
    phi_sixtyThreeBI_74482813698477804053215780890, phi_sixtyThreeBI_74482813698477804053215780891, phi_sixtyThreeBI_74482813698477804053215780892,
    phi_sixtyThreeBI_74482813698477804053215780893, phi_sixtyThreeBI_74482813698477804053215780894, phi_sixtyThreeBI_74482813698477804053215780895,
    phi_sixtyThreeBI_74482813698477804053215780896, phi_sixtyThreeBI_74482813698477804053215780897, phi_sixtyThreeBI_74482813698477804053215780898,
    phi_sixtyThreeBI_74482813698477804053215780899, phi_sixtyThreeBI_74482813698477804053215780900
  ]

end TotientTailPeriodKiller
end Erdos249257
