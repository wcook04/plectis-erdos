import Erdos249257.DiagonalPincerCertificatesT64

-- Explicit full-window certificate for the earliest successful 78P sweep coordinate.
namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def seventyEightBXFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem seventyEightBXFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    seventyEightBXFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [seventyEightBXFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [seventyEightBXFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then seventyEightBXFastPow a n * seventyEightBXFastPow a n * a
        else seventyEightBXFastPow a n * seventyEightBXFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_seventyEightBX_2 : Nat.Prime 2 := by norm_num

private theorem prime_seventyEightBX_3 : Nat.Prime 3 := by norm_num

private theorem prime_seventyEightBX_5 : Nat.Prime 5 := by norm_num

private theorem prime_seventyEightBX_7 : Nat.Prime 7 := by norm_num

private theorem prime_seventyEightBX_11 : Nat.Prime 11 := by norm_num

private theorem prime_seventyEightBX_13 : Nat.Prime 13 := by norm_num

private theorem prime_seventyEightBX_17 : Nat.Prime 17 := by norm_num

private theorem prime_seventyEightBX_19 : Nat.Prime 19 := by norm_num

private theorem prime_seventyEightBX_23 : Nat.Prime 23 := by norm_num

private theorem prime_seventyEightBX_29 : Nat.Prime 29 := by norm_num

private theorem prime_seventyEightBX_31 : Nat.Prime 31 := by norm_num

private theorem prime_seventyEightBX_37 : Nat.Prime 37 := by norm_num

private theorem prime_seventyEightBX_41 : Nat.Prime 41 := by norm_num

private theorem prime_seventyEightBX_43 : Nat.Prime 43 := by norm_num

private theorem prime_seventyEightBX_47 : Nat.Prime 47 := by norm_num

private theorem prime_seventyEightBX_53 : Nat.Prime 53 := by norm_num

private theorem prime_seventyEightBX_59 : Nat.Prime 59 := by norm_num

private theorem prime_seventyEightBX_61 : Nat.Prime 61 := by norm_num

private theorem prime_seventyEightBX_67 : Nat.Prime 67 := by norm_num

private theorem prime_seventyEightBX_71 : Nat.Prime 71 := by norm_num

private theorem prime_seventyEightBX_73 : Nat.Prime 73 := by norm_num

private theorem prime_seventyEightBX_79 : Nat.Prime 79 := by norm_num

private theorem prime_seventyEightBX_83 : Nat.Prime 83 := by norm_num

private theorem prime_seventyEightBX_89 : Nat.Prime 89 := by norm_num

private theorem prime_seventyEightBX_97 : Nat.Prime 97 := by norm_num

private theorem prime_seventyEightBX_101 : Nat.Prime 101 := by norm_num

private theorem prime_seventyEightBX_103 : Nat.Prime 103 := by norm_num

private theorem prime_seventyEightBX_107 : Nat.Prime 107 := by norm_num

private theorem prime_seventyEightBX_109 : Nat.Prime 109 := by norm_num

private theorem prime_seventyEightBX_113 : Nat.Prime 113 := by norm_num

private theorem prime_seventyEightBX_127 : Nat.Prime 127 := by norm_num

private theorem prime_seventyEightBX_131 : Nat.Prime 131 := by norm_num

private theorem prime_seventyEightBX_137 : Nat.Prime 137 := by norm_num

private theorem prime_seventyEightBX_149 : Nat.Prime 149 := by norm_num

private theorem prime_seventyEightBX_151 : Nat.Prime 151 := by norm_num

private theorem prime_seventyEightBX_157 : Nat.Prime 157 := by norm_num

private theorem prime_seventyEightBX_163 : Nat.Prime 163 := by norm_num

private theorem prime_seventyEightBX_167 : Nat.Prime 167 := by norm_num

private theorem prime_seventyEightBX_173 : Nat.Prime 173 := by norm_num

private theorem prime_seventyEightBX_179 : Nat.Prime 179 := by norm_num

private theorem prime_seventyEightBX_181 : Nat.Prime 181 := by norm_num

private theorem prime_seventyEightBX_193 : Nat.Prime 193 := by norm_num

private theorem prime_seventyEightBX_197 : Nat.Prime 197 := by norm_num

private theorem prime_seventyEightBX_199 : Nat.Prime 199 := by norm_num

private theorem prime_seventyEightBX_211 : Nat.Prime 211 := by norm_num

private theorem prime_seventyEightBX_223 : Nat.Prime 223 := by norm_num

private theorem prime_seventyEightBX_227 : Nat.Prime 227 := by norm_num

private theorem prime_seventyEightBX_233 : Nat.Prime 233 := by norm_num

private theorem prime_seventyEightBX_239 : Nat.Prime 239 := by norm_num

private theorem prime_seventyEightBX_241 : Nat.Prime 241 := by norm_num

private theorem prime_seventyEightBX_251 : Nat.Prime 251 := by norm_num

private theorem prime_seventyEightBX_257 : Nat.Prime 257 := by norm_num

private theorem prime_seventyEightBX_263 : Nat.Prime 263 := by norm_num

private theorem prime_seventyEightBX_271 : Nat.Prime 271 := by norm_num

private theorem prime_seventyEightBX_281 : Nat.Prime 281 := by norm_num

private theorem prime_seventyEightBX_283 : Nat.Prime 283 := by norm_num

private theorem prime_seventyEightBX_293 : Nat.Prime 293 := by norm_num

private theorem prime_seventyEightBX_311 : Nat.Prime 311 := by norm_num

private theorem prime_seventyEightBX_331 : Nat.Prime 331 := by norm_num

private theorem prime_seventyEightBX_337 : Nat.Prime 337 := by norm_num

private theorem prime_seventyEightBX_347 : Nat.Prime 347 := by norm_num

private theorem prime_seventyEightBX_349 : Nat.Prime 349 := by norm_num

private theorem prime_seventyEightBX_353 : Nat.Prime 353 := by norm_num

private theorem prime_seventyEightBX_373 : Nat.Prime 373 := by norm_num

private theorem prime_seventyEightBX_383 : Nat.Prime 383 := by norm_num

private theorem prime_seventyEightBX_389 : Nat.Prime 389 := by norm_num

private theorem prime_seventyEightBX_401 : Nat.Prime 401 := by norm_num

private theorem prime_seventyEightBX_409 : Nat.Prime 409 := by norm_num

private theorem prime_seventyEightBX_421 : Nat.Prime 421 := by norm_num

private theorem prime_seventyEightBX_443 : Nat.Prime 443 := by norm_num

private theorem prime_seventyEightBX_461 : Nat.Prime 461 := by norm_num

private theorem prime_seventyEightBX_463 : Nat.Prime 463 := by norm_num

private theorem prime_seventyEightBX_487 : Nat.Prime 487 := by norm_num

private theorem prime_seventyEightBX_503 : Nat.Prime 503 := by norm_num

private theorem prime_seventyEightBX_521 : Nat.Prime 521 := by norm_num

private theorem prime_seventyEightBX_547 : Nat.Prime 547 := by norm_num

private theorem prime_seventyEightBX_557 : Nat.Prime 557 := by norm_num

private theorem prime_seventyEightBX_569 : Nat.Prime 569 := by norm_num

private theorem prime_seventyEightBX_577 : Nat.Prime 577 := by norm_num

private theorem prime_seventyEightBX_587 : Nat.Prime 587 := by norm_num

private theorem prime_seventyEightBX_599 : Nat.Prime 599 := by norm_num

private theorem prime_seventyEightBX_607 : Nat.Prime 607 := by norm_num

private theorem prime_seventyEightBX_617 : Nat.Prime 617 := by norm_num

private theorem prime_seventyEightBX_643 : Nat.Prime 643 := by norm_num

private theorem prime_seventyEightBX_647 : Nat.Prime 647 := by norm_num

private theorem prime_seventyEightBX_673 : Nat.Prime 673 := by norm_num

private theorem prime_seventyEightBX_677 : Nat.Prime 677 := by norm_num

private theorem prime_seventyEightBX_691 : Nat.Prime 691 := by norm_num

private theorem prime_seventyEightBX_739 : Nat.Prime 739 := by norm_num

private theorem prime_seventyEightBX_757 : Nat.Prime 757 := by norm_num

private theorem prime_seventyEightBX_761 : Nat.Prime 761 := by norm_num

private theorem prime_seventyEightBX_821 : Nat.Prime 821 := by norm_num

private theorem prime_seventyEightBX_839 : Nat.Prime 839 := by norm_num

private theorem prime_seventyEightBX_859 : Nat.Prime 859 := by norm_num

private theorem prime_seventyEightBX_877 : Nat.Prime 877 := by norm_num

private theorem prime_seventyEightBX_881 : Nat.Prime 881 := by norm_num

private theorem prime_seventyEightBX_887 : Nat.Prime 887 := by norm_num

private theorem prime_seventyEightBX_953 : Nat.Prime 953 := by norm_num

private theorem prime_seventyEightBX_997 : Nat.Prime 997 := by norm_num

private theorem prime_seventyEightBX_1021 : Nat.Prime 1021 := by norm_num

private theorem prime_seventyEightBX_1063 : Nat.Prime 1063 := by norm_num

private theorem prime_seventyEightBX_1087 : Nat.Prime 1087 := by norm_num

private theorem prime_seventyEightBX_1097 : Nat.Prime 1097 := by norm_num

private theorem prime_seventyEightBX_1103 : Nat.Prime 1103 := by norm_num

private theorem prime_seventyEightBX_1109 : Nat.Prime 1109 := by norm_num

private theorem prime_seventyEightBX_1123 : Nat.Prime 1123 := by norm_num

private theorem prime_seventyEightBX_1129 : Nat.Prime 1129 := by norm_num

private theorem prime_seventyEightBX_1153 : Nat.Prime 1153 := by norm_num

private theorem prime_seventyEightBX_1187 : Nat.Prime 1187 := by norm_num

private theorem prime_seventyEightBX_1193 : Nat.Prime 1193 := by norm_num

private theorem prime_seventyEightBX_1201 : Nat.Prime 1201 := by norm_num

private theorem prime_seventyEightBX_1229 : Nat.Prime 1229 := by norm_num

private theorem prime_seventyEightBX_1301 : Nat.Prime 1301 := by norm_num

private theorem prime_seventyEightBX_1327 : Nat.Prime 1327 := by norm_num

private theorem prime_seventyEightBX_1409 : Nat.Prime 1409 := by norm_num

private theorem prime_seventyEightBX_1459 : Nat.Prime 1459 := by norm_num

private theorem prime_seventyEightBX_1523 : Nat.Prime 1523 := by norm_num

private theorem prime_seventyEightBX_1559 : Nat.Prime 1559 := by norm_num

private theorem prime_seventyEightBX_1579 : Nat.Prime 1579 := by norm_num

private theorem prime_seventyEightBX_1669 : Nat.Prime 1669 := by norm_num

private theorem prime_seventyEightBX_1693 : Nat.Prime 1693 := by norm_num

private theorem prime_seventyEightBX_1697 : Nat.Prime 1697 := by norm_num

private theorem prime_seventyEightBX_1721 : Nat.Prime 1721 := by norm_num

private theorem prime_seventyEightBX_1741 : Nat.Prime 1741 := by norm_num

private theorem prime_seventyEightBX_1747 : Nat.Prime 1747 := by norm_num

private theorem prime_seventyEightBX_1823 : Nat.Prime 1823 := by norm_num

private theorem prime_seventyEightBX_1861 : Nat.Prime 1861 := by norm_num

private theorem prime_seventyEightBX_1867 : Nat.Prime 1867 := by norm_num

private theorem prime_seventyEightBX_1889 : Nat.Prime 1889 := by norm_num

private theorem prime_seventyEightBX_2029 : Nat.Prime 2029 := by norm_num

private theorem prime_seventyEightBX_2081 : Nat.Prime 2081 := by norm_num

private theorem prime_seventyEightBX_2083 : Nat.Prime 2083 := by norm_num

private theorem prime_seventyEightBX_2129 : Nat.Prime 2129 := by norm_num

private theorem prime_seventyEightBX_2141 : Nat.Prime 2141 := by norm_num

private theorem prime_seventyEightBX_2153 : Nat.Prime 2153 := by norm_num

private theorem prime_seventyEightBX_2203 : Nat.Prime 2203 := by norm_num

private theorem prime_seventyEightBX_2207 : Nat.Prime 2207 := by norm_num

private theorem prime_seventyEightBX_2239 : Nat.Prime 2239 := by norm_num

private theorem prime_seventyEightBX_2281 : Nat.Prime 2281 := by norm_num

private theorem prime_seventyEightBX_2377 : Nat.Prime 2377 := by norm_num

private theorem prime_seventyEightBX_2381 : Nat.Prime 2381 := by norm_num

private theorem prime_seventyEightBX_2389 : Nat.Prime 2389 := by norm_num

private theorem prime_seventyEightBX_2393 : Nat.Prime 2393 := by norm_num

private theorem prime_seventyEightBX_2447 : Nat.Prime 2447 := by norm_num

private theorem prime_seventyEightBX_2539 : Nat.Prime 2539 := by norm_num

private theorem prime_seventyEightBX_2683 : Nat.Prime 2683 := by norm_num

private theorem prime_seventyEightBX_2741 : Nat.Prime 2741 := by norm_num

private theorem prime_seventyEightBX_2789 : Nat.Prime 2789 := by norm_num

private theorem prime_seventyEightBX_2797 : Nat.Prime 2797 := by norm_num

private theorem prime_seventyEightBX_2801 : Nat.Prime 2801 := by norm_num

private theorem prime_seventyEightBX_2819 : Nat.Prime 2819 := by norm_num

private theorem prime_seventyEightBX_2833 : Nat.Prime 2833 := by norm_num

private theorem prime_seventyEightBX_2837 : Nat.Prime 2837 := by norm_num

private theorem prime_seventyEightBX_3181 : Nat.Prime 3181 := by norm_num

private theorem prime_seventyEightBX_3203 : Nat.Prime 3203 := by norm_num

private theorem prime_seventyEightBX_3343 : Nat.Prime 3343 := by norm_num

private theorem prime_seventyEightBX_3433 : Nat.Prime 3433 := by norm_num

private theorem prime_seventyEightBX_3529 : Nat.Prime 3529 := by norm_num

private theorem prime_seventyEightBX_3547 : Nat.Prime 3547 := by norm_num

private theorem prime_seventyEightBX_3559 : Nat.Prime 3559 := by norm_num

private theorem prime_seventyEightBX_3593 : Nat.Prime 3593 := by norm_num

private theorem prime_seventyEightBX_3697 : Nat.Prime 3697 := by norm_num

private theorem prime_seventyEightBX_3739 : Nat.Prime 3739 := by norm_num

private theorem prime_seventyEightBX_3877 : Nat.Prime 3877 := by norm_num

private theorem prime_seventyEightBX_3919 : Nat.Prime 3919 := by norm_num

private theorem prime_seventyEightBX_3931 : Nat.Prime 3931 := by norm_num

private theorem prime_seventyEightBX_3989 : Nat.Prime 3989 := by norm_num

private theorem prime_seventyEightBX_4049 : Nat.Prime 4049 := by norm_num

private theorem prime_seventyEightBX_4079 : Nat.Prime 4079 := by norm_num

private theorem prime_seventyEightBX_4093 : Nat.Prime 4093 := by norm_num

private theorem prime_seventyEightBX_4373 : Nat.Prime 4373 := by norm_num

private theorem prime_seventyEightBX_4423 : Nat.Prime 4423 := by norm_num

private theorem prime_seventyEightBX_4523 : Nat.Prime 4523 := by norm_num

private theorem prime_seventyEightBX_4909 : Nat.Prime 4909 := by norm_num

private theorem prime_seventyEightBX_4931 : Nat.Prime 4931 := by norm_num

private theorem prime_seventyEightBX_5231 : Nat.Prime 5231 := by norm_num

private theorem prime_seventyEightBX_5693 : Nat.Prime 5693 := by norm_num

private theorem prime_seventyEightBX_5867 : Nat.Prime 5867 := by norm_num

private theorem prime_seventyEightBX_5881 : Nat.Prime 5881 := by norm_num

private theorem prime_seventyEightBX_6007 : Nat.Prime 6007 := by norm_num

private theorem prime_seventyEightBX_6257 : Nat.Prime 6257 := by norm_num

private theorem prime_seventyEightBX_6397 : Nat.Prime 6397 := by norm_num

private theorem prime_seventyEightBX_6899 : Nat.Prime 6899 := by norm_num

private theorem prime_seventyEightBX_6961 : Nat.Prime 6961 := by norm_num

private theorem prime_seventyEightBX_6983 : Nat.Prime 6983 := by norm_num

private theorem prime_seventyEightBX_7013 : Nat.Prime 7013 := by norm_num

private theorem prime_seventyEightBX_7177 : Nat.Prime 7177 := by norm_num

private theorem prime_seventyEightBX_7211 : Nat.Prime 7211 := by norm_num

private theorem prime_seventyEightBX_7229 : Nat.Prime 7229 := by norm_num

private theorem prime_seventyEightBX_7283 : Nat.Prime 7283 := by norm_num

private theorem prime_seventyEightBX_7307 : Nat.Prime 7307 := by norm_num

private theorem prime_seventyEightBX_7417 : Nat.Prime 7417 := by norm_num

private theorem prime_seventyEightBX_7451 : Nat.Prime 7451 := by norm_num

private theorem prime_seventyEightBX_7481 : Nat.Prime 7481 := by norm_num

private theorem prime_seventyEightBX_7549 : Nat.Prime 7549 := by norm_num

private theorem prime_seventyEightBX_7703 : Nat.Prime 7703 := by norm_num

private theorem prime_seventyEightBX_7873 : Nat.Prime 7873 := by norm_num

private theorem prime_seventyEightBX_7937 : Nat.Prime 7937 := by norm_num

private theorem prime_seventyEightBX_8053 : Nat.Prime 8053 := by norm_num

private theorem prime_seventyEightBX_8123 : Nat.Prime 8123 := by norm_num

private theorem prime_seventyEightBX_8353 : Nat.Prime 8353 := by norm_num

private theorem prime_seventyEightBX_8419 : Nat.Prime 8419 := by norm_num

private theorem prime_seventyEightBX_8699 : Nat.Prime 8699 := by norm_num

private theorem prime_seventyEightBX_8819 : Nat.Prime 8819 := by norm_num

private theorem prime_seventyEightBX_8963 : Nat.Prime 8963 := by norm_num

private theorem prime_seventyEightBX_9041 : Nat.Prime 9041 := by norm_num

private theorem prime_seventyEightBX_9133 : Nat.Prime 9133 := by norm_num

private theorem prime_seventyEightBX_9199 : Nat.Prime 9199 := by norm_num

private theorem prime_seventyEightBX_9479 : Nat.Prime 9479 := by norm_num

private theorem prime_seventyEightBX_9677 : Nat.Prime 9677 := by norm_num

private theorem prime_seventyEightBX_10211 : Nat.Prime 10211 := by norm_num

private theorem prime_seventyEightBX_10781 : Nat.Prime 10781 := by norm_num

private theorem prime_seventyEightBX_11287 : Nat.Prime 11287 := by norm_num

private theorem prime_seventyEightBX_11369 : Nat.Prime 11369 := by norm_num

private theorem prime_seventyEightBX_11471 : Nat.Prime 11471 := by norm_num

private theorem prime_seventyEightBX_11621 : Nat.Prime 11621 := by norm_num

private theorem prime_seventyEightBX_12569 : Nat.Prime 12569 := by norm_num

private theorem prime_seventyEightBX_13763 : Nat.Prime 13763 := by norm_num

private theorem prime_seventyEightBX_14071 : Nat.Prime 14071 := by norm_num

private theorem prime_seventyEightBX_14503 : Nat.Prime 14503 := by norm_num

private theorem prime_seventyEightBX_14731 : Nat.Prime 14731 := by norm_num

private theorem prime_seventyEightBX_15083 : Nat.Prime 15083 := by norm_num

private theorem prime_seventyEightBX_15451 : Nat.Prime 15451 := by norm_num

private theorem prime_seventyEightBX_15641 : Nat.Prime 15641 := by norm_num

private theorem prime_seventyEightBX_16193 : Nat.Prime 16193 := by norm_num

private theorem prime_seventyEightBX_16417 : Nat.Prime 16417 := by norm_num

private theorem prime_seventyEightBX_16693 : Nat.Prime 16693 := by norm_num

private theorem prime_seventyEightBX_16901 : Nat.Prime 16901 := by norm_num

private theorem prime_seventyEightBX_17117 : Nat.Prime 17117 := by norm_num

private theorem prime_seventyEightBX_17623 : Nat.Prime 17623 := by norm_num

private theorem prime_seventyEightBX_17837 : Nat.Prime 17837 := by norm_num

private theorem prime_seventyEightBX_17959 : Nat.Prime 17959 := by norm_num

private theorem prime_seventyEightBX_18233 : Nat.Prime 18233 := by norm_num

private theorem prime_seventyEightBX_19403 : Nat.Prime 19403 := by norm_num

private theorem prime_seventyEightBX_19427 : Nat.Prime 19427 := by norm_num

private theorem prime_seventyEightBX_19477 : Nat.Prime 19477 := by norm_num

private theorem prime_seventyEightBX_19501 : Nat.Prime 19501 := by norm_num

private theorem prime_seventyEightBX_20333 : Nat.Prime 20333 := by norm_num

private theorem prime_seventyEightBX_20611 : Nat.Prime 20611 := by norm_num

private theorem prime_seventyEightBX_20947 : Nat.Prime 20947 := by norm_num

private theorem prime_seventyEightBX_21841 : Nat.Prime 21841 := by norm_num

private theorem prime_seventyEightBX_23747 : Nat.Prime 23747 := by norm_num

private theorem prime_seventyEightBX_23957 : Nat.Prime 23957 := by norm_num

private theorem prime_seventyEightBX_24677 : Nat.Prime 24677 := by norm_num

private theorem prime_seventyEightBX_25849 : Nat.Prime 25849 := by norm_num

private theorem prime_seventyEightBX_26177 : Nat.Prime 26177 := by norm_num

private theorem prime_seventyEightBX_27427 : Nat.Prime 27427 := by norm_num

private theorem prime_seventyEightBX_30089 : Nat.Prime 30089 := by norm_num

private theorem prime_seventyEightBX_33287 : Nat.Prime 33287 := by norm_num

private theorem prime_seventyEightBX_33613 : Nat.Prime 33613 := by norm_num

private theorem prime_seventyEightBX_33911 : Nat.Prime 33911 := by norm_num

private theorem prime_seventyEightBX_35543 : Nat.Prime 35543 := by norm_num

private theorem prime_seventyEightBX_40387 : Nat.Prime 40387 := by norm_num

private theorem prime_seventyEightBX_42139 : Nat.Prime 42139 := by norm_num

private theorem prime_seventyEightBX_42181 : Nat.Prime 42181 := by norm_num

private theorem prime_seventyEightBX_42943 : Nat.Prime 42943 := by norm_num

private theorem prime_seventyEightBX_44809 : Nat.Prime 44809 := by norm_num

private theorem prime_seventyEightBX_46957 : Nat.Prime 46957 := by norm_num

private theorem prime_seventyEightBX_47969 : Nat.Prime 47969 := by norm_num

private theorem prime_seventyEightBX_48673 : Nat.Prime 48673 := by norm_num

private theorem prime_seventyEightBX_49367 : Nat.Prime 49367 := by norm_num

private theorem prime_seventyEightBX_50461 : Nat.Prime 50461 := by norm_num

private theorem prime_seventyEightBX_51487 : Nat.Prime 51487 := by norm_num

private theorem prime_seventyEightBX_54437 : Nat.Prime 54437 := by norm_num

private theorem prime_seventyEightBX_54767 : Nat.Prime 54767 := by norm_num

private theorem prime_seventyEightBX_56149 : Nat.Prime 56149 := by norm_num

private theorem prime_seventyEightBX_57529 : Nat.Prime 57529 := by norm_num

private theorem prime_seventyEightBX_59333 : Nat.Prime 59333 := by norm_num

private theorem prime_seventyEightBX_59809 : Nat.Prime 59809 := by norm_num

private theorem prime_seventyEightBX_60661 : Nat.Prime 60661 := by norm_num

private theorem prime_seventyEightBX_61339 : Nat.Prime 61339 := by norm_num

private theorem prime_seventyEightBX_62219 : Nat.Prime 62219 := by norm_num

private theorem prime_seventyEightBX_63337 : Nat.Prime 63337 := by norm_num

private theorem prime_seventyEightBX_67433 : Nat.Prime 67433 := by norm_num

private theorem prime_seventyEightBX_68477 : Nat.Prime 68477 := by norm_num

private theorem prime_seventyEightBX_70009 : Nat.Prime 70009 := by norm_num

private theorem prime_seventyEightBX_71233 : Nat.Prime 71233 := by norm_num

private theorem prime_seventyEightBX_72109 : Nat.Prime 72109 := by norm_num

private theorem prime_seventyEightBX_75997 : Nat.Prime 75997 := by norm_num

private theorem prime_seventyEightBX_76369 : Nat.Prime 76369 := by norm_num

private theorem prime_seventyEightBX_76379 : Nat.Prime 76379 := by norm_num

private theorem prime_seventyEightBX_77137 : Nat.Prime 77137 := by norm_num

private theorem prime_seventyEightBX_79811 : Nat.Prime 79811 := by norm_num

private theorem prime_seventyEightBX_84809 : Nat.Prime 84809 := by norm_num

private theorem prime_seventyEightBX_84913 : Nat.Prime 84913 := by norm_num

private theorem prime_seventyEightBX_86083 : Nat.Prime 86083 := by norm_num

private theorem prime_seventyEightBX_87833 : Nat.Prime 87833 := by norm_num

private theorem prime_seventyEightBX_94687 : Nat.Prime 94687 := by norm_num

private theorem prime_seventyEightBX_95617 : Nat.Prime 95617 := by norm_num

private theorem prime_seventyEightBX_102101 : Nat.Prime 102101 := by norm_num

private theorem prime_seventyEightBX_103681 : Nat.Prime 103681 := by norm_num

private theorem prime_seventyEightBX_104383 : Nat.Prime 104383 := by norm_num

private theorem prime_seventyEightBX_105229 : Nat.Prime 105229 := by norm_num

private theorem prime_seventyEightBX_107101 : Nat.Prime 107101 := by norm_num

private theorem prime_seventyEightBX_110039 : Nat.Prime 110039 := by norm_num

private theorem prime_seventyEightBX_110251 : Nat.Prime 110251 := by norm_num

private theorem prime_seventyEightBX_123379 : Nat.Prime 123379 := by norm_num

private theorem prime_seventyEightBX_134437 : Nat.Prime 134437 := by norm_num

private theorem prime_seventyEightBX_143687 : Nat.Prime 143687 := by norm_num

private theorem prime_seventyEightBX_151237 : Nat.Prime 151237 := by norm_num

private theorem prime_seventyEightBX_152287 : Nat.Prime 152287 := by norm_num

private theorem prime_seventyEightBX_153379 : Nat.Prime 153379 := by norm_num

private theorem prime_seventyEightBX_179969 : Nat.Prime 179969 := by norm_num

private theorem prime_seventyEightBX_195973 : Nat.Prime 195973 := by norm_num

private theorem prime_seventyEightBX_197891 : Nat.Prime 197891 := by norm_num

private theorem prime_seventyEightBX_211801 : Nat.Prime 211801 := by norm_num

private theorem prime_seventyEightBX_255839 : Nat.Prime 255839 := by norm_num

private theorem prime_seventyEightBX_256757 : Nat.Prime 256757 := by norm_num

private theorem prime_seventyEightBX_260399 : Nat.Prime 260399 := by norm_num

private theorem prime_seventyEightBX_265543 : Nat.Prime 265543 := by norm_num

private theorem prime_seventyEightBX_266351 : Nat.Prime 266351 := by norm_num

private theorem prime_seventyEightBX_268123 : Nat.Prime 268123 := by norm_num

private theorem prime_seventyEightBX_268501 : Nat.Prime 268501 := by norm_num

private theorem prime_seventyEightBX_272329 : Nat.Prime 272329 := by norm_num

private theorem prime_seventyEightBX_273067 : Nat.Prime 273067 := by norm_num

private theorem prime_seventyEightBX_288947 : Nat.Prime 288947 := by norm_num

private theorem prime_seventyEightBX_293351 : Nat.Prime 293351 := by norm_num

private theorem prime_seventyEightBX_297023 : Nat.Prime 297023 := by norm_num

private theorem prime_seventyEightBX_306589 : Nat.Prime 306589 := by norm_num

private theorem prime_seventyEightBX_317651 : Nat.Prime 317651 := by norm_num

private theorem prime_seventyEightBX_326611 : Nat.Prime 326611 := by norm_num

private theorem prime_seventyEightBX_329009 : Nat.Prime 329009 := by norm_num

private theorem prime_seventyEightBX_332749 : Nat.Prime 332749 := by norm_num

private theorem prime_seventyEightBX_345881 : Nat.Prime 345881 := by norm_num

private theorem prime_seventyEightBX_346469 : Nat.Prime 346469 := by norm_num

private theorem prime_seventyEightBX_350381 : Nat.Prime 350381 := by norm_num

private theorem prime_seventyEightBX_359143 : Nat.Prime 359143 := by norm_num

private theorem prime_seventyEightBX_376393 : Nat.Prime 376393 := by norm_num

private theorem prime_seventyEightBX_376631 : Nat.Prime 376631 := by norm_num

private theorem prime_seventyEightBX_379163 : Nat.Prime 379163 := by norm_num

private theorem prime_seventyEightBX_387707 : Nat.Prime 387707 := by norm_num

private theorem prime_seventyEightBX_388541 : Nat.Prime 388541 := by norm_num

private theorem prime_seventyEightBX_396259 : Nat.Prime 396259 := by norm_num

private theorem prime_seventyEightBX_413087 : Nat.Prime 413087 := by norm_num

private theorem prime_seventyEightBX_421459 : Nat.Prime 421459 := by norm_num

private theorem prime_seventyEightBX_430453 : Nat.Prime 430453 := by norm_num

private theorem prime_seventyEightBX_434201 : Nat.Prime 434201 := by norm_num

private theorem prime_seventyEightBX_446189 : Nat.Prime 446189 := by norm_num

private theorem prime_seventyEightBX_464021 : Nat.Prime 464021 := by norm_num

private theorem prime_seventyEightBX_528419 : Nat.Prime 528419 := by norm_num

private theorem prime_seventyEightBX_530389 : Nat.Prime 530389 := by norm_num

private theorem prime_seventyEightBX_556709 : Nat.Prime 556709 := by norm_num

private theorem prime_seventyEightBX_574219 : Nat.Prime 574219 := by norm_num

private theorem prime_seventyEightBX_589493 : Nat.Prime 589493 := by norm_num

private theorem prime_seventyEightBX_625543 : Nat.Prime 625543 := by norm_num

private theorem prime_seventyEightBX_636653 : Nat.Prime 636653 := by norm_num

private theorem prime_seventyEightBX_660757 : Nat.Prime 660757 := by norm_num

private theorem prime_seventyEightBX_662617 : Nat.Prime 662617 := by norm_num

private theorem prime_seventyEightBX_727877 : Nat.Prime 727877 := by norm_num

private theorem prime_seventyEightBX_842771 : Nat.Prime 842771 := by norm_num

private theorem prime_seventyEightBX_923917 : Nat.Prime 923917 := by norm_num

private theorem prime_seventyEightBX_956231 : Nat.Prime 956231 := by norm_num

private theorem prime_seventyEightBX_971171 : Nat.Prime 971171 := by norm_num

private theorem prime_seventyEightBX_983699 : Nat.Prime 983699 := by norm_num

private theorem prime_seventyEightBX_1156097 : Nat.Prime 1156097 := by norm_num

private theorem prime_seventyEightBX_1194889 : Nat.Prime 1194889 := by norm_num

private theorem prime_seventyEightBX_1291313 : Nat.Prime 1291313 := by norm_num

private theorem prime_seventyEightBX_1293533 : Nat.Prime 1293533 := by norm_num

private theorem prime_seventyEightBX_1317067 : Nat.Prime 1317067 := by norm_num

private theorem prime_seventyEightBX_1367881 : Nat.Prime 1367881 := by norm_num

private theorem prime_seventyEightBX_1411331 : Nat.Prime 1411331 := by norm_num

private theorem prime_seventyEightBX_1517557 : Nat.Prime 1517557 := by norm_num

private theorem prime_seventyEightBX_1688231 : Nat.Prime 1688231 := by norm_num

private theorem prime_seventyEightBX_1723807 : Nat.Prime 1723807 := by norm_num

private theorem prime_seventyEightBX_1726441 : Nat.Prime 1726441 := by norm_num

private theorem prime_seventyEightBX_1738127 : Nat.Prime 1738127 := by norm_num

private theorem prime_seventyEightBX_1800637 : Nat.Prime 1800637 := by norm_num

private theorem prime_seventyEightBX_1929287 : Nat.Prime 1929287 := by norm_num

private theorem prime_seventyEightBX_1938239 : Nat.Prime 1938239 := by norm_num

private theorem prime_seventyEightBX_1992889 : Nat.Prime 1992889 := by norm_num

private theorem prime_seventyEightBX_1999619 : Nat.Prime 1999619 := by norm_num

private theorem prime_seventyEightBX_2188157 : Nat.Prime 2188157 := by norm_num

private theorem prime_seventyEightBX_2321881 : Nat.Prime 2321881 := by norm_num

private theorem prime_seventyEightBX_2337701 : Nat.Prime 2337701 := by norm_num

private theorem prime_seventyEightBX_2666267 : Nat.Prime 2666267 := by norm_num

private theorem prime_seventyEightBX_2669167 : Nat.Prime 2669167 := by norm_num

private theorem prime_seventyEightBX_2818841 : Nat.Prime 2818841 := by norm_num

private theorem prime_seventyEightBX_2860157 : Nat.Prime 2860157 := by norm_num

private theorem prime_seventyEightBX_3008267 : Nat.Prime 3008267 := by norm_num

private theorem prime_seventyEightBX_3010621 : Nat.Prime 3010621 := by norm_num

private theorem prime_seventyEightBX_3120323 : Nat.Prime 3120323 := by norm_num

private theorem prime_seventyEightBX_3347683 : Nat.Prime 3347683 := by norm_num

private theorem prime_seventyEightBX_3376759 : Nat.Prime 3376759 := by norm_num

private theorem prime_seventyEightBX_3532219 : Nat.Prime 3532219 := by norm_num

private theorem prime_seventyEightBX_3623701 : Nat.Prime 3623701 := by norm_num

private theorem prime_seventyEightBX_3919277 : Nat.Prime 3919277 := by norm_num

private theorem prime_seventyEightBX_4211653 : Nat.Prime 4211653 := by norm_num

private theorem prime_seventyEightBX_4355831 : Nat.Prime 4355831 := by norm_num

private theorem prime_seventyEightBX_4392313 : Nat.Prime 4392313 := by norm_num

private theorem prime_seventyEightBX_4686137 : Nat.Prime 4686137 := by norm_num

private theorem prime_seventyEightBX_4740979 : Nat.Prime 4740979 := by norm_num

private theorem prime_seventyEightBX_4828303 : Nat.Prime 4828303 := by norm_num

private theorem prime_seventyEightBX_4890827 : Nat.Prime 4890827 := by norm_num

private theorem prime_seventyEightBX_5102243 : Nat.Prime 5102243 := by norm_num

private theorem prime_seventyEightBX_5374177 : Nat.Prime 5374177 := by norm_num

private theorem prime_seventyEightBX_5392307 : Nat.Prime 5392307 := by norm_num

private theorem prime_seventyEightBX_5549659 : Nat.Prime 5549659 := by norm_num

private theorem prime_seventyEightBX_5645483 : Nat.Prime 5645483 := by norm_num

private theorem prime_seventyEightBX_6220517 : Nat.Prime 6220517 := by norm_num

private theorem prime_seventyEightBX_6495527 : Nat.Prime 6495527 := by norm_num

private theorem prime_seventyEightBX_6862571 : Nat.Prime 6862571 := by norm_num

private theorem prime_seventyEightBX_7310959 : Nat.Prime 7310959 := by norm_num

private theorem prime_seventyEightBX_7461329 : Nat.Prime 7461329 := by norm_num

private theorem prime_seventyEightBX_7696573 : Nat.Prime 7696573 := by norm_num

private theorem prime_seventyEightBX_8299283 : Nat.Prime 8299283 := by norm_num

private theorem prime_seventyEightBX_9093421 : Nat.Prime 9093421 := by norm_num

private theorem prime_seventyEightBX_9246233 : Nat.Prime 9246233 := by norm_num

private theorem prime_seventyEightBX_9650983 : Nat.Prime 9650983 := by norm_num

private theorem prime_seventyEightBX_10516993 : Nat.Prime 10516993 := by norm_num

private theorem prime_seventyEightBX_11111809 : Nat.Prime 11111809 := by norm_num

private theorem prime_seventyEightBX_11183189 : Nat.Prime 11183189 := by norm_num

private theorem prime_seventyEightBX_11740229 : Nat.Prime 11740229 := by norm_num

private theorem prime_seventyEightBX_11968067 : Nat.Prime 11968067 := by norm_num

private theorem prime_seventyEightBX_12556139 : Nat.Prime 12556139 := by norm_num

private theorem prime_seventyEightBX_12672067 : Nat.Prime 12672067 := by norm_num

private theorem prime_seventyEightBX_12919559 : Nat.Prime 12919559 := by norm_num

private theorem prime_seventyEightBX_13858381 : Nat.Prime 13858381 := by norm_num

private theorem prime_seventyEightBX_14347919 : Nat.Prime 14347919 := by norm_num

private theorem prime_seventyEightBX_14572391 : Nat.Prime 14572391 := by norm_num

private theorem prime_seventyEightBX_14993929 : Nat.Prime 14993929 := by norm_num

private theorem prime_seventyEightBX_15680471 : Nat.Prime 15680471 := by norm_num

private theorem prime_seventyEightBX_15787393 : Nat.Prime 15787393 := by norm_num

private theorem prime_seventyEightBX_15807853 : Nat.Prime 15807853 := by norm_num

private theorem prime_seventyEightBX_15995339 : Nat.Prime 15995339 := by norm_num

private theorem prime_seventyEightBX_16231273 : Nat.Prime 16231273 := by norm_num

private theorem prime_seventyEightBX_17094331 : Nat.Prime 17094331 := by norm_num

private theorem prime_seventyEightBX_17805911 : Nat.Prime 17805911 := by norm_num

private theorem prime_seventyEightBX_18077177 : Nat.Prime 18077177 := by norm_num

private theorem prime_seventyEightBX_19605277 : Nat.Prime 19605277 := by norm_num

private theorem prime_seventyEightBX_21450931 : Nat.Prime 21450931 := by norm_num

private theorem prime_seventyEightBX_22537799 : Nat.Prime 22537799 := by norm_num

private theorem prime_seventyEightBX_23625919 : Nat.Prime 23625919 := by norm_num

private theorem prime_seventyEightBX_27599899 : Nat.Prime 27599899 := by norm_num

private theorem prime_seventyEightBX_31435787 : Nat.Prime 31435787 := by
  apply lucas_primality 31435787 (2 : ZMod 31435787)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1721, 1), (9133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1721, 1), (9133, 1)] : List FactorBlock).map factorBlockValue).prod) = 31435787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_1721
      · exact prime_seventyEightBX_9133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 31435787) ^ 15717893 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 31435787) ^ 18266 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 31435787) ^ 3442 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_37219873 : Nat.Prime 37219873 := by
  apply lucas_primality 37219873 (5 : ZMod 37219873)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (387707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (387707, 1)] : List FactorBlock).map factorBlockValue).prod) = 37219873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_387707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 37219873) ^ 18609936 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 37219873) ^ 12406624 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 37219873) ^ 96 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_37379291 : Nat.Prime 37379291 := by
  apply lucas_primality 37379291 (6 : ZMod 37379291)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (41, 1), (7013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (41, 1), (7013, 1)] : List FactorBlock).map factorBlockValue).prod) = 37379291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_13
      · exact prime_seventyEightBX_41
      · exact prime_seventyEightBX_7013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 37379291) ^ 18689645 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 37379291) ^ 7475858 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 37379291) ^ 2875330 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 37379291) ^ 911690 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 37379291) ^ 5330 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_38069159 : Nat.Prime 38069159 := by
  apply lucas_primality 38069159 (7 : ZMod 38069159)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (359143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (359143, 1)] : List FactorBlock).map factorBlockValue).prod) = 38069159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_53
      · exact prime_seventyEightBX_359143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 38069159) ^ 19034579 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 38069159) ^ 718286 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 38069159) ^ 106 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_42756079 : Nat.Prime 42756079 := by
  apply lucas_primality 42756079 (3 : ZMod 42756079)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1747, 1), (4079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1747, 1), (4079, 1)] : List FactorBlock).map factorBlockValue).prod) = 42756079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_1747
      · exact prime_seventyEightBX_4079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 42756079) ^ 21378039 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 42756079) ^ 14252026 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 42756079) ^ 24474 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 42756079) ^ 10482 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_43354499 : Nat.Prime 43354499 := by
  apply lucas_primality 43354499 (2 : ZMod 43354499)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (59, 1), (127, 1), (263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (59, 1), (127, 1), (263, 1)] : List FactorBlock).map factorBlockValue).prod) = 43354499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_11
      · exact prime_seventyEightBX_59
      · exact prime_seventyEightBX_127
      · exact prime_seventyEightBX_263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 43354499) ^ 21677249 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 43354499) ^ 3941318 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 43354499) ^ 734822 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 43354499) ^ 341374 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 43354499) ^ 164846 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_47156413 : Nat.Prime 47156413 := by
  apply lucas_primality 47156413 (2 : ZMod 47156413)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1409, 1), (2789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1409, 1), (2789, 1)] : List FactorBlock).map factorBlockValue).prod) = 47156413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_1409
      · exact prime_seventyEightBX_2789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 47156413) ^ 23578206 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 47156413) ^ 15718804 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 47156413) ^ 33468 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 47156413) ^ 16908 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_53741771 : Nat.Prime 53741771 := by
  apply lucas_primality 53741771 (2 : ZMod 53741771)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (5374177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (5374177, 1)] : List FactorBlock).map factorBlockValue).prod) = 53741771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_5374177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 53741771) ^ 26870885 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 53741771) ^ 10748354 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 53741771) ^ 10 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_60624517 : Nat.Prime 60624517 := by
  apply lucas_primality 60624517 (5 : ZMod 60624517)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (19, 1), (15641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (19, 1), (15641, 1)] : List FactorBlock).map factorBlockValue).prod) = 60624517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_17
      · exact prime_seventyEightBX_19
      · exact prime_seventyEightBX_15641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 60624517) ^ 30312258 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 60624517) ^ 20208172 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 60624517) ^ 3566148 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 60624517) ^ 3190764 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 60624517) ^ 3876 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_65704567 : Nat.Prime 65704567 := by
  apply lucas_primality 65704567 (5 : ZMod 65704567)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1823, 1), (6007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1823, 1), (6007, 1)] : List FactorBlock).map factorBlockValue).prod) = 65704567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_1823
      · exact prime_seventyEightBX_6007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 65704567) ^ 32852283 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 65704567) ^ 21901522 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 65704567) ^ 36042 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 65704567) ^ 10938 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_72459509 : Nat.Prime 72459509 := by
  apply lucas_primality 72459509 (2 : ZMod 72459509)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (17, 1), (73, 1), (1327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (17, 1), (73, 1), (1327, 1)] : List FactorBlock).map factorBlockValue).prod) = 72459509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_11
      · exact prime_seventyEightBX_17
      · exact prime_seventyEightBX_73
      · exact prime_seventyEightBX_1327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 72459509) ^ 36229754 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 72459509) ^ 6587228 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 72459509) ^ 4262324 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 72459509) ^ 992596 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 72459509) ^ 54604 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_78404959 : Nat.Prime 78404959 := by
  apply lucas_primality 78404959 (3 : ZMod 78404959)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (4355831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (4355831, 1)] : List FactorBlock).map factorBlockValue).prod) = 78404959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_4355831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 78404959) ^ 39202479 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 78404959) ^ 26134986 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 78404959) ^ 18 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_85282517 : Nat.Prime 85282517 := by
  apply lucas_primality 85282517 (2 : ZMod 85282517)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (1938239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (1938239, 1)] : List FactorBlock).map factorBlockValue).prod) = 85282517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_11
      · exact prime_seventyEightBX_1938239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 85282517) ^ 42641258 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 85282517) ^ 7752956 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 85282517) ^ 44 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_86560667 : Nat.Prime 86560667 := by
  apply lucas_primality 86560667 (2 : ZMod 86560667)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (97, 1), (446189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (97, 1), (446189, 1)] : List FactorBlock).map factorBlockValue).prod) = 86560667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_97
      · exact prime_seventyEightBX_446189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 86560667) ^ 43280333 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 86560667) ^ 892378 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 86560667) ^ 194 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_96402503 : Nat.Prime 96402503 := by
  apply lucas_primality 96402503 (5 : ZMod 96402503)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (983699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (983699, 1)] : List FactorBlock).map factorBlockValue).prod) = 96402503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_983699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 96402503) ^ 48201251 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 96402503) ^ 13771786 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 96402503) ^ 98 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_102565987 : Nat.Prime 102565987 := by
  apply lucas_primality 102565987 (3 : ZMod 102565987)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17094331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17094331, 1)] : List FactorBlock).map factorBlockValue).prod) = 102565987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_17094331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 102565987) ^ 51282993 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 102565987) ^ 34188662 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 102565987) ^ 6 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_118391323 : Nat.Prime 118391323 := by
  apply lucas_primality 118391323 (3 : ZMod 118391323)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (2818841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (2818841, 1)] : List FactorBlock).map factorBlockValue).prod) = 118391323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_2818841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 118391323) ^ 59195661 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 118391323) ^ 39463774 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 118391323) ^ 16913046 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 118391323) ^ 42 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_119135249 : Nat.Prime 119135249 := by
  apply lucas_primality 119135249 (3 : ZMod 119135249)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (29, 1), (256757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (29, 1), (256757, 1)] : List FactorBlock).map factorBlockValue).prod) = 119135249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_29
      · exact prime_seventyEightBX_256757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 119135249) ^ 59567624 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 119135249) ^ 4108112 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 119135249) ^ 464 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_138583811 : Nat.Prime 138583811 := by
  apply lucas_primality 138583811 (2 : ZMod 138583811)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13858381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13858381, 1)] : List FactorBlock).map factorBlockValue).prod) = 138583811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_13858381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 138583811) ^ 69291905 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 138583811) ^ 27716762 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 138583811) ^ 10 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_156016151 : Nat.Prime 156016151 := by
  apply lucas_primality 156016151 (7 : ZMod 156016151)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (3120323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (3120323, 1)] : List FactorBlock).map factorBlockValue).prod) = 156016151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_3120323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 156016151) ^ 78008075 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 156016151) ^ 31203230 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 156016151) ^ 50 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_163271777 : Nat.Prime 163271777 := by
  apply lucas_primality 163271777 (3 : ZMod 163271777)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5102243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5102243, 1)] : List FactorBlock).map factorBlockValue).prod) = 163271777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_5102243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 163271777) ^ 81635888 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 163271777) ^ 32 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_169781627 : Nat.Prime 169781627 := by
  apply lucas_primality 169781627 (2 : ZMod 169781627)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (149, 1), (199, 1), (409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (149, 1), (199, 1), (409, 1)] : List FactorBlock).map factorBlockValue).prod) = 169781627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_149
      · exact prime_seventyEightBX_199
      · exact prime_seventyEightBX_409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 169781627) ^ 84890813 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 169781627) ^ 24254518 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 169781627) ^ 1139474 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 169781627) ^ 853174 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 169781627) ^ 415114 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_251943121 : Nat.Prime 251943121 := by
  apply lucas_primality 251943121 (17 : ZMod 251943121)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (11, 1), (13, 1), (2447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (11, 1), (13, 1), (2447, 1)] : List FactorBlock).map factorBlockValue).prod) = 251943121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_11
      · exact prime_seventyEightBX_13
      · exact prime_seventyEightBX_2447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 251943121) ^ 125971560 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (17 : ZMod 251943121) ^ 83981040 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (17 : ZMod 251943121) ^ 50388624 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (17 : ZMod 251943121) ^ 22903920 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (17 : ZMod 251943121) ^ 19380240 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (17 : ZMod 251943121) ^ 102960 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_276556517 : Nat.Prime 276556517 := by
  apply lucas_primality 276556517 (2 : ZMod 276556517)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (149, 1), (464021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (149, 1), (464021, 1)] : List FactorBlock).map factorBlockValue).prod) = 276556517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_149
      · exact prime_seventyEightBX_464021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 276556517) ^ 138278258 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 276556517) ^ 1856084 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 276556517) ^ 596 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_294907933 : Nat.Prime 294907933 := by
  apply lucas_primality 294907933 (2 : ZMod 294907933)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (11, 1), (23, 1), (43, 1), (251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (11, 1), (23, 1), (43, 1), (251, 1)] : List FactorBlock).map factorBlockValue).prod) = 294907933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_11
      · exact prime_seventyEightBX_23
      · exact prime_seventyEightBX_43
      · exact prime_seventyEightBX_251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 294907933) ^ 147453966 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 294907933) ^ 98302644 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 294907933) ^ 26809812 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 294907933) ^ 12822084 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 294907933) ^ 6858324 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 294907933) ^ 1174932 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_309440777 : Nat.Prime 309440777 := by
  apply lucas_primality 309440777 (3 : ZMod 309440777)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (41, 1), (233, 1), (4049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (41, 1), (233, 1), (4049, 1)] : List FactorBlock).map factorBlockValue).prod) = 309440777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_41
      · exact prime_seventyEightBX_233
      · exact prime_seventyEightBX_4049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 309440777) ^ 154720388 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 309440777) ^ 7547336 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 309440777) ^ 1328072 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 309440777) ^ 76424 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_315124471 : Nat.Prime 315124471 := by
  apply lucas_primality 315124471 (3 : ZMod 315124471)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (503, 1), (6961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (503, 1), (6961, 1)] : List FactorBlock).map factorBlockValue).prod) = 315124471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_503
      · exact prime_seventyEightBX_6961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 315124471) ^ 157562235 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 315124471) ^ 105041490 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 315124471) ^ 63024894 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 315124471) ^ 626490 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 315124471) ^ 45270 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_347772767 : Nat.Prime 347772767 := by
  apply lucas_primality 347772767 (10 : ZMod 347772767)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (15807853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (15807853, 1)] : List FactorBlock).map factorBlockValue).prod) = 347772767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_11
      · exact prime_seventyEightBX_15807853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 347772767) ^ 173886383 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (10 : ZMod 347772767) ^ 31615706 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (10 : ZMod 347772767) ^ 22 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_355928147 : Nat.Prime 355928147 := by
  apply lucas_primality 355928147 (2 : ZMod 355928147)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1523, 1), (16693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1523, 1), (16693, 1)] : List FactorBlock).map factorBlockValue).prod) = 355928147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_1523
      · exact prime_seventyEightBX_16693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 355928147) ^ 177964073 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 355928147) ^ 50846878 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 355928147) ^ 233702 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 355928147) ^ 21322 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_401861413 : Nat.Prime 401861413 := by
  apply lucas_primality 401861413 (2 : ZMod 401861413)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (61, 1), (20333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (61, 1), (20333, 1)] : List FactorBlock).map factorBlockValue).prod) = 401861413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_61
      · exact prime_seventyEightBX_20333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 401861413) ^ 200930706 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 401861413) ^ 133953804 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 401861413) ^ 6587892 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 401861413) ^ 19764 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_407763371 : Nat.Prime 407763371 := by
  apply lucas_primality 407763371 (7 : ZMod 407763371)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (19, 1), (306589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (19, 1), (306589, 1)] : List FactorBlock).map factorBlockValue).prod) = 407763371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_19
      · exact prime_seventyEightBX_306589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 407763371) ^ 203881685 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 407763371) ^ 81552674 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 407763371) ^ 58251910 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 407763371) ^ 21461230 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 407763371) ^ 1330 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_446794223 : Nat.Prime 446794223 := by
  apply lucas_primality 446794223 (5 : ZMod 446794223)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (97, 1), (329009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (97, 1), (329009, 1)] : List FactorBlock).map factorBlockValue).prod) = 446794223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_97
      · exact prime_seventyEightBX_329009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 446794223) ^ 223397111 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 446794223) ^ 63827746 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 446794223) ^ 4606126 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 446794223) ^ 1358 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_478463177 : Nat.Prime 478463177 := by
  apply lucas_primality 478463177 (3 : ZMod 478463177)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (1929287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (1929287, 1)] : List FactorBlock).map factorBlockValue).prod) = 478463177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_31
      · exact prime_seventyEightBX_1929287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 478463177) ^ 239231588 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 478463177) ^ 15434296 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 478463177) ^ 248 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_547215289 : Nat.Prime 547215289 := by
  apply lucas_primality 547215289 (17 : ZMod 547215289)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (3877, 1), (5881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (3877, 1), (5881, 1)] : List FactorBlock).map factorBlockValue).prod) = 547215289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_3877
      · exact prime_seventyEightBX_5881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 547215289) ^ 273607644 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (17 : ZMod 547215289) ^ 182405096 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (17 : ZMod 547215289) ^ 141144 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (17 : ZMod 547215289) ^ 93048 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_615395923 : Nat.Prime 615395923 := by
  apply lucas_primality 615395923 (2 : ZMod 615395923)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (102565987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (102565987, 1)] : List FactorBlock).map factorBlockValue).prod) = 615395923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_102565987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 615395923) ^ 307697961 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 615395923) ^ 205131974 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 615395923) ^ 6 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_624483161 : Nat.Prime 624483161 := by
  apply lucas_primality 624483161 (3 : ZMod 624483161)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (281, 1), (7937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (281, 1), (7937, 1)] : List FactorBlock).map factorBlockValue).prod) = 624483161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_281
      · exact prime_seventyEightBX_7937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 624483161) ^ 312241580 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 624483161) ^ 124896632 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 624483161) ^ 89211880 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 624483161) ^ 2222360 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 624483161) ^ 78680 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_672847421 : Nat.Prime 672847421 := by
  apply lucas_primality 672847421 (3 : ZMod 672847421)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 2), (17, 1), (40387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 2), (17, 1), (40387, 1)] : List FactorBlock).map factorBlockValue).prod) = 672847421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_17
      · exact prime_seventyEightBX_40387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 672847421) ^ 336423710 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 672847421) ^ 134569484 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 672847421) ^ 96121060 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 672847421) ^ 39579260 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 672847421) ^ 16660 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_704629103 : Nat.Prime 704629103 := by
  apply lucas_primality 704629103 (5 : ZMod 704629103)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1201, 1), (293351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1201, 1), (293351, 1)] : List FactorBlock).map factorBlockValue).prod) = 704629103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_1201
      · exact prime_seventyEightBX_293351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 704629103) ^ 352314551 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 704629103) ^ 586702 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 704629103) ^ 2402 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_716778593 : Nat.Prime 716778593 := by
  apply lucas_primality 716778593 (3 : ZMod 716778593)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (1153, 1), (19427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (1153, 1), (19427, 1)] : List FactorBlock).map factorBlockValue).prod) = 716778593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_1153
      · exact prime_seventyEightBX_19427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 716778593) ^ 358389296 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 716778593) ^ 621664 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 716778593) ^ 36896 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_810992503 : Nat.Prime 810992503 := by
  apply lucas_primality 810992503 (5 : ZMod 810992503)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (83, 1), (647, 1), (839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (83, 1), (647, 1), (839, 1)] : List FactorBlock).map factorBlockValue).prod) = 810992503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_83
      · exact prime_seventyEightBX_647
      · exact prime_seventyEightBX_839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 810992503) ^ 405496251 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 810992503) ^ 270330834 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 810992503) ^ 9770994 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 810992503) ^ 1253466 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 810992503) ^ 966618 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_858431347 : Nat.Prime 858431347 := by
  apply lucas_primality 858431347 (2 : ZMod 858431347)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (6220517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (6220517, 1)] : List FactorBlock).map factorBlockValue).prod) = 858431347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_23
      · exact prime_seventyEightBX_6220517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 858431347) ^ 429215673 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 858431347) ^ 286143782 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 858431347) ^ 37323102 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 858431347) ^ 138 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_1372637333 : Nat.Prime 1372637333 := by
  apply lucas_primality 1372637333 (3 : ZMod 1372637333)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (23, 1), (859, 1), (1579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (23, 1), (859, 1), (1579, 1)] : List FactorBlock).map factorBlockValue).prod) = 1372637333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_11
      · exact prime_seventyEightBX_23
      · exact prime_seventyEightBX_859
      · exact prime_seventyEightBX_1579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1372637333) ^ 686318666 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1372637333) ^ 124785212 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1372637333) ^ 59679884 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1372637333) ^ 1597948 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1372637333) ^ 869308 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_1480533629 : Nat.Prime 1480533629 := by
  apply lucas_primality 1480533629 (2 : ZMod 1480533629)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (79, 1), (95617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (79, 1), (95617, 1)] : List FactorBlock).map factorBlockValue).prod) = 1480533629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_79
      · exact prime_seventyEightBX_95617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1480533629) ^ 740266814 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1480533629) ^ 211504804 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1480533629) ^ 18740932 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1480533629) ^ 15484 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_1501698479 : Nat.Prime 1501698479 := by
  apply lucas_primality 1501698479 (7 : ZMod 1501698479)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (5645483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (5645483, 1)] : List FactorBlock).map factorBlockValue).prod) = 1501698479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_19
      · exact prime_seventyEightBX_5645483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1501698479) ^ 750849239 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1501698479) ^ 214528354 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1501698479) ^ 79036762 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1501698479) ^ 266 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_1584407437 : Nat.Prime 1584407437 := by
  apply lucas_primality 1584407437 (2 : ZMod 1584407437)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (8963, 1), (14731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (8963, 1), (14731, 1)] : List FactorBlock).map factorBlockValue).prod) = 1584407437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_8963
      · exact prime_seventyEightBX_14731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1584407437) ^ 792203718 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1584407437) ^ 528135812 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1584407437) ^ 176772 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1584407437) ^ 107556 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_1596355169 : Nat.Prime 1596355169 := by
  apply lucas_primality 1596355169 (3 : ZMod 1596355169)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (31, 1), (677, 1), (2377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (31, 1), (677, 1), (2377, 1)] : List FactorBlock).map factorBlockValue).prod) = 1596355169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_31
      · exact prime_seventyEightBX_677
      · exact prime_seventyEightBX_2377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1596355169) ^ 798177584 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1596355169) ^ 51495328 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1596355169) ^ 2357984 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1596355169) ^ 671584 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_1687009321 : Nat.Prime 1687009321 := by
  apply lucas_primality 1687009321 (17 : ZMod 1687009321)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (4686137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (4686137, 1)] : List FactorBlock).map factorBlockValue).prod) = 1687009321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_4686137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 1687009321) ^ 843504660 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (17 : ZMod 1687009321) ^ 562336440 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (17 : ZMod 1687009321) ^ 337401864 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (17 : ZMod 1687009321) ^ 360 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_1705322417 : Nat.Prime 1705322417 := by
  apply lucas_primality 1705322417 (3 : ZMod 1705322417)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (2207, 1), (6899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (2207, 1), (6899, 1)] : List FactorBlock).map factorBlockValue).prod) = 1705322417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_2207
      · exact prime_seventyEightBX_6899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1705322417) ^ 852661208 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1705322417) ^ 243617488 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1705322417) ^ 772688 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1705322417) ^ 247184 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_1870231403 : Nat.Prime 1870231403 := by
  apply lucas_primality 1870231403 (2 : ZMod 1870231403)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 4), (29, 1), (1129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 4), (29, 1), (1129, 1)] : List FactorBlock).map factorBlockValue).prod) = 1870231403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_13
      · exact prime_seventyEightBX_29
      · exact prime_seventyEightBX_1129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1870231403) ^ 935115701 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1870231403) ^ 143863954 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1870231403) ^ 64490738 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1870231403) ^ 1656538 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_2237401043 : Nat.Prime 2237401043 := by
  apply lucas_primality 2237401043 (2 : ZMod 2237401043)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (53, 1), (173, 1), (7177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (53, 1), (173, 1), (7177, 1)] : List FactorBlock).map factorBlockValue).prod) = 2237401043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_17
      · exact prime_seventyEightBX_53
      · exact prime_seventyEightBX_173
      · exact prime_seventyEightBX_7177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2237401043) ^ 1118700521 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2237401043) ^ 131611826 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2237401043) ^ 42215114 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2237401043) ^ 12932954 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2237401043) ^ 311746 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_2347099483 : Nat.Prime 2347099483 := by
  apply lucas_primality 2347099483 (37 : ZMod 2347099483)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (241, 1), (17837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (241, 1), (17837, 1)] : List FactorBlock).map factorBlockValue).prod) = 2347099483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_13
      · exact prime_seventyEightBX_241
      · exact prime_seventyEightBX_17837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (37 : ZMod 2347099483) ^ 1173549741 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (37 : ZMod 2347099483) ^ 782366494 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (37 : ZMod 2347099483) ^ 335299926 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (37 : ZMod 2347099483) ^ 180546114 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (37 : ZMod 2347099483) ^ 9739002 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (37 : ZMod 2347099483) ^ 131586 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_2391596869 : Nat.Prime 2391596869 := by
  apply lucas_primality 2391596869 (2 : ZMod 2391596869)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (463, 1), (430453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (463, 1), (430453, 1)] : List FactorBlock).map factorBlockValue).prod) = 2391596869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_463
      · exact prime_seventyEightBX_430453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2391596869) ^ 1195798434 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2391596869) ^ 797198956 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2391596869) ^ 5165436 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2391596869) ^ 5556 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_2483725133 : Nat.Prime 2483725133 := by
  apply lucas_primality 2483725133 (2 : ZMod 2483725133)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (12672067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (12672067, 1)] : List FactorBlock).map factorBlockValue).prod) = 2483725133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_12672067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2483725133) ^ 1241862566 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2483725133) ^ 354817876 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2483725133) ^ 196 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_2638788283 : Nat.Prime 2638788283 := by
  apply lucas_primality 2638788283 (2 : ZMod 2638788283)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (131, 1), (86083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (131, 1), (86083, 1)] : List FactorBlock).map factorBlockValue).prod) = 2638788283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_13
      · exact prime_seventyEightBX_131
      · exact prime_seventyEightBX_86083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2638788283) ^ 1319394141 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2638788283) ^ 879596094 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2638788283) ^ 202983714 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2638788283) ^ 20143422 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2638788283) ^ 30654 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_2826217577 : Nat.Prime 2826217577 := by
  apply lucas_primality 2826217577 (3 : ZMod 2826217577)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (13, 1), (41, 1), (94687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (13, 1), (41, 1), (94687, 1)] : List FactorBlock).map factorBlockValue).prod) = 2826217577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_13
      · exact prime_seventyEightBX_41
      · exact prime_seventyEightBX_94687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2826217577) ^ 1413108788 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2826217577) ^ 403745368 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2826217577) ^ 217401352 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2826217577) ^ 68932136 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2826217577) ^ 29848 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_3003396959 : Nat.Prime 3003396959 := by
  apply lucas_primality 3003396959 (17 : ZMod 3003396959)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1501698479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1501698479, 1)] : List FactorBlock).map factorBlockValue).prod) = 3003396959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_1501698479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (17 : ZMod 3003396959) ^ 1501698479 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (17 : ZMod 3003396959) ^ 2 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_3598037117 : Nat.Prime 3598037117 := by
  apply lucas_primality 3598037117 (2 : ZMod 3598037117)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (337, 1), (2669167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (337, 1), (2669167, 1)] : List FactorBlock).map factorBlockValue).prod) = 3598037117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_337
      · exact prime_seventyEightBX_2669167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3598037117) ^ 1799018558 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3598037117) ^ 10676668 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3598037117) ^ 1348 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_3701479099 : Nat.Prime 3701479099 := by
  apply lucas_primality 3701479099 (3 : ZMod 3701479099)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (197, 1), (76379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (197, 1), (76379, 1)] : List FactorBlock).map factorBlockValue).prod) = 3701479099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_41
      · exact prime_seventyEightBX_197
      · exact prime_seventyEightBX_76379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3701479099) ^ 1850739549 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3701479099) ^ 1233826366 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3701479099) ^ 90279978 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3701479099) ^ 18789234 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3701479099) ^ 48462 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_3768812123 : Nat.Prime 3768812123 := by
  apply lucas_primality 3768812123 (2 : ZMod 3768812123)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (109, 1), (127, 1), (197, 1), (691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (109, 1), (127, 1), (197, 1), (691, 1)] : List FactorBlock).map factorBlockValue).prod) = 3768812123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_109
      · exact prime_seventyEightBX_127
      · exact prime_seventyEightBX_197
      · exact prime_seventyEightBX_691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3768812123) ^ 1884406061 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3768812123) ^ 34576258 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3768812123) ^ 29675686 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3768812123) ^ 19131026 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3768812123) ^ 5454142 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_4690199621 : Nat.Prime 4690199621 := by
  apply lucas_primality 4690199621 (3 : ZMod 4690199621)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (101, 1), (2321881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (101, 1), (2321881, 1)] : List FactorBlock).map factorBlockValue).prod) = 4690199621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_101
      · exact prime_seventyEightBX_2321881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4690199621) ^ 2345099810 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 4690199621) ^ 938039924 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 4690199621) ^ 46437620 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 4690199621) ^ 2020 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_4934066413 : Nat.Prime 4934066413 := by
  apply lucas_primality 4934066413 (2 : ZMod 4934066413)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (37379291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (37379291, 1)] : List FactorBlock).map factorBlockValue).prod) = 4934066413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_11
      · exact prime_seventyEightBX_37379291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4934066413) ^ 2467033206 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4934066413) ^ 1644688804 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4934066413) ^ 448551492 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4934066413) ^ 132 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_4995887929 : Nat.Prime 4995887929 := by
  apply lucas_primality 4995887929 (19 : ZMod 4995887929)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (8053, 1), (25849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (8053, 1), (25849, 1)] : List FactorBlock).map factorBlockValue).prod) = 4995887929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_8053
      · exact prime_seventyEightBX_25849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 4995887929) ^ 2497943964 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (19 : ZMod 4995887929) ^ 1665295976 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (19 : ZMod 4995887929) ^ 620376 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (19 : ZMod 4995887929) ^ 193272 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_5207232059 : Nat.Prime 5207232059 := by
  apply lucas_primality 5207232059 (2 : ZMod 5207232059)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (73, 1), (727877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (73, 1), (727877, 1)] : List FactorBlock).map factorBlockValue).prod) = 5207232059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_73
      · exact prime_seventyEightBX_727877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5207232059) ^ 2603616029 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5207232059) ^ 743890294 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5207232059) ^ 71331946 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5207232059) ^ 7154 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_5230683487 : Nat.Prime 5230683487 := by
  apply lucas_primality 5230683487 (3 : ZMod 5230683487)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (41, 1), (43, 1), (47, 1), (167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (41, 1), (43, 1), (47, 1), (167, 1)] : List FactorBlock).map factorBlockValue).prod) = 5230683487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_41
      · exact prime_seventyEightBX_43
      · exact prime_seventyEightBX_47
      · exact prime_seventyEightBX_167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5230683487) ^ 2615341743 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 5230683487) ^ 1743561162 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 5230683487) ^ 747240498 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 5230683487) ^ 127577646 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 5230683487) ^ 121643802 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 5230683487) ^ 111291138 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 5230683487) ^ 31321458 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_6002856239 : Nat.Prime 6002856239 := by
  apply lucas_primality 6002856239 (7 : ZMod 6002856239)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (79, 1), (1999619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (79, 1), (1999619, 1)] : List FactorBlock).map factorBlockValue).prod) = 6002856239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_19
      · exact prime_seventyEightBX_79
      · exact prime_seventyEightBX_1999619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 6002856239) ^ 3001428119 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 6002856239) ^ 315939802 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 6002856239) ^ 75985522 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 6002856239) ^ 3002 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_7003805663 : Nat.Prime 7003805663 := by
  apply lucas_primality 7003805663 (5 : ZMod 7003805663)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1187, 1), (421459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1187, 1), (421459, 1)] : List FactorBlock).map factorBlockValue).prod) = 7003805663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_1187
      · exact prime_seventyEightBX_421459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7003805663) ^ 3501902831 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 7003805663) ^ 1000543666 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 7003805663) ^ 5900426 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 7003805663) ^ 16618 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_8368731841 : Nat.Prime 8368731841 := by
  apply lucas_primality 8368731841 (17 : ZMod 8368731841)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (7, 1), (29, 1), (42943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (7, 1), (29, 1), (42943, 1)] : List FactorBlock).map factorBlockValue).prod) = 8368731841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_29
      · exact prime_seventyEightBX_42943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 8368731841) ^ 4184365920 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (17 : ZMod 8368731841) ^ 2789577280 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (17 : ZMod 8368731841) ^ 1673746368 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (17 : ZMod 8368731841) ^ 1195533120 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (17 : ZMod 8368731841) ^ 288576960 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (17 : ZMod 8368731841) ^ 194880 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_9223453697 : Nat.Prime 9223453697 := by
  apply lucas_primality 9223453697 (3 : ZMod 9223453697)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (67, 1), (134437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (67, 1), (134437, 1)] : List FactorBlock).map factorBlockValue).prod) = 9223453697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_67
      · exact prime_seventyEightBX_134437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 9223453697) ^ 4611726848 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 9223453697) ^ 137663488 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 9223453697) ^ 68608 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_9246139447 : Nat.Prime 9246139447 := by
  apply lucas_primality 9246139447 (5 : ZMod 9246139447)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (197, 1), (887, 1), (8819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (197, 1), (887, 1), (8819, 1)] : List FactorBlock).map factorBlockValue).prod) = 9246139447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_197
      · exact prime_seventyEightBX_887
      · exact prime_seventyEightBX_8819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 9246139447) ^ 4623069723 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 9246139447) ^ 3082046482 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 9246139447) ^ 46934718 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 9246139447) ^ 10424058 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 9246139447) ^ 1048434 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_9380399243 : Nat.Prime 9380399243 := by
  apply lucas_primality 9380399243 (2 : ZMod 9380399243)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4690199621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4690199621, 1)] : List FactorBlock).map factorBlockValue).prod) = 9380399243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_4690199621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 9380399243) ^ 4690199621 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 9380399243) ^ 2 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_9860314021 : Nat.Prime 9860314021 := by
  apply lucas_primality 9860314021 (7 : ZMod 9860314021)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (617, 1), (266351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (617, 1), (266351, 1)] : List FactorBlock).map factorBlockValue).prod) = 9860314021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_617
      · exact prime_seventyEightBX_266351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 9860314021) ^ 4930157010 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 9860314021) ^ 3286771340 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 9860314021) ^ 1972062804 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 9860314021) ^ 15981060 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 9860314021) ^ 37020 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_11393719709 : Nat.Prime 11393719709 := by
  apply lucas_primality 11393719709 (3 : ZMod 11393719709)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (5693, 1), (10211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (5693, 1), (10211, 1)] : List FactorBlock).map factorBlockValue).prod) = 11393719709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_5693
      · exact prime_seventyEightBX_10211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 11393719709) ^ 5696859854 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 11393719709) ^ 1627674244 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 11393719709) ^ 2001356 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 11393719709) ^ 1115828 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_11844269033 : Nat.Prime 11844269033 := by
  apply lucas_primality 11844269033 (3 : ZMod 11844269033)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1480533629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1480533629, 1)] : List FactorBlock).map factorBlockValue).prod) = 11844269033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_1480533629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 11844269033) ^ 5922134516 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 11844269033) ^ 8 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_11877577609 : Nat.Prime 11877577609 := by
  apply lucas_primality 11877577609 (11 : ZMod 11877577609)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (38069159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (38069159, 1)] : List FactorBlock).map factorBlockValue).prod) = 11877577609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_13
      · exact prime_seventyEightBX_38069159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 11877577609) ^ 5938788804 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (11 : ZMod 11877577609) ^ 3959192536 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (11 : ZMod 11877577609) ^ 913659816 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (11 : ZMod 11877577609) ^ 312 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_13299785203 : Nat.Prime 13299785203 := by
  apply lucas_primality 13299785203 (3 : ZMod 13299785203)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (17, 2), (109, 1), (6397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (17, 2), (109, 1), (6397, 1)] : List FactorBlock).map factorBlockValue).prod) = 13299785203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_11
      · exact prime_seventyEightBX_17
      · exact prime_seventyEightBX_109
      · exact prime_seventyEightBX_6397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13299785203) ^ 6649892601 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 13299785203) ^ 4433261734 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 13299785203) ^ 1209071382 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 13299785203) ^ 782340306 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 13299785203) ^ 122016378 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 13299785203) ^ 2079066 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_14070560171 : Nat.Prime 14070560171 := by
  apply lucas_primality 14070560171 (2 : ZMod 14070560171)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (29, 1), (37, 1), (77137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (29, 1), (37, 1), (77137, 1)] : List FactorBlock).map factorBlockValue).prod) = 14070560171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_17
      · exact prime_seventyEightBX_29
      · exact prime_seventyEightBX_37
      · exact prime_seventyEightBX_77137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14070560171) ^ 7035280085 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 14070560171) ^ 2814112034 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 14070560171) ^ 827680010 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 14070560171) ^ 485191730 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 14070560171) ^ 380285410 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 14070560171) ^ 182410 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_14543563807 : Nat.Prime 14543563807 := by
  apply lucas_primality 14543563807 (6 : ZMod 14543563807)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (9199, 1), (87833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (9199, 1), (87833, 1)] : List FactorBlock).map factorBlockValue).prod) = 14543563807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_9199
      · exact prime_seventyEightBX_87833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 14543563807) ^ 7271781903 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 14543563807) ^ 4847854602 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 14543563807) ^ 1580994 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 14543563807) ^ 165582 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_15844074371 : Nat.Prime 15844074371 := by
  apply lucas_primality 15844074371 (2 : ZMod 15844074371)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1584407437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1584407437, 1)] : List FactorBlock).map factorBlockValue).prod) = 15844074371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_1584407437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 15844074371) ^ 7922037185 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 15844074371) ^ 3168814874 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 15844074371) ^ 10 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_16148618371 : Nat.Prime 16148618371 := by
  apply lucas_primality 16148618371 (7 : ZMod 16148618371)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (997, 1), (179969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (997, 1), (179969, 1)] : List FactorBlock).map factorBlockValue).prod) = 16148618371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_997
      · exact prime_seventyEightBX_179969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 16148618371) ^ 8074309185 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 16148618371) ^ 5382872790 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 16148618371) ^ 3229723674 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 16148618371) ^ 16197210 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 16148618371) ^ 89730 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_16963103611 : Nat.Prime 16963103611 := by
  apply lucas_primality 16963103611 (2 : ZMod 16963103611)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (9677, 1), (19477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (9677, 1), (19477, 1)] : List FactorBlock).map factorBlockValue).prod) = 16963103611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_9677
      · exact prime_seventyEightBX_19477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16963103611) ^ 8481551805 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 16963103611) ^ 5654367870 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 16963103611) ^ 3392620722 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 16963103611) ^ 1752930 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 16963103611) ^ 870930 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_17883913301 : Nat.Prime 17883913301 := by
  apply lucas_primality 17883913301 (3 : ZMod 17883913301)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (11, 1), (17, 1), (271, 1), (3529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (11, 1), (17, 1), (271, 1), (3529, 1)] : List FactorBlock).map factorBlockValue).prod) = 17883913301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_11
      · exact prime_seventyEightBX_17
      · exact prime_seventyEightBX_271
      · exact prime_seventyEightBX_3529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 17883913301) ^ 8941956650 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 17883913301) ^ 3576782660 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 17883913301) ^ 1625810300 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 17883913301) ^ 1051994900 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 17883913301) ^ 65992300 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 17883913301) ^ 5067700 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_17930590291 : Nat.Prime 17930590291 := by
  apply lucas_primality 17930590291 (2 : ZMod 17930590291)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (59, 1), (3376759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (59, 1), (3376759, 1)] : List FactorBlock).map factorBlockValue).prod) = 17930590291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_59
      · exact prime_seventyEightBX_3376759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17930590291) ^ 8965295145 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 17930590291) ^ 5976863430 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 17930590291) ^ 3586118058 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 17930590291) ^ 303908310 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 17930590291) ^ 5310 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_18109991923 : Nat.Prime 18109991923 := by
  apply lucas_primality 18109991923 (2 : ZMod 18109991923)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (3593, 1), (76369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (3593, 1), (76369, 1)] : List FactorBlock).map factorBlockValue).prod) = 18109991923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_11
      · exact prime_seventyEightBX_3593
      · exact prime_seventyEightBX_76369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18109991923) ^ 9054995961 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 18109991923) ^ 6036663974 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 18109991923) ^ 1646362902 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 18109991923) ^ 5040354 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 18109991923) ^ 237138 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_18702136309 : Nat.Prime 18702136309 := by
  apply lucas_primality 18702136309 (6 : ZMod 18702136309)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (53741771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (53741771, 1)] : List FactorBlock).map factorBlockValue).prod) = 18702136309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_29
      · exact prime_seventyEightBX_53741771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 18702136309) ^ 9351068154 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 18702136309) ^ 6234045436 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 18702136309) ^ 644901252 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 18702136309) ^ 348 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_18760798487 : Nat.Prime 18760798487 := by
  apply lucas_primality 18760798487 (5 : ZMod 18760798487)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (9380399243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (9380399243, 1)] : List FactorBlock).map factorBlockValue).prod) = 18760798487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_9380399243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 18760798487) ^ 9380399243 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 18760798487) ^ 2 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_18942416089 : Nat.Prime 18942416089 := by
  apply lucas_primality 18942416089 (23 : ZMod 18942416089)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (577, 1), (1367881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (577, 1), (1367881, 1)] : List FactorBlock).map factorBlockValue).prod) = 18942416089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_577
      · exact prime_seventyEightBX_1367881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 18942416089) ^ 9471208044 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (23 : ZMod 18942416089) ^ 6314138696 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (23 : ZMod 18942416089) ^ 32829144 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (23 : ZMod 18942416089) ^ 13848 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_20570230921 : Nat.Prime 20570230921 := by
  apply lucas_primality 20570230921 (13 : ZMod 20570230921)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (1193, 1), (143687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (1193, 1), (143687, 1)] : List FactorBlock).map factorBlockValue).prod) = 20570230921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_1193
      · exact prime_seventyEightBX_143687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 20570230921) ^ 10285115460 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (13 : ZMod 20570230921) ^ 6856743640 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (13 : ZMod 20570230921) ^ 4114046184 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (13 : ZMod 20570230921) ^ 17242440 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (13 : ZMod 20570230921) ^ 143160 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_21351031529 : Nat.Prime 21351031529 := by
  apply lucas_primality 21351031529 (3 : ZMod 21351031529)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (223, 1), (11968067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (223, 1), (11968067, 1)] : List FactorBlock).map factorBlockValue).prod) = 21351031529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_223
      · exact prime_seventyEightBX_11968067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 21351031529) ^ 10675515764 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 21351031529) ^ 95744536 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 21351031529) ^ 1784 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_22156382029 : Nat.Prime 22156382029 := by
  apply lucas_primality 22156382029 (7 : ZMod 22156382029)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (79, 1), (1021, 1), (2081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (79, 1), (1021, 1), (2081, 1)] : List FactorBlock).map factorBlockValue).prod) = 22156382029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_11
      · exact prime_seventyEightBX_79
      · exact prime_seventyEightBX_1021
      · exact prime_seventyEightBX_2081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 22156382029) ^ 11078191014 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 22156382029) ^ 7385460676 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 22156382029) ^ 2014216548 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 22156382029) ^ 280460532 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 22156382029) ^ 21700668 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 22156382029) ^ 10646988 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_22784748163 : Nat.Prime 22784748163 := by
  apply lucas_primality 22784748163 (2 : ZMod 22784748163)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (521, 1), (662617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (521, 1), (662617, 1)] : List FactorBlock).map factorBlockValue).prod) = 22784748163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_11
      · exact prime_seventyEightBX_521
      · exact prime_seventyEightBX_662617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22784748163) ^ 11392374081 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 22784748163) ^ 7594916054 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 22784748163) ^ 2071340742 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 22784748163) ^ 43732722 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 22784748163) ^ 34386 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_28100941513 : Nat.Prime 28100941513 := by
  apply lucas_primality 28100941513 (11 : ZMod 28100941513)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (127, 1), (1317067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (127, 1), (1317067, 1)] : List FactorBlock).map factorBlockValue).prod) = 28100941513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_127
      · exact prime_seventyEightBX_1317067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 28100941513) ^ 14050470756 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (11 : ZMod 28100941513) ^ 9366980504 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (11 : ZMod 28100941513) ^ 4014420216 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (11 : ZMod 28100941513) ^ 221267256 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (11 : ZMod 28100941513) ^ 21336 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_28734393043 : Nat.Prime 28734393043 := by
  apply lucas_primality 28734393043 (2 : ZMod 28734393043)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1596355169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1596355169, 1)] : List FactorBlock).map factorBlockValue).prod) = 28734393043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_1596355169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 28734393043) ^ 14367196521 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 28734393043) ^ 9578131014 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 28734393043) ^ 18 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_35576210179 : Nat.Prime 35576210179 := by
  apply lucas_primality 35576210179 (2 : ZMod 35576210179)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (37, 1), (17805911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (37, 1), (17805911, 1)] : List FactorBlock).map factorBlockValue).prod) = 35576210179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_37
      · exact prime_seventyEightBX_17805911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 35576210179) ^ 17788105089 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 35576210179) ^ 11858736726 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 35576210179) ^ 961519194 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 35576210179) ^ 1998 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_36984557789 : Nat.Prime 36984557789 := by
  apply lucas_primality 36984557789 (2 : ZMod 36984557789)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (9246139447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (9246139447, 1)] : List FactorBlock).map factorBlockValue).prod) = 36984557789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_9246139447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 36984557789) ^ 18492278894 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 36984557789) ^ 4 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_37014790991 : Nat.Prime 37014790991 := by
  apply lucas_primality 37014790991 (19 : ZMod 37014790991)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (3701479099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (3701479099, 1)] : List FactorBlock).map factorBlockValue).prod) = 37014790991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_3701479099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (19 : ZMod 37014790991) ^ 18507395495 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (19 : ZMod 37014790991) ^ 7402958198 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (19 : ZMod 37014790991) ^ 10 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_39991274473 : Nat.Prime 39991274473 := by
  apply lucas_primality 39991274473 (7 : ZMod 39991274473)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (31, 1), (37, 1), (83, 1), (761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (31, 1), (37, 1), (83, 1), (761, 1)] : List FactorBlock).map factorBlockValue).prod) = 39991274473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_23
      · exact prime_seventyEightBX_31
      · exact prime_seventyEightBX_37
      · exact prime_seventyEightBX_83
      · exact prime_seventyEightBX_761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 39991274473) ^ 19995637236 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 39991274473) ^ 13330424824 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 39991274473) ^ 1738751064 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 39991274473) ^ 1290041112 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 39991274473) ^ 1080845256 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 39991274473) ^ 481822584 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 39991274473) ^ 52550952 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_40164149489 : Nat.Prime 40164149489 := by
  apply lucas_primality 40164149489 (3 : ZMod 40164149489)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (29, 1), (86560667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (29, 1), (86560667, 1)] : List FactorBlock).map factorBlockValue).prod) = 40164149489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_29
      · exact prime_seventyEightBX_86560667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 40164149489) ^ 20082074744 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 40164149489) ^ 1384970672 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 40164149489) ^ 464 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_45380784637 : Nat.Prime 45380784637 := by
  apply lucas_primality 45380784637 (2 : ZMod 45380784637)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (2389, 1), (47969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (2389, 1), (47969, 1)] : List FactorBlock).map factorBlockValue).prod) = 45380784637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_11
      · exact prime_seventyEightBX_2389
      · exact prime_seventyEightBX_47969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 45380784637) ^ 22690392318 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 45380784637) ^ 15126928212 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 45380784637) ^ 4125525876 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 45380784637) ^ 18995724 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 45380784637) ^ 946044 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_52763369723 : Nat.Prime 52763369723 := by
  apply lucas_primality 52763369723 (2 : ZMod 52763369723)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (3768812123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (3768812123, 1)] : List FactorBlock).map factorBlockValue).prod) = 52763369723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_3768812123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 52763369723) ^ 26381684861 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 52763369723) ^ 7537624246 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 52763369723) ^ 14 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_54528463391 : Nat.Prime 54528463391 := by
  apply lucas_primality 54528463391 (19 : ZMod 54528463391)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (31, 1), (173, 1), (59809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (31, 1), (173, 1), (59809, 1)] : List FactorBlock).map factorBlockValue).prod) = 54528463391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_17
      · exact prime_seventyEightBX_31
      · exact prime_seventyEightBX_173
      · exact prime_seventyEightBX_59809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 54528463391) ^ 27264231695 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (19 : ZMod 54528463391) ^ 10905692678 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (19 : ZMod 54528463391) ^ 3207556670 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (19 : ZMod 54528463391) ^ 1758982690 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (19 : ZMod 54528463391) ^ 315193430 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (19 : ZMod 54528463391) ^ 911710 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_59609403193 : Nat.Prime 59609403193 := by
  apply lucas_primality 59609403193 (5 : ZMod 59609403193)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2483725133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2483725133, 1)] : List FactorBlock).map factorBlockValue).prod) = 59609403193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_2483725133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 59609403193) ^ 29804701596 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 59609403193) ^ 19869801064 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 59609403193) ^ 24 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_68101905533 : Nat.Prime 68101905533 := by
  apply lucas_primality 68101905533 (2 : ZMod 68101905533)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7283, 1), (2337701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7283, 1), (2337701, 1)] : List FactorBlock).map factorBlockValue).prod) = 68101905533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_7283
      · exact prime_seventyEightBX_2337701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 68101905533) ^ 34050952766 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 68101905533) ^ 9350804 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 68101905533) ^ 29132 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_73719412673 : Nat.Prime 73719412673 := by
  apply lucas_primality 73719412673 (3 : ZMod 73719412673)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (19, 1), (60624517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (19, 1), (60624517, 1)] : List FactorBlock).map factorBlockValue).prod) = 73719412673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_19
      · exact prime_seventyEightBX_60624517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 73719412673) ^ 36859706336 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 73719412673) ^ 3879969088 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 73719412673) ^ 1216 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_73969115579 : Nat.Prime 73969115579 := by
  apply lucas_primality 73969115579 (2 : ZMod 73969115579)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (36984557789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (36984557789, 1)] : List FactorBlock).map factorBlockValue).prod) = 73969115579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_36984557789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 73969115579) ^ 36984557789 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 73969115579) ^ 2 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_82941768683 : Nat.Prime 82941768683 := by
  apply lucas_primality 82941768683 (2 : ZMod 82941768683)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (2377, 1), (260399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (2377, 1), (260399, 1)] : List FactorBlock).map factorBlockValue).prod) = 82941768683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_67
      · exact prime_seventyEightBX_2377
      · exact prime_seventyEightBX_260399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 82941768683) ^ 41470884341 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 82941768683) ^ 1237936846 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 82941768683) ^ 34893466 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 82941768683) ^ 318518 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_84039987347 : Nat.Prime 84039987347 := by
  apply lucas_primality 84039987347 (5 : ZMod 84039987347)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (6002856239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (6002856239, 1)] : List FactorBlock).map factorBlockValue).prod) = 84039987347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_6002856239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 84039987347) ^ 42019993673 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 84039987347) ^ 12005712478 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 84039987347) ^ 14 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_100290972241 : Nat.Prime 100290972241 := by
  apply lucas_primality 100290972241 (13 : ZMod 100290972241)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (3919, 1), (35543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (3919, 1), (35543, 1)] : List FactorBlock).map factorBlockValue).prod) = 100290972241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_3919
      · exact prime_seventyEightBX_35543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 100290972241) ^ 50145486120 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (13 : ZMod 100290972241) ^ 33430324080 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (13 : ZMod 100290972241) ^ 20058194448 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (13 : ZMod 100290972241) ^ 25590960 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (13 : ZMod 100290972241) ^ 2821680 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_102641951197 : Nat.Prime 102641951197 := by
  apply lucas_primality 102641951197 (2 : ZMod 102641951197)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7703, 1), (123379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7703, 1), (123379, 1)] : List FactorBlock).map factorBlockValue).prod) = 102641951197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_7703
      · exact prime_seventyEightBX_123379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 102641951197) ^ 51320975598 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 102641951197) ^ 34213983732 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 102641951197) ^ 13324932 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 102641951197) ^ 831924 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_115299363463 : Nat.Prime 115299363463 := by
  apply lucas_primality 115299363463 (5 : ZMod 115299363463)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (421, 1), (971171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (421, 1), (971171, 1)] : List FactorBlock).map factorBlockValue).prod) = 115299363463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_47
      · exact prime_seventyEightBX_421
      · exact prime_seventyEightBX_971171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 115299363463) ^ 57649681731 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 115299363463) ^ 38433121154 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 115299363463) ^ 2453177946 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 115299363463) ^ 273870222 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 115299363463) ^ 118722 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_128861505491 : Nat.Prime 128861505491 := by
  apply lucas_primality 128861505491 (2 : ZMod 128861505491)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (101, 1), (7549, 1), (16901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (101, 1), (7549, 1), (16901, 1)] : List FactorBlock).map factorBlockValue).prod) = 128861505491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_101
      · exact prime_seventyEightBX_7549
      · exact prime_seventyEightBX_16901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 128861505491) ^ 64430752745 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 128861505491) ^ 25772301098 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 128861505491) ^ 1275856490 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 128861505491) ^ 17070010 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 128861505491) ^ 7624490 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_153038260961 : Nat.Prime 153038260961 := by
  apply lucas_primality 153038260961 (6 : ZMod 153038260961)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (13, 2), (1693, 1), (3343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (13, 2), (1693, 1), (3343, 1)] : List FactorBlock).map factorBlockValue).prod) = 153038260961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_13
      · exact prime_seventyEightBX_1693
      · exact prime_seventyEightBX_3343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 153038260961) ^ 76519130480 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 153038260961) ^ 30607652192 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 153038260961) ^ 11772173920 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 153038260961) ^ 90394720 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 153038260961) ^ 45778720 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_177392075923 : Nat.Prime 177392075923 := by
  apply lucas_primality 177392075923 (20 : ZMod 177392075923)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11369, 1), (288947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11369, 1), (288947, 1)] : List FactorBlock).map factorBlockValue).prod) = 177392075923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_11369
      · exact prime_seventyEightBX_288947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (20 : ZMod 177392075923) ^ 88696037961 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (20 : ZMod 177392075923) ^ 59130691974 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (20 : ZMod 177392075923) ^ 15603138 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (20 : ZMod 177392075923) ^ 613926 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_206427323357 : Nat.Prime 206427323357 := by
  apply lucas_primality 206427323357 (2 : ZMod 206427323357)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (1861, 1), (956231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (1861, 1), (956231, 1)] : List FactorBlock).map factorBlockValue).prod) = 206427323357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_29
      · exact prime_seventyEightBX_1861
      · exact prime_seventyEightBX_956231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 206427323357) ^ 103213661678 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 206427323357) ^ 7118183564 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 206427323357) ^ 110922796 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 206427323357) ^ 215876 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_210907786451 : Nat.Prime 210907786451 := by
  apply lucas_primality 210907786451 (2 : ZMod 210907786451)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (2447, 1), (1723807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (2447, 1), (1723807, 1)] : List FactorBlock).map factorBlockValue).prod) = 210907786451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_2447
      · exact prime_seventyEightBX_1723807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 210907786451) ^ 105453893225 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 210907786451) ^ 42181557290 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 210907786451) ^ 86190350 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 210907786451) ^ 122350 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_233505261949 : Nat.Prime 233505261949 := by
  apply lucas_primality 233505261949 (10 : ZMod 233505261949)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (17, 1), (11621, 1), (14071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (17, 1), (11621, 1), (14071, 1)] : List FactorBlock).map factorBlockValue).prod) = 233505261949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_17
      · exact prime_seventyEightBX_11621
      · exact prime_seventyEightBX_14071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 233505261949) ^ 116752630974 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (10 : ZMod 233505261949) ^ 77835087316 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (10 : ZMod 233505261949) ^ 33357894564 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (10 : ZMod 233505261949) ^ 13735603644 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (10 : ZMod 233505261949) ^ 20093388 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (10 : ZMod 233505261949) ^ 16594788 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_288598686601 : Nat.Prime 288598686601 := by
  apply lucas_primality 288598686601 (19 : ZMod 288598686601)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (7, 1), (673, 1), (102101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (7, 1), (673, 1), (102101, 1)] : List FactorBlock).map factorBlockValue).prod) = 288598686601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_673
      · exact prime_seventyEightBX_102101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 288598686601) ^ 144299343300 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (19 : ZMod 288598686601) ^ 96199562200 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (19 : ZMod 288598686601) ^ 57719737320 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (19 : ZMod 288598686601) ^ 41228383800 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (19 : ZMod 288598686601) ^ 428824200 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (19 : ZMod 288598686601) ^ 2826600 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_298914441407 : Nat.Prime 298914441407 := by
  apply lucas_primality 298914441407 (5 : ZMod 298914441407)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (21351031529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (21351031529, 1)] : List FactorBlock).map factorBlockValue).prod) = 298914441407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_21351031529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 298914441407) ^ 149457220703 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 298914441407) ^ 42702063058 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 298914441407) ^ 14 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_321313195913 : Nat.Prime 321313195913 := by
  apply lucas_primality 321313195913 (3 : ZMod 321313195913)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (40164149489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (40164149489, 1)] : List FactorBlock).map factorBlockValue).prod) = 321313195913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_40164149489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 321313195913) ^ 160656597956 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 321313195913) ^ 8 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_337117379789 : Nat.Prime 337117379789 := by
  apply lucas_primality 337117379789 (2 : ZMod 337117379789)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (383, 1), (31435787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (383, 1), (31435787, 1)] : List FactorBlock).map factorBlockValue).prod) = 337117379789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_383
      · exact prime_seventyEightBX_31435787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 337117379789) ^ 168558689894 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 337117379789) ^ 48159625684 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 337117379789) ^ 880202036 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 337117379789) ^ 10724 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_391539565447 : Nat.Prime 391539565447 := by
  apply lucas_primality 391539565447 (5 : ZMod 391539565447)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (83, 1), (179, 1), (4392313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (83, 1), (179, 1), (4392313, 1)] : List FactorBlock).map factorBlockValue).prod) = 391539565447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_83
      · exact prime_seventyEightBX_179
      · exact prime_seventyEightBX_4392313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 391539565447) ^ 195769782723 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 391539565447) ^ 130513188482 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 391539565447) ^ 4717344162 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 391539565447) ^ 2187371874 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 391539565447) ^ 89142 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_411446998799 : Nat.Prime 411446998799 := by
  apply lucas_primality 411446998799 (7 : ZMod 411446998799)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (18702136309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (18702136309, 1)] : List FactorBlock).map factorBlockValue).prod) = 411446998799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_11
      · exact prime_seventyEightBX_18702136309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 411446998799) ^ 205723499399 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 411446998799) ^ 37404272618 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 411446998799) ^ 22 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_422897975923 : Nat.Prime 422897975923 := by
  apply lucas_primality 422897975923 (2 : ZMod 422897975923)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (239, 1), (294907933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (239, 1), (294907933, 1)] : List FactorBlock).map factorBlockValue).prod) = 422897975923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_239
      · exact prime_seventyEightBX_294907933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 422897975923) ^ 211448987961 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 422897975923) ^ 140965991974 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 422897975923) ^ 1769447598 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 422897975923) ^ 1434 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_445907170801 : Nat.Prime 445907170801 := by
  apply lucas_primality 445907170801 (37 : ZMod 445907170801)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (5, 2), (7, 1), (13, 1), (151237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (5, 2), (7, 1), (13, 1), (151237, 1)] : List FactorBlock).map factorBlockValue).prod) = 445907170801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_13
      · exact prime_seventyEightBX_151237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (37 : ZMod 445907170801) ^ 222953585400 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (37 : ZMod 445907170801) ^ 148635723600 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (37 : ZMod 445907170801) ^ 89181434160 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (37 : ZMod 445907170801) ^ 63701024400 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (37 : ZMod 445907170801) ^ 34300551600 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (37 : ZMod 445907170801) ^ 2948400 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_451631192279 : Nat.Prime 451631192279 := by
  apply lucas_primality 451631192279 (7 : ZMod 451631192279)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (31, 1), (83, 1), (373, 1), (33613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (31, 1), (83, 1), (373, 1), (33613, 1)] : List FactorBlock).map factorBlockValue).prod) = 451631192279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_31
      · exact prime_seventyEightBX_83
      · exact prime_seventyEightBX_373
      · exact prime_seventyEightBX_33613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 451631192279) ^ 225815596139 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 451631192279) ^ 64518741754 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 451631192279) ^ 14568748138 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 451631192279) ^ 5441339666 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 451631192279) ^ 1210807486 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 451631192279) ^ 13436206 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_564475576981 : Nat.Prime 564475576981 := by
  apply lucas_primality 564475576981 (2 : ZMod 564475576981)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (31, 1), (43354499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (31, 1), (43354499, 1)] : List FactorBlock).map factorBlockValue).prod) = 564475576981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_31
      · exact prime_seventyEightBX_43354499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 564475576981) ^ 282237788490 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 564475576981) ^ 188158525660 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 564475576981) ^ 112895115396 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 564475576981) ^ 80639368140 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 564475576981) ^ 18208889580 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 564475576981) ^ 13020 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_571146824419 : Nat.Prime 571146824419 := by
  apply lucas_primality 571146824419 (2 : ZMod 571146824419)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (19403, 1), (104383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (19403, 1), (104383, 1)] : List FactorBlock).map factorBlockValue).prod) = 571146824419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_47
      · exact prime_seventyEightBX_19403
      · exact prime_seventyEightBX_104383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 571146824419) ^ 285573412209 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 571146824419) ^ 190382274806 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 571146824419) ^ 12152060094 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 571146824419) ^ 29436006 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 571146824419) ^ 5471646 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_582930502081 : Nat.Prime 582930502081 := by
  apply lucas_primality 582930502081 (13 : ZMod 582930502081)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (47, 1), (12919559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (47, 1), (12919559, 1)] : List FactorBlock).map factorBlockValue).prod) = 582930502081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_47
      · exact prime_seventyEightBX_12919559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 582930502081) ^ 291465251040 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (13 : ZMod 582930502081) ^ 194310167360 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (13 : ZMod 582930502081) ^ 116586100416 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (13 : ZMod 582930502081) ^ 12402776640 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (13 : ZMod 582930502081) ^ 45120 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_769413804491 : Nat.Prime 769413804491 := by
  apply lucas_primality 769413804491 (6 : ZMod 769413804491)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (73, 1), (3931, 1), (268123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (73, 1), (3931, 1), (268123, 1)] : List FactorBlock).map factorBlockValue).prod) = 769413804491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_73
      · exact prime_seventyEightBX_3931
      · exact prime_seventyEightBX_268123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 769413804491) ^ 384706902245 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 769413804491) ^ 153882760898 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 769413804491) ^ 10539915130 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 769413804491) ^ 195729790 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 769413804491) ^ 2869630 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_784497168701 : Nat.Prime 784497168701 := by
  apply lucas_primality 784497168701 (2 : ZMod 784497168701)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 2), (101, 1), (761, 1), (2083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 2), (101, 1), (761, 1), (2083, 1)] : List FactorBlock).map factorBlockValue).prod) = 784497168701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_101
      · exact prime_seventyEightBX_761
      · exact prime_seventyEightBX_2083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 784497168701) ^ 392248584350 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 784497168701) ^ 156899433740 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 784497168701) ^ 112071024100 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 784497168701) ^ 7767298700 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 784497168701) ^ 1030876700 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 784497168701) ^ 376618900 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_843028245391 : Nat.Prime 843028245391 := by
  apply lucas_primality 843028245391 (17 : ZMod 843028245391)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (28100941513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (28100941513, 1)] : List FactorBlock).map factorBlockValue).prod) = 843028245391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_28100941513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 843028245391) ^ 421514122695 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (17 : ZMod 843028245391) ^ 281009415130 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (17 : ZMod 843028245391) ^ 168605649078 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (17 : ZMod 843028245391) ^ 30 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_870293636243 : Nat.Prime 870293636243 := by
  apply lucas_primality 870293636243 (2 : ZMod 870293636243)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (376393, 1), (1156097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (376393, 1), (1156097, 1)] : List FactorBlock).map factorBlockValue).prod) = 870293636243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_376393
      · exact prime_seventyEightBX_1156097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 870293636243) ^ 435146818121 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 870293636243) ^ 2312194 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 870293636243) ^ 752786 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_871646960851 : Nat.Prime 871646960851 := by
  apply lucas_primality 871646960851 (3 : ZMod 871646960851)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (23, 1), (3989, 1), (63337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (23, 1), (3989, 1), (63337, 1)] : List FactorBlock).map factorBlockValue).prod) = 871646960851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_23
      · exact prime_seventyEightBX_3989
      · exact prime_seventyEightBX_63337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 871646960851) ^ 435823480425 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 871646960851) ^ 290548986950 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 871646960851) ^ 174329392170 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 871646960851) ^ 37897693950 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 871646960851) ^ 218512650 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 871646960851) ^ 13762050 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_1045415271613 : Nat.Prime 1045415271613 := by
  apply lucas_primality 1045415271613 (2 : ZMod 1045415271613)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (50461, 1), (1726441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (50461, 1), (1726441, 1)] : List FactorBlock).map factorBlockValue).prod) = 1045415271613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_50461
      · exact prime_seventyEightBX_1726441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1045415271613) ^ 522707635806 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1045415271613) ^ 348471757204 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1045415271613) ^ 20717292 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1045415271613) ^ 605532 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_1084566390709 : Nat.Prime 1084566390709 := by
  apply lucas_primality 1084566390709 (6 : ZMod 1084566390709)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (353, 1), (3739, 1), (68477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (353, 1), (3739, 1), (68477, 1)] : List FactorBlock).map factorBlockValue).prod) = 1084566390709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_353
      · exact prime_seventyEightBX_3739
      · exact prime_seventyEightBX_68477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1084566390709) ^ 542283195354 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1084566390709) ^ 361522130236 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1084566390709) ^ 3072426036 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1084566390709) ^ 290068572 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1084566390709) ^ 15838404 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_1130403285971 : Nat.Prime 1130403285971 := by
  apply lucas_primality 1130403285971 (2 : ZMod 1130403285971)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (16148618371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (16148618371, 1)] : List FactorBlock).map factorBlockValue).prod) = 1130403285971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_16148618371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1130403285971) ^ 565201642985 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130403285971) ^ 226080657194 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130403285971) ^ 161486183710 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130403285971) ^ 70 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_1764864093611 : Nat.Prime 1764864093611 := by
  apply lucas_primality 1764864093611 (2 : ZMod 1764864093611)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (332749, 1), (530389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (332749, 1), (530389, 1)] : List FactorBlock).map factorBlockValue).prod) = 1764864093611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_332749
      · exact prime_seventyEightBX_530389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1764864093611) ^ 882432046805 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1764864093611) ^ 352972818722 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1764864093611) ^ 5303890 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1764864093611) ^ 3327490 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_2216323525151 : Nat.Prime 2216323525151 := by
  apply lucas_primality 2216323525151 (13 : ZMod 2216323525151)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 2), (109, 1), (8299283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 2), (109, 1), (8299283, 1)] : List FactorBlock).map factorBlockValue).prod) = 2216323525151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_109
      · exact prime_seventyEightBX_8299283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 2216323525151) ^ 1108161762575 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (13 : ZMod 2216323525151) ^ 443264705030 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (13 : ZMod 2216323525151) ^ 316617646450 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (13 : ZMod 2216323525151) ^ 20333243350 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (13 : ZMod 2216323525151) ^ 267050 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_2355120316933 : Nat.Prime 2355120316933 := by
  apply lucas_primality 2355120316933 (6 : ZMod 2355120316933)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (297023, 1), (660757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (297023, 1), (660757, 1)] : List FactorBlock).map factorBlockValue).prod) = 2355120316933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_297023
      · exact prime_seventyEightBX_660757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 2355120316933) ^ 1177560158466 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 2355120316933) ^ 785040105644 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 2355120316933) ^ 7929084 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 2355120316933) ^ 3564276 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_2555045282687 : Nat.Prime 2555045282687 := by
  apply lucas_primality 2555045282687 (5 : ZMod 2555045282687)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (241, 1), (407763371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (241, 1), (407763371, 1)] : List FactorBlock).map factorBlockValue).prod) = 2555045282687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_13
      · exact prime_seventyEightBX_241
      · exact prime_seventyEightBX_407763371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2555045282687) ^ 1277522641343 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 2555045282687) ^ 196541944822 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 2555045282687) ^ 10601847646 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 2555045282687) ^ 6266 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_3664056696721 : Nat.Prime 3664056696721 := by
  apply lucas_primality 3664056696721 (19 : ZMod 3664056696721)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (7, 3), (163, 1), (273067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (7, 3), (163, 1), (273067, 1)] : List FactorBlock).map factorBlockValue).prod) = 3664056696721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_163
      · exact prime_seventyEightBX_273067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 3664056696721) ^ 1832028348360 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (19 : ZMod 3664056696721) ^ 1221352232240 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (19 : ZMod 3664056696721) ^ 732811339344 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (19 : ZMod 3664056696721) ^ 523436670960 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (19 : ZMod 3664056696721) ^ 22478875440 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (19 : ZMod 3664056696721) ^ 13418160 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_4176372649831 : Nat.Prime 4176372649831 := by
  apply lucas_primality 4176372649831 (3 : ZMod 4176372649831)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (48673, 1), (2860157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (48673, 1), (2860157, 1)] : List FactorBlock).map factorBlockValue).prod) = 4176372649831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_48673
      · exact prime_seventyEightBX_2860157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4176372649831) ^ 2088186324915 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 4176372649831) ^ 1392124216610 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 4176372649831) ^ 835274529966 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 4176372649831) ^ 85804710 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 4176372649831) ^ 1460190 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_4781185006249 : Nat.Prime 4781185006249 := by
  apply lucas_primality 4781185006249 (29 : ZMod 4781185006249)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (27427, 1), (345881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (27427, 1), (345881, 1)] : List FactorBlock).map factorBlockValue).prod) = 4781185006249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_27427
      · exact prime_seventyEightBX_345881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 4781185006249) ^ 2390592503124 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (29 : ZMod 4781185006249) ^ 1593728335416 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (29 : ZMod 4781185006249) ^ 683026429464 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (29 : ZMod 4781185006249) ^ 174324024 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (29 : ZMod 4781185006249) ^ 13823208 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_5229881765107 : Nat.Prime 5229881765107 := by
  apply lucas_primality 5229881765107 (2 : ZMod 5229881765107)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (871646960851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (871646960851, 1)] : List FactorBlock).map factorBlockValue).prod) = 5229881765107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_871646960851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5229881765107) ^ 2614940882553 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5229881765107) ^ 1743293921702 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5229881765107) ^ 6 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_5628497536247 : Nat.Prime 5628497536247 := by
  apply lucas_primality 5628497536247 (5 : ZMod 5628497536247)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (19, 1), (11393719709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (19, 1), (11393719709, 1)] : List FactorBlock).map factorBlockValue).prod) = 5628497536247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_13
      · exact prime_seventyEightBX_19
      · exact prime_seventyEightBX_11393719709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 5628497536247) ^ 2814248768123 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 5628497536247) ^ 432961348942 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 5628497536247) ^ 296236712434 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 5628497536247) ^ 494 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_5928339216433 : Nat.Prime 5928339216433 := by
  apply lucas_primality 5928339216433 (5 : ZMod 5928339216433)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (347, 1), (355928147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (347, 1), (355928147, 1)] : List FactorBlock).map factorBlockValue).prod) = 5928339216433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_347
      · exact prime_seventyEightBX_355928147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 5928339216433) ^ 2964169608216 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 5928339216433) ^ 1976113072144 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 5928339216433) ^ 17084551056 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 5928339216433) ^ 16656 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_6062583787999 : Nat.Prime 6062583787999 := by
  apply lucas_primality 6062583787999 (3 : ZMod 6062583787999)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (67, 1), (3181, 1), (4740979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (67, 1), (3181, 1), (4740979, 1)] : List FactorBlock).map factorBlockValue).prod) = 6062583787999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_67
      · exact prime_seventyEightBX_3181
      · exact prime_seventyEightBX_4740979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6062583787999) ^ 3031291893999 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6062583787999) ^ 2020861262666 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6062583787999) ^ 90486325194 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6062583787999) ^ 1905873558 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6062583787999) ^ 1278762 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_6172893972383 : Nat.Prime 6172893972383 := by
  apply lucas_primality 6172893972383 (5 : ZMod 6172893972383)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (211801, 1), (14572391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (211801, 1), (14572391, 1)] : List FactorBlock).map factorBlockValue).prod) = 6172893972383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_211801
      · exact prime_seventyEightBX_14572391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 6172893972383) ^ 3086446986191 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 6172893972383) ^ 29144782 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 6172893972383) ^ 423602 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_6754508306851 : Nat.Prime 6754508306851 := by
  apply lucas_primality 6754508306851 (3 : ZMod 6754508306851)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (17, 1), (79, 1), (1867, 1), (17959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (17, 1), (79, 1), (1867, 1), (17959, 1)] : List FactorBlock).map factorBlockValue).prod) = 6754508306851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_17
      · exact prime_seventyEightBX_79
      · exact prime_seventyEightBX_1867
      · exact prime_seventyEightBX_17959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6754508306851) ^ 3377254153425 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6754508306851) ^ 2251502768950 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6754508306851) ^ 1350901661370 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6754508306851) ^ 397324018050 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6754508306851) ^ 85500105150 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6754508306851) ^ 3617840550 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6754508306851) ^ 376107150 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_6972132937879 : Nat.Prime 6972132937879 := by
  apply lucas_primality 6972132937879 (6 : ZMod 6972132937879)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (22784748163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (22784748163, 1)] : List FactorBlock).map factorBlockValue).prod) = 6972132937879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_17
      · exact prime_seventyEightBX_22784748163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 6972132937879) ^ 3486066468939 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 6972132937879) ^ 2324044312626 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 6972132937879) ^ 410125466934 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 6972132937879) ^ 306 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_9058121252407 : Nat.Prime 9058121252407 := by
  apply lucas_primality 9058121252407 (3 : ZMod 9058121252407)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (18233, 1), (27599899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (18233, 1), (27599899, 1)] : List FactorBlock).map factorBlockValue).prod) = 9058121252407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_18233
      · exact prime_seventyEightBX_27599899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9058121252407) ^ 4529060626203 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 9058121252407) ^ 3019373750802 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 9058121252407) ^ 496798182 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 9058121252407) ^ 328194 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_12834186024857 : Nat.Prime 12834186024857 := by
  apply lucas_primality 12834186024857 (3 : ZMod 12834186024857)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (23747, 1), (9650983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (23747, 1), (9650983, 1)] : List FactorBlock).map factorBlockValue).prod) = 12834186024857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_23747
      · exact prime_seventyEightBX_9650983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 12834186024857) ^ 6417093012428 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 12834186024857) ^ 1833455146408 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 12834186024857) ^ 540455048 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 12834186024857) ^ 1329832 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_25862615906459 : Nat.Prime 25862615906459 := by
  apply lucas_primality 25862615906459 (2 : ZMod 25862615906459)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (445907170801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (445907170801, 1)] : List FactorBlock).map factorBlockValue).prod) = 25862615906459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_29
      · exact prime_seventyEightBX_445907170801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 25862615906459) ^ 12931307953229 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 25862615906459) ^ 891814341602 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 25862615906459) ^ 58 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_27119884711471 : Nat.Prime 27119884711471 := by
  apply lucas_primality 27119884711471 (6 : ZMod 27119884711471)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (43, 1), (6983, 1), (3010621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (43, 1), (6983, 1), (3010621, 1)] : List FactorBlock).map factorBlockValue).prod) = 27119884711471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_43
      · exact prime_seventyEightBX_6983
      · exact prime_seventyEightBX_3010621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 27119884711471) ^ 13559942355735 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 27119884711471) ^ 9039961570490 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 27119884711471) ^ 5423976942294 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 27119884711471) ^ 630694993290 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 27119884711471) ^ 3883701090 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 27119884711471) ^ 9008070 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_28427556531433 : Nat.Prime 28427556531433 := by
  apply lucas_primality 28427556531433 (5 : ZMod 28427556531433)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (41, 2), (704629103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (41, 2), (704629103, 1)] : List FactorBlock).map factorBlockValue).prod) = 28427556531433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_41
      · exact prime_seventyEightBX_704629103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 28427556531433) ^ 14213778265716 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 28427556531433) ^ 9475852177144 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 28427556531433) ^ 693355037352 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 28427556531433) ^ 40344 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_45990815088367 : Nat.Prime 45990815088367 := by
  apply lucas_primality 45990815088367 (5 : ZMod 45990815088367)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (2555045282687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (2555045282687, 1)] : List FactorBlock).map factorBlockValue).prod) = 45990815088367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_2555045282687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 45990815088367) ^ 22995407544183 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 45990815088367) ^ 15330271696122 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 45990815088367) ^ 18 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_56397452316869 : Nat.Prime 56397452316869 := by
  apply lucas_primality 56397452316869 (2 : ZMod 56397452316869)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (1084566390709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (1084566390709, 1)] : List FactorBlock).map factorBlockValue).prod) = 56397452316869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_13
      · exact prime_seventyEightBX_1084566390709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 56397452316869) ^ 28198726158434 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 56397452316869) ^ 4338265562836 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 56397452316869) ^ 52 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_58734953142497 : Nat.Prime 58734953142497 := by
  apply lucas_primality 58734953142497 (3 : ZMod 58734953142497)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (199, 1), (9223453697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (199, 1), (9223453697, 1)] : List FactorBlock).map factorBlockValue).prod) = 58734953142497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_199
      · exact prime_seventyEightBX_9223453697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 58734953142497) ^ 29367476571248 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 58734953142497) ^ 295150518304 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 58734953142497) ^ 6368 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_94853427462929 : Nat.Prime 94853427462929 := by
  apply lucas_primality 94853427462929 (3 : ZMod 94853427462929)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5928339216433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5928339216433, 1)] : List FactorBlock).map factorBlockValue).prod) = 94853427462929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_5928339216433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 94853427462929) ^ 47426713731464 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 94853427462929) ^ 16 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_132561245991457 : Nat.Prime 132561245991457 := by
  apply lucas_primality 132561245991457 (7 : ZMod 132561245991457)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (179, 1), (7873, 1), (326611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (179, 1), (7873, 1), (326611, 1)] : List FactorBlock).map factorBlockValue).prod) = 132561245991457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_179
      · exact prime_seventyEightBX_7873
      · exact prime_seventyEightBX_326611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 132561245991457) ^ 66280622995728 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 132561245991457) ^ 44187081997152 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 132561245991457) ^ 740565620064 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 132561245991457) ^ 16837450272 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 132561245991457) ^ 405868896 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_156605830836269 : Nat.Prime 156605830836269 := by
  apply lucas_primality 156605830836269 (2 : ZMod 156605830836269)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (89, 1), (39991274473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (89, 1), (39991274473, 1)] : List FactorBlock).map factorBlockValue).prod) = 156605830836269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_11
      · exact prime_seventyEightBX_89
      · exact prime_seventyEightBX_39991274473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 156605830836269) ^ 78302915418134 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 156605830836269) ^ 14236893712388 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 156605830836269) ^ 1759616076812 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 156605830836269) ^ 3916 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_161024070061871 : Nat.Prime 161024070061871 := by
  apply lucas_primality 161024070061871 (7 : ZMod 161024070061871)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (83, 1), (15451, 1), (12556139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (83, 1), (15451, 1), (12556139, 1)] : List FactorBlock).map factorBlockValue).prod) = 161024070061871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_83
      · exact prime_seventyEightBX_15451
      · exact prime_seventyEightBX_12556139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 161024070061871) ^ 80512035030935 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 161024070061871) ^ 32204814012374 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 161024070061871) ^ 1940049036890 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 161024070061871) ^ 10421595370 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 161024070061871) ^ 12824330 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_180925960112327 : Nat.Prime 180925960112327 := by
  apply lucas_primality 180925960112327 (5 : ZMod 180925960112327)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (13, 1), (31, 1), (101, 1), (1021, 1), (197891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (13, 1), (31, 1), (101, 1), (1021, 1), (197891, 1)] : List FactorBlock).map factorBlockValue).prod) = 180925960112327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_11
      · exact prime_seventyEightBX_13
      · exact prime_seventyEightBX_31
      · exact prime_seventyEightBX_101
      · exact prime_seventyEightBX_1021
      · exact prime_seventyEightBX_197891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 180925960112327) ^ 90462980056163 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 180925960112327) ^ 16447814555666 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 180925960112327) ^ 13917381547102 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 180925960112327) ^ 5836321293946 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 180925960112327) ^ 1791346139726 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 180925960112327) ^ 177204662206 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 180925960112327) ^ 914270786 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_215968852178549 : Nat.Prime 215968852178549 := by
  apply lucas_primality 215968852178549 (2 : ZMod 215968852178549)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (4523, 1), (1705322417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (4523, 1), (1705322417, 1)] : List FactorBlock).map factorBlockValue).prod) = 215968852178549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_4523
      · exact prime_seventyEightBX_1705322417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 215968852178549) ^ 107984426089274 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 215968852178549) ^ 30852693168364 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 215968852178549) ^ 47749027676 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 215968852178549) ^ 126644 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_680067912833087 : Nat.Prime 680067912833087 := by
  apply lucas_primality 680067912833087 (5 : ZMod 680067912833087)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83, 1), (2081, 1), (7229, 1), (272329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83, 1), (2081, 1), (7229, 1), (272329, 1)] : List FactorBlock).map factorBlockValue).prod) = 680067912833087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_83
      · exact prime_seventyEightBX_2081
      · exact prime_seventyEightBX_7229
      · exact prime_seventyEightBX_272329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 680067912833087) ^ 340033956416543 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 680067912833087) ^ 8193589311242 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 680067912833087) ^ 326798612606 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 680067912833087) ^ 94074963734 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 680067912833087) ^ 2497229134 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_1288192560494969 : Nat.Prime 1288192560494969 := by
  apply lucas_primality 1288192560494969 (3 : ZMod 1288192560494969)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (161024070061871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (161024070061871, 1)] : List FactorBlock).map factorBlockValue).prod) = 1288192560494969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_161024070061871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1288192560494969) ^ 644096280247484 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1288192560494969) ^ 8 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_2528199120737491 : Nat.Prime 2528199120737491 := by
  apply lucas_primality 2528199120737491 (3 : ZMod 2528199120737491)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (23, 1), (3664056696721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (23, 1), (3664056696721, 1)] : List FactorBlock).map factorBlockValue).prod) = 2528199120737491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_23
      · exact prime_seventyEightBX_3664056696721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2528199120737491) ^ 1264099560368745 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2528199120737491) ^ 842733040245830 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2528199120737491) ^ 505639824147498 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2528199120737491) ^ 109921700901630 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2528199120737491) ^ 690 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_2748023789635879 : Nat.Prime 2748023789635879 := by
  apply lucas_primality 2748023789635879 (6 : ZMod 2748023789635879)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 3), (57529, 1), (3623701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 3), (57529, 1), (3623701, 1)] : List FactorBlock).map factorBlockValue).prod) = 2748023789635879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_13
      · exact prime_seventyEightBX_57529
      · exact prime_seventyEightBX_3623701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2748023789635879) ^ 1374011894817939 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 2748023789635879) ^ 916007929878626 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 2748023789635879) ^ 211386445356606 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 2748023789635879) ^ 47767626582 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 2748023789635879) ^ 758347278 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_3134628116820517 : Nat.Prime 3134628116820517 := by
  apply lucas_primality 3134628116820517 (2 : ZMod 3134628116820517)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1097, 1), (15083, 1), (15787393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1097, 1), (15083, 1), (15787393, 1)] : List FactorBlock).map factorBlockValue).prod) = 3134628116820517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_1097
      · exact prime_seventyEightBX_15083
      · exact prime_seventyEightBX_15787393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3134628116820517) ^ 1567314058410258 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3134628116820517) ^ 1044876038940172 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3134628116820517) ^ 2857454983428 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3134628116820517) ^ 207825241452 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3134628116820517) ^ 198552612 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_3581872122960559 : Nat.Prime 3581872122960559 := by
  apply lucas_primality 3581872122960559 (3 : ZMod 3581872122960559)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (28427556531433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (28427556531433, 1)] : List FactorBlock).map factorBlockValue).prod) = 3581872122960559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_28427556531433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3581872122960559) ^ 1790936061480279 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3581872122960559) ^ 1193957374320186 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3581872122960559) ^ 511696017565794 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3581872122960559) ^ 126 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_4257764608972349 : Nat.Prime 4257764608972349 := by
  apply lucas_primality 4257764608972349 (2 : ZMod 4257764608972349)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (376631, 1), (2826217577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (376631, 1), (2826217577, 1)] : List FactorBlock).map factorBlockValue).prod) = 4257764608972349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_376631
      · exact prime_seventyEightBX_2826217577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4257764608972349) ^ 2128882304486174 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4257764608972349) ^ 11304870308 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4257764608972349) ^ 1506524 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_4860101258566261 : Nat.Prime 4860101258566261 := by
  apply lucas_primality 4860101258566261 (2 : ZMod 4860101258566261)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 2), (110251, 1), (14993929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 2), (110251, 1), (14993929, 1)] : List FactorBlock).map factorBlockValue).prod) = 4860101258566261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_110251
      · exact prime_seventyEightBX_14993929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4860101258566261) ^ 2430050629283130 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4860101258566261) ^ 1620033752855420 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4860101258566261) ^ 972020251713252 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4860101258566261) ^ 694300179795180 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4860101258566261) ^ 44082151260 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4860101258566261) ^ 324137940 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_5068446393271957 : Nat.Prime 5068446393271957 := by
  apply lucas_primality 5068446393271957 (2 : ZMod 5068446393271957)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2381, 1), (177392075923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2381, 1), (177392075923, 1)] : List FactorBlock).map factorBlockValue).prod) = 5068446393271957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_2381
      · exact prime_seventyEightBX_177392075923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5068446393271957) ^ 2534223196635978 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5068446393271957) ^ 1689482131090652 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5068446393271957) ^ 2128704911076 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5068446393271957) ^ 28572 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_5108685551191757 : Nat.Prime 5108685551191757 := by
  apply lucas_primality 5108685551191757 (2 : ZMod 5108685551191757)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1301, 1), (1459, 1), (672847421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1301, 1), (1459, 1), (672847421, 1)] : List FactorBlock).map factorBlockValue).prod) = 5108685551191757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_1301
      · exact prime_seventyEightBX_1459
      · exact prime_seventyEightBX_672847421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5108685551191757) ^ 2554342775595878 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5108685551191757) ^ 3926737548956 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5108685551191757) ^ 3501497978884 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5108685551191757) ^ 7592636 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_5576570614480753 : Nat.Prime 5576570614480753 := by
  apply lucas_primality 5576570614480753 (5 : ZMod 5576570614480753)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (37, 1), (67, 1), (5207232059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (37, 1), (67, 1), (5207232059, 1)] : List FactorBlock).map factorBlockValue).prod) = 5576570614480753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_37
      · exact prime_seventyEightBX_67
      · exact prime_seventyEightBX_5207232059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5576570614480753) ^ 2788285307240376 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 5576570614480753) ^ 1858856871493584 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 5576570614480753) ^ 150718124715696 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 5576570614480753) ^ 83232397231056 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 5576570614480753) ^ 1070928 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_7073967095719697 : Nat.Prime 7073967095719697 := by
  apply lucas_primality 7073967095719697 (3 : ZMod 7073967095719697)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7417, 1), (59609403193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7417, 1), (59609403193, 1)] : List FactorBlock).map factorBlockValue).prod) = 7073967095719697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_7417
      · exact prime_seventyEightBX_59609403193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 7073967095719697) ^ 3536983547859848 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 7073967095719697) ^ 953750451088 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 7073967095719697) ^ 118672 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_8087438996026207 : Nat.Prime 8087438996026207 := by
  apply lucas_primality 8087438996026207 (5 : ZMod 8087438996026207)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (2819, 1), (59333, 1), (350381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (2819, 1), (59333, 1), (350381, 1)] : List FactorBlock).map factorBlockValue).prod) = 8087438996026207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_23
      · exact prime_seventyEightBX_2819
      · exact prime_seventyEightBX_59333
      · exact prime_seventyEightBX_350381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 8087438996026207) ^ 4043719498013103 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 8087438996026207) ^ 2695812998675402 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 8087438996026207) ^ 351627782435922 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 8087438996026207) ^ 2868903510474 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 8087438996026207) ^ 136305917382 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 8087438996026207) ^ 23081842326 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_8515529217944699 : Nat.Prime 8515529217944699 := by
  apply lucas_primality 8515529217944699 (2 : ZMod 8515529217944699)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4257764608972349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4257764608972349, 1)] : List FactorBlock).map factorBlockValue).prod) = 8515529217944699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_4257764608972349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 8515529217944699) ^ 4257764608972349 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 8515529217944699) ^ 2 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_8821648435122689 : Nat.Prime 8821648435122689 := by
  apply lucas_primality 8821648435122689 (3 : ZMod 8821648435122689)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (11, 1), (23, 1), (68101905533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (11, 1), (23, 1), (68101905533, 1)] : List FactorBlock).map factorBlockValue).prod) = 8821648435122689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_11
      · exact prime_seventyEightBX_23
      · exact prime_seventyEightBX_68101905533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8821648435122689) ^ 4410824217561344 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 8821648435122689) ^ 801968039556608 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 8821648435122689) ^ 383549931961856 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 8821648435122689) ^ 129536 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_9000190335447733 : Nat.Prime 9000190335447733 := by
  apply lucas_primality 9000190335447733 (5 : ZMod 9000190335447733)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (25862615906459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (25862615906459, 1)] : List FactorBlock).map factorBlockValue).prod) = 9000190335447733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_29
      · exact prime_seventyEightBX_25862615906459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9000190335447733) ^ 4500095167723866 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 9000190335447733) ^ 3000063445149244 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 9000190335447733) ^ 310351390877508 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 9000190335447733) ^ 348 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_11667284899887053 : Nat.Prime 11667284899887053 := by
  apply lucas_primality 11667284899887053 (2 : ZMod 11667284899887053)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (2801, 1), (22156382029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (2801, 1), (22156382029, 1)] : List FactorBlock).map factorBlockValue).prod) = 11667284899887053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_47
      · exact prime_seventyEightBX_2801
      · exact prime_seventyEightBX_22156382029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11667284899887053) ^ 5833642449943526 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 11667284899887053) ^ 248240104252916 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 11667284899887053) ^ 4165399821452 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 11667284899887053) ^ 526588 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_27075606424818997 : Nat.Prime 27075606424818997 := by
  apply lucas_primality 27075606424818997 (2 : ZMod 27075606424818997)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 2), (157, 1), (193, 1), (615395923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 2), (157, 1), (193, 1), (615395923, 1)] : List FactorBlock).map factorBlockValue).prod) = 27075606424818997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_11
      · exact prime_seventyEightBX_157
      · exact prime_seventyEightBX_193
      · exact prime_seventyEightBX_615395923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 27075606424818997) ^ 13537803212409498 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 27075606424818997) ^ 9025202141606332 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 27075606424818997) ^ 2461418765892636 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 27075606424818997) ^ 172456091877828 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 27075606424818997) ^ 140288116190772 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 27075606424818997) ^ 43997052 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_27561765092259707 : Nat.Prime 27561765092259707 := by
  apply lucas_primality 27561765092259707 (2 : ZMod 27561765092259707)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (43, 1), (8699, 1), (478463177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (43, 1), (8699, 1), (478463177, 1)] : List FactorBlock).map factorBlockValue).prod) = 27561765092259707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_11
      · exact prime_seventyEightBX_43
      · exact prime_seventyEightBX_8699
      · exact prime_seventyEightBX_478463177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 27561765092259707) ^ 13780882546129853 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 27561765092259707) ^ 3937395013179958 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 27561765092259707) ^ 2505615008387246 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 27561765092259707) ^ 640971281215342 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 27561765092259707) ^ 3168383158094 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 27561765092259707) ^ 57604778 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_40766462518462651 : Nat.Prime 40766462518462651 := by
  apply lucas_primality 40766462518462651 (2 : ZMod 40766462518462651)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (59, 1), (821, 1), (1870231403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (59, 1), (821, 1), (1870231403, 1)] : List FactorBlock).map factorBlockValue).prod) = 40766462518462651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_59
      · exact prime_seventyEightBX_821
      · exact prime_seventyEightBX_1870231403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 40766462518462651) ^ 20383231259231325 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 40766462518462651) ^ 13588820839487550 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 40766462518462651) ^ 8153292503692530 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 40766462518462651) ^ 690956991838350 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 40766462518462651) ^ 49654643749650 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 40766462518462651) ^ 21797550 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_44204858890241311 : Nat.Prime 44204858890241311 := by
  apply lucas_primality 44204858890241311 (3 : ZMod 44204858890241311)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (3008267, 1), (163271777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (3008267, 1), (163271777, 1)] : List FactorBlock).map factorBlockValue).prod) = 44204858890241311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_3008267
      · exact prime_seventyEightBX_163271777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 44204858890241311) ^ 22102429445120655 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 44204858890241311) ^ 14734952963413770 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 44204858890241311) ^ 8840971778048262 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 44204858890241311) ^ 14694459930 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 44204858890241311) ^ 270744030 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_58565780035271933 : Nat.Prime 58565780035271933 := by
  apply lucas_primality 58565780035271933 (2 : ZMod 58565780035271933)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (54767, 1), (14070560171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (54767, 1), (14070560171, 1)] : List FactorBlock).map factorBlockValue).prod) = 58565780035271933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_19
      · exact prime_seventyEightBX_54767
      · exact prime_seventyEightBX_14070560171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 58565780035271933) ^ 29282890017635966 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 58565780035271933) ^ 3082409475540628 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 58565780035271933) ^ 1069362572996 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 58565780035271933) ^ 4162292 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_62966941313719351 : Nat.Prime 62966941313719351 := by
  apply lucas_primality 62966941313719351 (3 : ZMod 62966941313719351)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (47, 1), (157, 1), (331, 1), (877, 1), (195973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (47, 1), (157, 1), (331, 1), (877, 1), (195973, 1)] : List FactorBlock).map factorBlockValue).prod) = 62966941313719351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_47
      · exact prime_seventyEightBX_157
      · exact prime_seventyEightBX_331
      · exact prime_seventyEightBX_877
      · exact prime_seventyEightBX_195973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 62966941313719351) ^ 31483470656859675 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 62966941313719351) ^ 20988980437906450 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 62966941313719351) ^ 12593388262743870 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 62966941313719351) ^ 1339722155611050 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 62966941313719351) ^ 401063320469550 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 62966941313719351) ^ 190232451098850 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 62966941313719351) ^ 71798108681550 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 62966941313719351) ^ 321304165950 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_125105450193518611 : Nat.Prime 125105450193518611 := by
  apply lucas_primality 125105450193518611 (2 : ZMod 125105450193518611)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (71, 1), (58734953142497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (71, 1), (58734953142497, 1)] : List FactorBlock).map factorBlockValue).prod) = 125105450193518611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_71
      · exact prime_seventyEightBX_58734953142497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 125105450193518611) ^ 62552725096759305 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 125105450193518611) ^ 41701816731172870 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 125105450193518611) ^ 25021090038703722 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 125105450193518611) ^ 1762048594274910 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 125105450193518611) ^ 2130 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_171348849023448209 : Nat.Prime 171348849023448209 := by
  apply lucas_primality 171348849023448209 (3 : ZMod 171348849023448209)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (257, 1), (2741, 1), (20947, 1), (103681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (257, 1), (2741, 1), (20947, 1), (103681, 1)] : List FactorBlock).map factorBlockValue).prod) = 171348849023448209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_257
      · exact prime_seventyEightBX_2741
      · exact prime_seventyEightBX_20947
      · exact prime_seventyEightBX_103681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 171348849023448209) ^ 85674424511724104 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 171348849023448209) ^ 24478407003349744 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 171348849023448209) ^ 666727039001744 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 171348849023448209) ^ 62513261227088 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 171348849023448209) ^ 8180114050864 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 171348849023448209) ^ 1652654285968 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_194098535904628969 : Nat.Prime 194098535904628969 := by
  apply lucas_primality 194098535904628969 (7 : ZMod 194098535904628969)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (8087438996026207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (8087438996026207, 1)] : List FactorBlock).map factorBlockValue).prod) = 194098535904628969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_8087438996026207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 194098535904628969) ^ 97049267952314484 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 194098535904628969) ^ 64699511968209656 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 194098535904628969) ^ 24 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_244598775110775907 : Nat.Prime 244598775110775907 := by
  apply lucas_primality 244598775110775907 (2 : ZMod 244598775110775907)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (40766462518462651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (40766462518462651, 1)] : List FactorBlock).map factorBlockValue).prod) = 244598775110775907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_40766462518462651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 244598775110775907) ^ 122299387555387953 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 244598775110775907) ^ 81532925036925302 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 244598775110775907) ^ 6 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_277956506185891073 : Nat.Prime 277956506185891073 := by
  apply lucas_primality 277956506185891073 (3 : ZMod 277956506185891073)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (2029, 1), (379163, 1), (1411331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (2029, 1), (379163, 1), (1411331, 1)] : List FactorBlock).map factorBlockValue).prod) = 277956506185891073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_2029
      · exact prime_seventyEightBX_379163
      · exact prime_seventyEightBX_1411331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 277956506185891073) ^ 138978253092945536 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 277956506185891073) ^ 136991870963968 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 277956506185891073) ^ 733079193344 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 277956506185891073) ^ 196946362112 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_300653068793725897 : Nat.Prime 300653068793725897 := by
  apply lucas_primality 300653068793725897 (5 : ZMod 300653068793725897)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (521, 1), (1045415271613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (521, 1), (1045415271613, 1)] : List FactorBlock).map factorBlockValue).prod) = 300653068793725897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_23
      · exact prime_seventyEightBX_521
      · exact prime_seventyEightBX_1045415271613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 300653068793725897) ^ 150326534396862948 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 300653068793725897) ^ 100217689597908632 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 300653068793725897) ^ 13071872556248952 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 300653068793725897) ^ 577069229930376 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 300653068793725897) ^ 287592 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_319533044471244697 : Nat.Prime 319533044471244697 := by
  apply lucas_primality 319533044471244697 (5 : ZMod 319533044471244697)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (29, 1), (59, 1), (56149, 1), (138583811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (29, 1), (59, 1), (56149, 1), (138583811, 1)] : List FactorBlock).map factorBlockValue).prod) = 319533044471244697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_29
      · exact prime_seventyEightBX_59
      · exact prime_seventyEightBX_56149
      · exact prime_seventyEightBX_138583811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 319533044471244697) ^ 159766522235622348 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 319533044471244697) ^ 106511014823748232 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 319533044471244697) ^ 11018380843836024 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 319533044471244697) ^ 5415814313071944 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 319533044471244697) ^ 5690805614904 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 319533044471244697) ^ 2305702536 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_443376867845076029 : Nat.Prime 443376867845076029 := by
  apply lucas_primality 443376867845076029 (2 : ZMod 443376867845076029)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (65704567, 1), (1687009321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (65704567, 1), (1687009321, 1)] : List FactorBlock).map factorBlockValue).prod) = 443376867845076029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_65704567
      · exact prime_seventyEightBX_1687009321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 443376867845076029) ^ 221688433922538014 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 443376867845076029) ^ 6748037284 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 443376867845076029) ^ 262818268 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_515200533943905827 : Nat.Prime 515200533943905827 := by
  apply lucas_primality 515200533943905827 (2 : ZMod 515200533943905827)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (101, 1), (163, 1), (422897975923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (101, 1), (163, 1), (422897975923, 1)] : List FactorBlock).map factorBlockValue).prod) = 515200533943905827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_37
      · exact prime_seventyEightBX_101
      · exact prime_seventyEightBX_163
      · exact prime_seventyEightBX_422897975923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 515200533943905827) ^ 257600266971952913 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 515200533943905827) ^ 13924338755240698 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 515200533943905827) ^ 5100995385583226 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 515200533943905827) ^ 3160739472048502 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 515200533943905827) ^ 1218262 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_555913012371782147 : Nat.Prime 555913012371782147 := by
  apply lucas_primality 555913012371782147 (2 : ZMod 555913012371782147)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (277956506185891073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (277956506185891073, 1)] : List FactorBlock).map factorBlockValue).prod) = 555913012371782147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_277956506185891073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 555913012371782147) ^ 277956506185891073 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 555913012371782147) ^ 2 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_555964578749761261 : Nat.Prime 555964578749761261 := by
  apply lucas_primality 555964578749761261 (2 : ZMod 555964578749761261)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (109, 1), (1559, 1), (54528463391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (109, 1), (1559, 1), (54528463391, 1)] : List FactorBlock).map factorBlockValue).prod) = 555964578749761261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_109
      · exact prime_seventyEightBX_1559
      · exact prime_seventyEightBX_54528463391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 555964578749761261) ^ 277982289374880630 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 555964578749761261) ^ 185321526249920420 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 555964578749761261) ^ 111192915749952252 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 555964578749761261) ^ 5100592465594140 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 555964578749761261) ^ 356616150577140 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 555964578749761261) ^ 10195860 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_583040829728616163 : Nat.Prime 583040829728616163 := by
  apply lucas_primality 583040829728616163 (3 : ZMod 583040829728616163)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (3134628116820517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (3134628116820517, 1)] : List FactorBlock).map factorBlockValue).prod) = 583040829728616163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_31
      · exact prime_seventyEightBX_3134628116820517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 583040829728616163) ^ 291520414864308081 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 583040829728616163) ^ 194346943242872054 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 583040829728616163) ^ 18807768700923102 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 583040829728616163) ^ 186 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_755466135498253247 : Nat.Prime 755466135498253247 := by
  apply lucas_primality 755466135498253247 (5 : ZMod 755466135498253247)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1123, 1), (15680471, 1), (21450931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1123, 1), (15680471, 1), (21450931, 1)] : List FactorBlock).map factorBlockValue).prod) = 755466135498253247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_1123
      · exact prime_seventyEightBX_15680471
      · exact prime_seventyEightBX_21450931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 755466135498253247) ^ 377733067749126623 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 755466135498253247) ^ 672721402937002 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 755466135498253247) ^ 48178791026 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 755466135498253247) ^ 35218337866 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_919978222885966903 : Nat.Prime 919978222885966903 := by
  apply lucas_primality 919978222885966903 (7 : ZMod 919978222885966903)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (167, 1), (2239, 1), (8368731841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (167, 1), (2239, 1), (8368731841, 1)] : List FactorBlock).map factorBlockValue).prod) = 919978222885966903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_167
      · exact prime_seventyEightBX_2239
      · exact prime_seventyEightBX_8368731841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 919978222885966903) ^ 459989111442983451 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 919978222885966903) ^ 306659407628655634 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 919978222885966903) ^ 131425460412280986 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 919978222885966903) ^ 5508851634047706 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 919978222885966903) ^ 410887995929418 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 919978222885966903) ^ 109930422 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_1373648109517237423 : Nat.Prime 1373648109517237423 := by
  apply lucas_primality 1373648109517237423 (5 : ZMod 1373648109517237423)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (3433, 1), (6062583787999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (3433, 1), (6062583787999, 1)] : List FactorBlock).map factorBlockValue).prod) = 1373648109517237423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_11
      · exact prime_seventyEightBX_3433
      · exact prime_seventyEightBX_6062583787999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1373648109517237423) ^ 686824054758618711 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1373648109517237423) ^ 457882703172412474 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1373648109517237423) ^ 124877100865203402 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1373648109517237423) ^ 400130530007934 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1373648109517237423) ^ 226578 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_1562158492327693999 : Nat.Prime 1562158492327693999 := by
  apply lucas_primality 1562158492327693999 (3 : ZMod 1562158492327693999)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (41, 1), (59, 1), (211, 1), (26177, 1), (6495527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (41, 1), (59, 1), (211, 1), (26177, 1), (6495527, 1)] : List FactorBlock).map factorBlockValue).prod) = 1562158492327693999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_41
      · exact prime_seventyEightBX_59
      · exact prime_seventyEightBX_211
      · exact prime_seventyEightBX_26177
      · exact prime_seventyEightBX_6495527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1562158492327693999) ^ 781079246163846999 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1562158492327693999) ^ 520719497442564666 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1562158492327693999) ^ 38101426642138878 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1562158492327693999) ^ 26477262581825322 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1562158492327693999) ^ 7403594750368218 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1562158492327693999) ^ 59676757929774 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1562158492327693999) ^ 240497575074 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_1988556542649278027 : Nat.Prime 1988556542649278027 := by
  apply lucas_primality 1988556542649278027 (2 : ZMod 1988556542649278027)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (113, 1), (223, 1), (2083, 1), (18942416089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (113, 1), (223, 1), (2083, 1), (18942416089, 1)] : List FactorBlock).map factorBlockValue).prod) = 1988556542649278027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_113
      · exact prime_seventyEightBX_223
      · exact prime_seventyEightBX_2083
      · exact prime_seventyEightBX_18942416089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1988556542649278027) ^ 994278271324639013 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1988556542649278027) ^ 17597845510170602 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1988556542649278027) ^ 8917293913225462 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1988556542649278027) ^ 954659886053422 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1988556542649278027) ^ 104979034 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_2311235746855496141 : Nat.Prime 2311235746855496141 := by
  apply lucas_primality 2311235746855496141 (2 : ZMod 2311235746855496141)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (569, 1), (17117, 1), (624483161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (569, 1), (17117, 1), (624483161, 1)] : List FactorBlock).map factorBlockValue).prod) = 2311235746855496141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_19
      · exact prime_seventyEightBX_569
      · exact prime_seventyEightBX_17117
      · exact prime_seventyEightBX_624483161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2311235746855496141) ^ 1155617873427748070 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2311235746855496141) ^ 462247149371099228 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2311235746855496141) ^ 121643986676605060 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2311235746855496141) ^ 4061925741398060 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2311235746855496141) ^ 135025749071420 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2311235746855496141) ^ 3701037740 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_2332163318914464653 : Nat.Prime 2332163318914464653 := by
  apply lucas_primality 2332163318914464653 (2 : ZMod 2332163318914464653)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (583040829728616163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (583040829728616163, 1)] : List FactorBlock).map factorBlockValue).prod) = 2332163318914464653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_583040829728616163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 2332163318914464653) ^ 1166081659457232326 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2332163318914464653) ^ 4 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_2970212297131708549 : Nat.Prime 2970212297131708549 := by
  apply lucas_primality 2970212297131708549 (2 : ZMod 2970212297131708549)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (131, 1), (271, 1), (6972132937879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (131, 1), (271, 1), (6972132937879, 1)] : List FactorBlock).map factorBlockValue).prod) = 2970212297131708549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_131
      · exact prime_seventyEightBX_271
      · exact prime_seventyEightBX_6972132937879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2970212297131708549) ^ 1485106148565854274 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2970212297131708549) ^ 990070765710569516 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2970212297131708549) ^ 22673376313982508 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2970212297131708549) ^ 10960192978345788 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2970212297131708549) ^ 426012 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_8131413307309851379 : Nat.Prime 8131413307309851379 := by
  apply lucas_primality 8131413307309851379 (2 : ZMod 8131413307309851379)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (10516993, 1), (128861505491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (10516993, 1), (128861505491, 1)] : List FactorBlock).map factorBlockValue).prod) = 8131413307309851379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_10516993
      · exact prime_seventyEightBX_128861505491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8131413307309851379) ^ 4065706653654925689 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 8131413307309851379) ^ 2710471102436617126 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 8131413307309851379) ^ 773169032946 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 8131413307309851379) ^ 63101958 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_17749710372792891533 : Nat.Prime 17749710372792891533 := by
  apply lucas_primality 17749710372792891533 (2 : ZMod 17749710372792891533)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (691, 1), (2393, 1), (206427323357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (691, 1), (2393, 1), (206427323357, 1)] : List FactorBlock).map factorBlockValue).prod) = 17749710372792891533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_13
      · exact prime_seventyEightBX_691
      · exact prime_seventyEightBX_2393
      · exact prime_seventyEightBX_206427323357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17749710372792891533) ^ 8874855186396445766 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 17749710372792891533) ^ 1365362336368683964 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 17749710372792891533) ^ 25686990409251652 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 17749710372792891533) ^ 7417346582863724 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 17749710372792891533) ^ 85985276 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_19602739051568953829 : Nat.Prime 19602739051568953829 := by
  apply lucas_primality 19602739051568953829 (2 : ZMod 19602739051568953829)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (181, 1), (27075606424818997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (181, 1), (27075606424818997, 1)] : List FactorBlock).map factorBlockValue).prod) = 19602739051568953829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_181
      · exact prime_seventyEightBX_27075606424818997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 19602739051568953829) ^ 9801369525784476914 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 19602739051568953829) ^ 108302425699275988 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 19602739051568953829) ^ 724 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_32525653229239405517 : Nat.Prime 32525653229239405517 := by
  apply lucas_primality 32525653229239405517 (2 : ZMod 32525653229239405517)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (8131413307309851379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (8131413307309851379, 1)] : List FactorBlock).map factorBlockValue).prod) = 32525653229239405517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_8131413307309851379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 32525653229239405517) ^ 16262826614619702758 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 32525653229239405517) ^ 4 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_37131288166716682987 : Nat.Prime 37131288166716682987 := by
  apply lucas_primality 37131288166716682987 (2 : ZMod 37131288166716682987)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (953, 1), (105229, 1), (20570230921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (953, 1), (105229, 1), (20570230921, 1)] : List FactorBlock).map factorBlockValue).prod) = 37131288166716682987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_953
      · exact prime_seventyEightBX_105229
      · exact prime_seventyEightBX_20570230921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 37131288166716682987) ^ 18565644083358341493 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 37131288166716682987) ^ 12377096055572227662 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 37131288166716682987) ^ 38962526932546362 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 37131288166716682987) ^ 352861741218834 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 37131288166716682987) ^ 1805098266 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_66024755418215990503 : Nat.Prime 66024755418215990503 := by
  apply lucas_primality 66024755418215990503 (5 : ZMod 66024755418215990503)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (137, 1), (179, 1), (5392307, 1), (9246233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (137, 1), (179, 1), (5392307, 1), (9246233, 1)] : List FactorBlock).map factorBlockValue).prod) = 66024755418215990503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_137
      · exact prime_seventyEightBX_179
      · exact prime_seventyEightBX_5392307
      · exact prime_seventyEightBX_9246233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 66024755418215990503) ^ 33012377709107995251 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 66024755418215990503) ^ 22008251806071996834 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 66024755418215990503) ^ 481932521300846646 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 66024755418215990503) ^ 368853382224670338 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 66024755418215990503) ^ 12244250080386 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 66024755418215990503) ^ 7140719406294 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_174550479305945289229 : Nat.Prime 174550479305945289229 := by
  apply lucas_primality 174550479305945289229 (10 : ZMod 174550479305945289229)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (11, 1), (43, 1), (47156413, 1), (72459509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (11, 1), (43, 1), (47156413, 1), (72459509, 1)] : List FactorBlock).map factorBlockValue).prod) = 174550479305945289229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_11
      · exact prime_seventyEightBX_43
      · exact prime_seventyEightBX_47156413
      · exact prime_seventyEightBX_72459509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 174550479305945289229) ^ 87275239652972644614 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (10 : ZMod 174550479305945289229) ^ 58183493101981763076 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (10 : ZMod 174550479305945289229) ^ 15868225391449571748 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (10 : ZMod 174550479305945289229) ^ 4059313472231285796 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (10 : ZMod 174550479305945289229) ^ 3701521557756 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (10 : ZMod 174550479305945289229) ^ 2408938201692 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_175730719077382688123 : Nat.Prime 175730719077382688123 := by
  apply lucas_primality 175730719077382688123 (2 : ZMod 175730719077382688123)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (42181, 1), (1517557, 1), (1372637333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (42181, 1), (1517557, 1), (1372637333, 1)] : List FactorBlock).map factorBlockValue).prod) = 175730719077382688123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_42181
      · exact prime_seventyEightBX_1517557
      · exact prime_seventyEightBX_1372637333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 175730719077382688123) ^ 87865359538691344061 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 175730719077382688123) ^ 4166110786310962 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 175730719077382688123) ^ 115798430686546 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 175730719077382688123) ^ 128024143634 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_332405099619231428681 : Nat.Prime 332405099619231428681 := by
  apply lucas_primality 332405099619231428681 (3 : ZMod 332405099619231428681)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 1), (755466135498253247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 1), (755466135498253247, 1)] : List FactorBlock).map factorBlockValue).prod) = 332405099619231428681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_11
      · exact prime_seventyEightBX_755466135498253247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 332405099619231428681) ^ 166202549809615714340 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 332405099619231428681) ^ 66481019923846285736 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 332405099619231428681) ^ 30218645419930129880 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 332405099619231428681) ^ 440 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_346053590743723896119 : Nat.Prime 346053590743723896119 := by
  apply lucas_primality 346053590743723896119 (7 : ZMod 346053590743723896119)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2347099483, 1), (73719412673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2347099483, 1), (73719412673, 1)] : List FactorBlock).map factorBlockValue).prod) = 346053590743723896119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_2347099483
      · exact prime_seventyEightBX_73719412673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 346053590743723896119) ^ 173026795371861948059 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 346053590743723896119) ^ 147438825346 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 346053590743723896119) ^ 4694198966 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_393314830378127658457 : Nat.Prime 393314830378127658457 := by
  apply lucas_primality 393314830378127658457 (5 : ZMod 393314830378127658457)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (67, 1), (244598775110775907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (67, 1), (244598775110775907, 1)] : List FactorBlock).map factorBlockValue).prod) = 393314830378127658457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_67
      · exact prime_seventyEightBX_244598775110775907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 393314830378127658457) ^ 196657415189063829228 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 393314830378127658457) ^ 131104943459375886152 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 393314830378127658457) ^ 5870370602658621768 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 393314830378127658457) ^ 1608 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_730486705031772310207 : Nat.Prime 730486705031772310207 := by
  apply lucas_primality 730486705031772310207 (3 : ZMod 730486705031772310207)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (13, 1), (96402503, 1), (3598037117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (13, 1), (96402503, 1), (3598037117, 1)] : List FactorBlock).map factorBlockValue).prod) = 730486705031772310207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_13
      · exact prime_seventyEightBX_96402503
      · exact prime_seventyEightBX_3598037117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 730486705031772310207) ^ 365243352515886155103 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 730486705031772310207) ^ 243495568343924103402 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 730486705031772310207) ^ 56191285002444023862 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 730486705031772310207) ^ 7577466168402 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 730486705031772310207) ^ 203023671318 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_977853296795507446351 : Nat.Prime 977853296795507446351 := by
  apply lucas_primality 977853296795507446351 (6 : ZMod 977853296795507446351)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (11183189, 1), (582930502081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (11183189, 1), (582930502081, 1)] : List FactorBlock).map factorBlockValue).prod) = 977853296795507446351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_11183189
      · exact prime_seventyEightBX_582930502081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 977853296795507446351) ^ 488926648397753723175 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 977853296795507446351) ^ 325951098931835815450 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 977853296795507446351) ^ 195570659359101489270 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 977853296795507446351) ^ 87439575312150 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 977853296795507446351) ^ 1677478350 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_1036837480313182770601 : Nat.Prime 1036837480313182770601 := by
  apply lucas_primality 1036837480313182770601 (13 : ZMod 1036837480313182770601)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (7, 1), (37, 1), (2833, 1), (2355120316933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (7, 1), (37, 1), (2833, 1), (2355120316933, 1)] : List FactorBlock).map factorBlockValue).prod) = 1036837480313182770601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_37
      · exact prime_seventyEightBX_2833
      · exact prime_seventyEightBX_2355120316933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 1036837480313182770601) ^ 518418740156591385300 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (13 : ZMod 1036837480313182770601) ^ 345612493437727590200 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (13 : ZMod 1036837480313182770601) ^ 207367496062636554120 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (13 : ZMod 1036837480313182770601) ^ 148119640044740395800 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (13 : ZMod 1036837480313182770601) ^ 28022634603058993800 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (13 : ZMod 1036837480313182770601) ^ 365985697251388200 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (13 : ZMod 1036837480313182770601) ^ 440248200 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_1057052654823097519991 : Nat.Prime 1057052654823097519991 := by
  apply lucas_primality 1057052654823097519991 (17 : ZMod 1057052654823097519991)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (61339, 1), (132561245991457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (61339, 1), (132561245991457, 1)] : List FactorBlock).map factorBlockValue).prod) = 1057052654823097519991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_13
      · exact prime_seventyEightBX_61339
      · exact prime_seventyEightBX_132561245991457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 1057052654823097519991) ^ 528526327411548759995 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (17 : ZMod 1057052654823097519991) ^ 211410530964619503998 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (17 : ZMod 1057052654823097519991) ^ 81311742678699809230 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (17 : ZMod 1057052654823097519991) ^ 17232961978889410 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (17 : ZMod 1057052654823097519991) ^ 7974070 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_1133228957975860628941 : Nat.Prime 1133228957975860628941 := by
  apply lucas_primality 1133228957975860628941 (2 : ZMod 1133228957975860628941)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (2141, 1), (8821648435122689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (2141, 1), (8821648435122689, 1)] : List FactorBlock).map factorBlockValue).prod) = 1133228957975860628941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_2141
      · exact prime_seventyEightBX_8821648435122689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1133228957975860628941) ^ 566614478987930314470 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1133228957975860628941) ^ 377742985991953542980 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1133228957975860628941) ^ 226645791595172125788 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1133228957975860628941) ^ 529298906107361340 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1133228957975860628941) ^ 128460 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_1573259321512510633829 : Nat.Prime 1573259321512510633829 := by
  apply lucas_primality 1573259321512510633829 (2 : ZMod 1573259321512510633829)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (393314830378127658457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (393314830378127658457, 1)] : List FactorBlock).map factorBlockValue).prod) = 1573259321512510633829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_393314830378127658457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1573259321512510633829) ^ 786629660756255316914 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1573259321512510633829) ^ 4 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_1925983558692608096183 : Nat.Prime 1925983558692608096183 := by
  apply lucas_primality 1925983558692608096183 (5 : ZMod 1925983558692608096183)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3203, 1), (300653068793725897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3203, 1), (300653068793725897, 1)] : List FactorBlock).map factorBlockValue).prod) = 1925983558692608096183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3203
      · exact prime_seventyEightBX_300653068793725897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1925983558692608096183) ^ 962991779346304048091 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1925983558692608096183) ^ 601306137587451794 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1925983558692608096183) ^ 6406 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_2154500920157382217331 : Nat.Prime 2154500920157382217331 := by
  apply lucas_primality 2154500920157382217331 (6 : ZMod 2154500920157382217331)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (13, 2), (83, 1), (2797, 1), (784497168701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (13, 2), (83, 1), (2797, 1), (784497168701, 1)] : List FactorBlock).map factorBlockValue).prod) = 2154500920157382217331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_13
      · exact prime_seventyEightBX_83
      · exact prime_seventyEightBX_2797
      · exact prime_seventyEightBX_784497168701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2154500920157382217331) ^ 1077250460078691108665 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 2154500920157382217331) ^ 430900184031476443466 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 2154500920157382217331) ^ 307785845736768888190 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 2154500920157382217331) ^ 165730840012106324410 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 2154500920157382217331) ^ 25957842411534725510 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 2154500920157382217331) ^ 770289924975824890 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 2154500920157382217331) ^ 2746346330 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_2173119189262831037801 : Nat.Prime 2173119189262831037801 := by
  apply lucas_primality 2173119189262831037801 (3 : ZMod 2173119189262831037801)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (11, 2), (13, 2), (43, 1), (1800637, 1), (6862571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (11, 2), (13, 2), (43, 1), (1800637, 1), (6862571, 1)] : List FactorBlock).map factorBlockValue).prod) = 2173119189262831037801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_11
      · exact prime_seventyEightBX_13
      · exact prime_seventyEightBX_43
      · exact prime_seventyEightBX_1800637
      · exact prime_seventyEightBX_6862571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2173119189262831037801) ^ 1086559594631415518900 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2173119189262831037801) ^ 434623837852566207560 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2173119189262831037801) ^ 197556289932984639800 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2173119189262831037801) ^ 167163014558679310600 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2173119189262831037801) ^ 50537655564251884600 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2173119189262831037801) ^ 1206861343659400 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2173119189262831037801) ^ 316662543711800 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_27607725927435501631279 : Nat.Prime 27607725927435501631279 := by
  apply lucas_primality 27607725927435501631279 (3 : ZMod 27607725927435501631279)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (643, 1), (12569, 1), (67433, 1), (85282517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (643, 1), (12569, 1), (67433, 1), (85282517, 1)] : List FactorBlock).map factorBlockValue).prod) = 27607725927435501631279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_11
      · exact prime_seventyEightBX_643
      · exact prime_seventyEightBX_12569
      · exact prime_seventyEightBX_67433
      · exact prime_seventyEightBX_85282517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 27607725927435501631279) ^ 13803862963717750815639 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 27607725927435501631279) ^ 9202575309145167210426 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 27607725927435501631279) ^ 2509793266130500148298 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 27607725927435501631279) ^ 42935810151532661946 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 27607725927435501631279) ^ 2196493430458708062 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 27607725927435501631279) ^ 409409724132627966 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 27607725927435501631279) ^ 323720815222134 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_49589838281654484274169 : Nat.Prime 49589838281654484274169 := by
  apply lucas_primality 49589838281654484274169 (3 : ZMod 49589838281654484274169)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (463, 1), (547, 1), (1288192560494969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (463, 1), (547, 1), (1288192560494969, 1)] : List FactorBlock).map factorBlockValue).prod) = 49589838281654484274169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_19
      · exact prime_seventyEightBX_463
      · exact prime_seventyEightBX_547
      · exact prime_seventyEightBX_1288192560494969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 49589838281654484274169) ^ 24794919140827242137084 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 49589838281654484274169) ^ 2609991488508130751272 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 49589838281654484274169) ^ 107105482249793702536 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 49589838281654484274169) ^ 90657839637393938344 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 49589838281654484274169) ^ 38495672 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_187013674574469671722861 : Nat.Prime 187013674574469671722861 := by
  apply lucas_primality 187013674574469671722861 (2 : ZMod 187013674574469671722861)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (15844074371, 1), (17883913301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (15844074371, 1), (17883913301, 1)] : List FactorBlock).map factorBlockValue).prod) = 187013674574469671722861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_11
      · exact prime_seventyEightBX_15844074371
      · exact prime_seventyEightBX_17883913301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 187013674574469671722861) ^ 93506837287234835861430 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 187013674574469671722861) ^ 62337891524823223907620 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 187013674574469671722861) ^ 37402734914893934344572 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 187013674574469671722861) ^ 17001243143133606520260 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 187013674574469671722861) ^ 11803382778660 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 187013674574469671722861) ^ 10457089084860 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_215256666511097338180517 : Nat.Prime 215256666511097338180517 := by
  apply lucas_primality 215256666511097338180517 (3 : ZMod 215256666511097338180517)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (103, 1), (2129, 1), (5231, 1), (396259, 1), (118391323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (103, 1), (2129, 1), (5231, 1), (396259, 1), (118391323, 1)] : List FactorBlock).map factorBlockValue).prod) = 215256666511097338180517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_103
      · exact prime_seventyEightBX_2129
      · exact prime_seventyEightBX_5231
      · exact prime_seventyEightBX_396259
      · exact prime_seventyEightBX_118391323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 215256666511097338180517) ^ 107628333255548669090258 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 215256666511097338180517) ^ 2089870548651430467772 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 215256666511097338180517) ^ 101106935890604668004 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 215256666511097338180517) ^ 41150194324430766236 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 215256666511097338180517) ^ 543222151449171724 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 215256666511097338180517) ^ 1818179415995692 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_271503824385018030413147 : Nat.Prime 271503824385018030413147 := by
  apply lucas_primality 271503824385018030413147 (2 : ZMod 271503824385018030413147)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (37, 1), (47, 1), (401, 1), (2528199120737491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (37, 1), (47, 1), (401, 1), (2528199120737491, 1)] : List FactorBlock).map factorBlockValue).prod) = 271503824385018030413147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_11
      · exact prime_seventyEightBX_37
      · exact prime_seventyEightBX_47
      · exact prime_seventyEightBX_401
      · exact prime_seventyEightBX_2528199120737491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 271503824385018030413147) ^ 135751912192509015206573 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 271503824385018030413147) ^ 38786260626431147201878 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 271503824385018030413147) ^ 24682165853183457310286 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 271503824385018030413147) ^ 7337941199595081903058 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 271503824385018030413147) ^ 5776677114574851710918 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 271503824385018030413147) ^ 677066893728224514746 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 271503824385018030413147) ^ 107390206 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_508213239571790734051717 : Nat.Prime 508213239571790734051717 := by
  apply lucas_primality 508213239571790734051717 (5 : ZMod 508213239571790734051717)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (241, 1), (175730719077382688123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (241, 1), (175730719077382688123, 1)] : List FactorBlock).map factorBlockValue).prod) = 508213239571790734051717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_241
      · exact prime_seventyEightBX_175730719077382688123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 508213239571790734051717) ^ 254106619785895367025858 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 508213239571790734051717) ^ 169404413190596911350572 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 508213239571790734051717) ^ 2108768628928592257476 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (5 : ZMod 508213239571790734051717) ^ 2892 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_510859699633932980261179 : Nat.Prime 510859699633932980261179 := by
  apply lucas_primality 510859699633932980261179 (2 : ZMod 510859699633932980261179)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (643, 1), (2153, 1), (9041, 1), (115299363463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (643, 1), (2153, 1), (9041, 1), (115299363463, 1)] : List FactorBlock).map factorBlockValue).prod) = 510859699633932980261179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_59
      · exact prime_seventyEightBX_643
      · exact prime_seventyEightBX_2153
      · exact prime_seventyEightBX_9041
      · exact prime_seventyEightBX_115299363463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 510859699633932980261179) ^ 255429849816966490130589 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 510859699633932980261179) ^ 170286566544644326753726 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 510859699633932980261179) ^ 8658638976846321699342 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 510859699633932980261179) ^ 794494089632866221246 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 510859699633932980261179) ^ 237278076931692048426 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 510859699633932980261179) ^ 56504778192006744858 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 510859699633932980261179) ^ 4430724370806 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_816750218852862480323507 : Nat.Prime 816750218852862480323507 := by
  apply lucas_primality 816750218852862480323507 (2 : ZMod 816750218852862480323507)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (251, 1), (24677, 1), (1291313, 1), (3003396959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (251, 1), (24677, 1), (1291313, 1), (3003396959, 1)] : List FactorBlock).map factorBlockValue).prod) = 816750218852862480323507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_17
      · exact prime_seventyEightBX_251
      · exact prime_seventyEightBX_24677
      · exact prime_seventyEightBX_1291313
      · exact prime_seventyEightBX_3003396959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 816750218852862480323507) ^ 408375109426431240161753 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 816750218852862480323507) ^ 48044130520756616489618 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 816750218852862480323507) ^ 3253984935668774822006 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 816750218852862480323507) ^ 33097630135464703178 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 816750218852862480323507) ^ 632495931546311762 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 816750218852862480323507) ^ 271942147509134 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_891173166856917838244711 : Nat.Prime 891173166856917838244711 := by
  apply lucas_primality 891173166856917838244711 (23 : ZMod 891173166856917838244711)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (43, 1), (8419, 1), (51487, 1), (4781185006249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (43, 1), (8419, 1), (51487, 1), (4781185006249, 1)] : List FactorBlock).map factorBlockValue).prod) = 891173166856917838244711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_43
      · exact prime_seventyEightBX_8419
      · exact prime_seventyEightBX_51487
      · exact prime_seventyEightBX_4781185006249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 891173166856917838244711) ^ 445586583428458919122355 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (23 : ZMod 891173166856917838244711) ^ 178234633371383567648942 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (23 : ZMod 891173166856917838244711) ^ 20724957368765531121970 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (23 : ZMod 891173166856917838244711) ^ 105852615139199173090 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (23 : ZMod 891173166856917838244711) ^ 17308702524072442330 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (23 : ZMod 891173166856917838244711) ^ 186391692790 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_1189495355880867632354129 : Nat.Prime 1189495355880867632354129 := by
  apply lucas_primality 1189495355880867632354129 (3 : ZMod 1189495355880867632354129)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (41, 1), (4423, 1), (58565780035271933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (41, 1), (4423, 1), (58565780035271933, 1)] : List FactorBlock).map factorBlockValue).prod) = 1189495355880867632354129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_41
      · exact prime_seventyEightBX_4423
      · exact prime_seventyEightBX_58565780035271933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1189495355880867632354129) ^ 594747677940433816177064 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1189495355880867632354129) ^ 169927907982981090336304 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1189495355880867632354129) ^ 29012081850752869081808 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1189495355880867632354129) ^ 268934061921968716336 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1189495355880867632354129) ^ 20310416 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_1227217664453377481147761 : Nat.Prime 1227217664453377481147761 := by
  apply lucas_primality 1227217664453377481147761 (17 : ZMod 1227217664453377481147761)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (7, 1), (730486705031772310207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (7, 1), (730486705031772310207, 1)] : List FactorBlock).map factorBlockValue).prod) = 1227217664453377481147761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_730486705031772310207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 1227217664453377481147761) ^ 613608832226688740573880 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (17 : ZMod 1227217664453377481147761) ^ 409072554817792493715920 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (17 : ZMod 1227217664453377481147761) ^ 245443532890675496229552 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (17 : ZMod 1227217664453377481147761) ^ 175316809207625354449680 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (17 : ZMod 1227217664453377481147761) ^ 1680 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_1333210209198053232891703 : Nat.Prime 1333210209198053232891703 := by
  apply lucas_primality 1333210209198053232891703 (3 : ZMod 1333210209198053232891703)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (13, 1), (263, 1), (3347683, 1), (1764864093611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (13, 1), (263, 1), (3347683, 1), (1764864093611, 1)] : List FactorBlock).map factorBlockValue).prod) = 1333210209198053232891703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_11
      · exact prime_seventyEightBX_13
      · exact prime_seventyEightBX_263
      · exact prime_seventyEightBX_3347683
      · exact prime_seventyEightBX_1764864093611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1333210209198053232891703) ^ 666605104599026616445851 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1333210209198053232891703) ^ 444403403066017744297234 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1333210209198053232891703) ^ 121200928108913930262882 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1333210209198053232891703) ^ 102554631476773325607054 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1333210209198053232891703) ^ 5069240339156095942554 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1333210209198053232891703) ^ 398248642179696594 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1333210209198053232891703) ^ 755418059682 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_3201972811111810557843271 : Nat.Prime 3201972811111810557843271 := by
  apply lucas_primality 3201972811111810557843271 (3 : ZMod 3201972811111810557843271)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (101, 1), (227, 1), (1153, 1), (1688231, 1), (2391596869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (101, 1), (227, 1), (1153, 1), (1688231, 1), (2391596869, 1)] : List FactorBlock).map factorBlockValue).prod) = 3201972811111810557843271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_101
      · exact prime_seventyEightBX_227
      · exact prime_seventyEightBX_1153
      · exact prime_seventyEightBX_1688231
      · exact prime_seventyEightBX_2391596869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3201972811111810557843271) ^ 1600986405555905278921635 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3201972811111810557843271) ^ 1067324270370603519281090 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3201972811111810557843271) ^ 640394562222362111568654 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3201972811111810557843271) ^ 31702701100116936216270 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3201972811111810557843271) ^ 14105607097408857083010 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3201972811111810557843271) ^ 2777079628024120171590 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3201972811111810557843271) ^ 1896643771564324170 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3201972811111810557843271) ^ 1338843035218830 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_7725292532463780184794019 : Nat.Prime 7725292532463780184794019 := by
  apply lucas_primality 7725292532463780184794019 (2 : ZMod 7725292532463780184794019)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19501, 1), (66024755418215990503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19501, 1), (66024755418215990503, 1)] : List FactorBlock).map factorBlockValue).prod) = 7725292532463780184794019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_19501
      · exact prime_seventyEightBX_66024755418215990503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7725292532463780184794019) ^ 3862646266231890092397009 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 7725292532463780184794019) ^ 2575097510821260061598006 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 7725292532463780184794019) ^ 396148532509295943018 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 7725292532463780184794019) ^ 117006 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_20792968874863617602229133 : Nat.Prime 20792968874863617602229133 := by
  apply lucas_primality 20792968874863617602229133 (2 : ZMod 20792968874863617602229133)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1193, 1), (347772767, 1), (4176372649831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1193, 1), (347772767, 1), (4176372649831, 1)] : List FactorBlock).map factorBlockValue).prod) = 20792968874863617602229133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_1193
      · exact prime_seventyEightBX_347772767
      · exact prime_seventyEightBX_4176372649831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20792968874863617602229133) ^ 10396484437431808801114566 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 20792968874863617602229133) ^ 6930989624954539200743044 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 20792968874863617602229133) ^ 17429144069458187428524 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 20792968874863617602229133) ^ 59788950854980596 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 20792968874863617602229133) ^ 4978714932372 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_34040906961986025864114509 : Nat.Prime 34040906961986025864114509 := by
  apply lucas_primality 34040906961986025864114509 (2 : ZMod 34040906961986025864114509)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (5867, 1), (21841, 1), (5108685551191757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (5867, 1), (21841, 1), (5108685551191757, 1)] : List FactorBlock).map factorBlockValue).prod) = 34040906961986025864114509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_13
      · exact prime_seventyEightBX_5867
      · exact prime_seventyEightBX_21841
      · exact prime_seventyEightBX_5108685551191757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 34040906961986025864114509) ^ 17020453480993012932057254 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 34040906961986025864114509) ^ 2618531304768155835701116 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 34040906961986025864114509) ^ 5802097658426116561124 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 34040906961986025864114509) ^ 1558578222699785992588 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 34040906961986025864114509) ^ 6663339644 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_77558298536602307877112031 : Nat.Prime 77558298536602307877112031 := by
  apply lucas_primality 77558298536602307877112031 (7 : ZMod 77558298536602307877112031)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (1992889, 1), (555964578749761261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (1992889, 1), (555964578749761261, 1)] : List FactorBlock).map factorBlockValue).prod) = 77558298536602307877112031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_7
      · exact prime_seventyEightBX_1992889
      · exact prime_seventyEightBX_555964578749761261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 77558298536602307877112031) ^ 38779149268301153938556015 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 77558298536602307877112031) ^ 15511659707320461575422406 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 77558298536602307877112031) ^ 11079756933800329696730290 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 77558298536602307877112031) ^ 38917520512483288270 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 77558298536602307877112031) ^ 139502230 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_91849419282888589707057973 : Nat.Prime 91849419282888589707057973 := by
  apply lucas_primality 91849419282888589707057973 (2 : ZMod 91849419282888589707057973)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (557, 1), (1057052654823097519991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (557, 1), (1057052654823097519991, 1)] : List FactorBlock).map factorBlockValue).prod) = 91849419282888589707057973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_13
      · exact prime_seventyEightBX_557
      · exact prime_seventyEightBX_1057052654823097519991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 91849419282888589707057973) ^ 45924709641444294853528986 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 91849419282888589707057973) ^ 30616473094296196569019324 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 91849419282888589707057973) ^ 7065339944837583823619844 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 91849419282888589707057973) ^ 164900214152403213118596 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 91849419282888589707057973) ^ 86892 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_139300327734169401912214811 : Nat.Prime 139300327734169401912214811 := by
  apply lucas_primality 139300327734169401912214811 (2 : ZMod 139300327734169401912214811)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (315124471, 1), (44204858890241311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (315124471, 1), (44204858890241311, 1)] : List FactorBlock).map factorBlockValue).prod) = 139300327734169401912214811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_315124471
      · exact prime_seventyEightBX_44204858890241311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 139300327734169401912214811) ^ 69650163867084700956107405 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 139300327734169401912214811) ^ 27860065546833880382442962 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 139300327734169401912214811) ^ 442048588902413110 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 139300327734169401912214811) ^ 3151244710 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_853859416296482815424872267 : Nat.Prime 853859416296482815424872267 := by
  apply lucas_primality 853859416296482815424872267 (2 : ZMod 853859416296482815424872267)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7310959, 1), (7696573, 1), (843028245391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7310959, 1), (7696573, 1), (843028245391, 1)] : List FactorBlock).map factorBlockValue).prod) = 853859416296482815424872267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_7310959
      · exact prime_seventyEightBX_7696573
      · exact prime_seventyEightBX_843028245391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 853859416296482815424872267) ^ 426929708148241407712436133 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 853859416296482815424872267) ^ 284619805432160938474957422 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 853859416296482815424872267) ^ 116791711770847410774 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 853859416296482815424872267) ^ 110940208882119719442 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 853859416296482815424872267) ^ 1012847933583126 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_1111045987470122217661279577 : Nat.Prime 1111045987470122217661279577 := by
  apply lucas_primality 1111045987470122217661279577 (3 : ZMod 1111045987470122217661279577)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (72109, 1), (1925983558692608096183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (72109, 1), (1925983558692608096183, 1)] : List FactorBlock).map factorBlockValue).prod) = 1111045987470122217661279577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_72109
      · exact prime_seventyEightBX_1925983558692608096183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1111045987470122217661279577) ^ 555522993735061108830639788 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1111045987470122217661279577) ^ 15407868469540864769464 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1111045987470122217661279577) ^ 576872 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_1397224499394244607058881891 : Nat.Prime 1397224499394244607058881891 := by
  apply lucas_primality 1397224499394244607058881891 (2 : ZMod 1397224499394244607058881891)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (268501, 1), (18109991923, 1), (28734393043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (268501, 1), (18109991923, 1), (28734393043, 1)] : List FactorBlock).map factorBlockValue).prod) = 1397224499394244607058881891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_268501
      · exact prime_seventyEightBX_18109991923
      · exact prime_seventyEightBX_28734393043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1397224499394244607058881891) ^ 698612249697122303529440945 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1397224499394244607058881891) ^ 279444899878848921411776378 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1397224499394244607058881891) ^ 5203796259210373916890 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1397224499394244607058881891) ^ 77152132664385430 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1397224499394244607058881891) ^ 48625509413174230 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_1440887765000314751029471951 : Nat.Prime 1440887765000314751029471951 := by
  apply lucas_primality 1440887765000314751029471951 (7 : ZMod 1440887765000314751029471951)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (3201972811111810557843271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (3201972811111810557843271, 1)] : List FactorBlock).map factorBlockValue).prod) = 1440887765000314751029471951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_3201972811111810557843271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1440887765000314751029471951) ^ 720443882500157375514735975 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440887765000314751029471951) ^ 480295921666771583676490650 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440887765000314751029471951) ^ 288177553000062950205894390 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440887765000314751029471951) ^ 450 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_10246312995557793785098467211 : Nat.Prime 10246312995557793785098467211 := by
  apply lucas_primality 10246312995557793785098467211 (3 : ZMod 10246312995557793785098467211)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (17, 1), (37014790991, 1), (180925960112327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (17, 1), (37014790991, 1), (180925960112327, 1)] : List FactorBlock).map factorBlockValue).prod) = 10246312995557793785098467211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_17
      · exact prime_seventyEightBX_37014790991
      · exact prime_seventyEightBX_180925960112327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10246312995557793785098467211) ^ 5123156497778896892549233605 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 10246312995557793785098467211) ^ 3415437665185931261699489070 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 10246312995557793785098467211) ^ 2049262599111558757019693442 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 10246312995557793785098467211) ^ 602724293856340810888145130 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 10246312995557793785098467211) ^ 276816718971860310 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 10246312995557793785098467211) ^ 56632630216230 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_13173830994288592009412314979 : Nat.Prime 13173830994288592009412314979 := by
  apply lucas_primality 13173830994288592009412314979 (2 : ZMod 13173830994288592009412314979)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (42139, 1), (44809, 1), (4828303, 1), (11844269033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (42139, 1), (44809, 1), (4828303, 1), (11844269033, 1)] : List FactorBlock).map factorBlockValue).prod) = 13173830994288592009412314979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_61
      · exact prime_seventyEightBX_42139
      · exact prime_seventyEightBX_44809
      · exact prime_seventyEightBX_4828303
      · exact prime_seventyEightBX_11844269033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13173830994288592009412314979) ^ 6586915497144296004706157489 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 13173830994288592009412314979) ^ 215964442529321180482169098 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 13173830994288592009412314979) ^ 312627992935014879551302 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 13173830994288592009412314979) ^ 293999665118359972537042 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 13173830994288592009412314979) ^ 2728459873849796089726 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 13173830994288592009412314979) ^ 1112253610381883666 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_13173830994288592009412314981 : Nat.Prime 13173830994288592009412314981 := by
  apply lucas_primality 13173830994288592009412314981 (6 : ZMod 13173830994288592009412314981)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (193, 1), (9093421, 1), (125105450193518611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (193, 1), (9093421, 1), (125105450193518611, 1)] : List FactorBlock).map factorBlockValue).prod) = 13173830994288592009412314981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_193
      · exact prime_seventyEightBX_9093421
      · exact prime_seventyEightBX_125105450193518611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 13173830994288592009412314981) ^ 6586915497144296004706157490 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 13173830994288592009412314981) ^ 4391276998096197336470771660 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 13173830994288592009412314981) ^ 2634766198857718401882462996 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 13173830994288592009412314981) ^ 68258191680251772069493860 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 13173830994288592009412314981) ^ 1448721113240945515380 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 13173830994288592009412314981) ^ 105301815180 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_18443363392004028813177240967 : Nat.Prime 18443363392004028813177240967 := by
  apply lucas_primality 18443363392004028813177240967 (3 : ZMod 18443363392004028813177240967)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (1087, 1), (1697, 1), (8123, 1), (7073967095719697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (1087, 1), (1697, 1), (8123, 1), (7073967095719697, 1)] : List FactorBlock).map factorBlockValue).prod) = 18443363392004028813177240967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_29
      · exact prime_seventyEightBX_1087
      · exact prime_seventyEightBX_1697
      · exact prime_seventyEightBX_8123
      · exact prime_seventyEightBX_7073967095719697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 18443363392004028813177240967) ^ 9221681696002014406588620483 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 18443363392004028813177240967) ^ 6147787797334676271059080322 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 18443363392004028813177240967) ^ 635978048000138924592318654 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 18443363392004028813177240967) ^ 16967215632018425771092218 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 18443363392004028813177240967) ^ 10868216494993534951783878 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 18443363392004028813177240967) ^ 2270511312569743790862642 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (3 : ZMod 18443363392004028813177240967) ^ 2607216451878 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_30738938986673381355295401611 : Nat.Prime 30738938986673381355295401611 := by
  apply lucas_primality 30738938986673381355295401611 (6 : ZMod 30738938986673381355295401611)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (1087, 1), (1697, 1), (8123, 1), (7073967095719697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (1087, 1), (1697, 1), (8123, 1), (7073967095719697, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673381355295401611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_5
      · exact prime_seventyEightBX_29
      · exact prime_seventyEightBX_1087
      · exact prime_seventyEightBX_1697
      · exact prime_seventyEightBX_8123
      · exact prime_seventyEightBX_7073967095719697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 30738938986673381355295401611) ^ 15369469493336690677647700805 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 30738938986673381355295401611) ^ 6147787797334676271059080322 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 30738938986673381355295401611) ^ 1059963413333564874320531090 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 30738938986673381355295401611) ^ 28278692720030709618487030 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 30738938986673381355295401611) ^ 18113694158322558252973130 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 30738938986673381355295401611) ^ 3784185520949572984771070 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (6 : ZMod 30738938986673381355295401611) ^ 4345360753130 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem prime_seventyEightBX_92216816960020144065886204813 : Nat.Prime 92216816960020144065886204813 := by
  apply lucas_primality 92216816960020144065886204813 (2 : ZMod 92216816960020144065886204813)
  · rw [← seventyEightBXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (53, 1), (52763369723, 1), (2748023789635879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (53, 1), (52763369723, 1), (2748023789635879, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyEightBX_2
      · exact prime_seventyEightBX_3
      · exact prime_seventyEightBX_53
      · exact prime_seventyEightBX_52763369723
      · exact prime_seventyEightBX_2748023789635879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 92216816960020144065886204813) ^ 46108408480010072032943102406 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 92216816960020144065886204813) ^ 30738938986673381355295401604 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 92216816960020144065886204813) ^ 1739939942641889510677098204 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 92216816960020144065886204813) ^ 1747743130208419044 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide
    · change (2 : ZMod 92216816960020144065886204813) ^ 33557503143828 ≠ 1
      rw [← seventyEightBXFastPow_eq_pow]
      decide

private theorem phi_seventyEightBX_92216816960020144065886204800 : Nat.totient 92216816960020144065886204800 = 24591151189338705084236313600 := by
  rw [← show ((([(2, 7), (3, 2), (5, 2), (3201972811111810557843271, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204800 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_3, prime_seventyEightBX_5, prime_seventyEightBX_3201972811111810557843271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204801 : Nat.totient 92216816960020144065886204801 = 89022696749311439302370988288 := by
  rw [← show ((([(29, 1), (6257, 1), (508213239571790734051717, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204801 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_29, prime_seventyEightBX_6257, prime_seventyEightBX_508213239571790734051717]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204802 : Nat.totient 92216816960020144065886204802 = 46108408479454158937629551572 := by
  rw [← show ((([(2, 1), (82941768683, 1), (555913012371782147, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204802 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_82941768683, prime_seventyEightBX_555913012371782147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204803 : Nat.totient 92216816960020144065886204803 = 58465013885685888438521128224 := by
  rw [← show ((([(3, 1), (23, 1), (173, 1), (7725292532463780184794019, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204803 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_3, prime_seventyEightBX_23, prime_seventyEightBX_173, prime_seventyEightBX_7725292532463780184794019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204804 : Nat.totient 92216816960020144065886204804 = 39521355067081137472743456000 := by
  rw [← show ((([(2, 2), (7, 1), (434201, 1), (842771, 1), (9000190335447733, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204804 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_7, prime_seventyEightBX_434201, prime_seventyEightBX_842771, prime_seventyEightBX_9000190335447733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204805 : Nat.totient 92216816960020144065886204805 = 68279535203134975073588957184 := by
  rw [← show ((([(5, 1), (17, 2), (67, 1), (587, 1), (49367, 1), (923917, 1), (35576210179, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204805 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_5, prime_seventyEightBX_17, prime_seventyEightBX_67, prime_seventyEightBX_587, prime_seventyEightBX_49367, prime_seventyEightBX_923917, prime_seventyEightBX_35576210179]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204806 : Nat.totient 92216816960020144065886204806 = 27944489987884892141177637800 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (1397224499394244607058881891, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204806 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_3, prime_seventyEightBX_11, prime_seventyEightBX_1397224499394244607058881891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204807 : Nat.totient 92216816960020144065886204807 = 91866182675001056065635618012 := by
  rw [← show ((([(263, 2), (1333210209198053232891703, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204807 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_263, prime_seventyEightBX_1333210209198053232891703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204808 : Nat.totient 92216816960020144065886204808 = 45552253763667759748633263168 := by
  rw [← show ((([(2, 3), (83, 1), (72109, 1), (1925983558692608096183, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204808 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_83, prime_seventyEightBX_72109, prime_seventyEightBX_1925983558692608096183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204809 : Nat.totient 92216816960020144065886204809 = 61477761630297074211922532760 := by
  rw [← show ((([(3, 4), (528419, 1), (2154500920157382217331, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204809 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_3, prime_seventyEightBX_528419, prime_seventyEightBX_2154500920157382217331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204810 : Nat.totient 92216816960020144065886204810 = 36483683632517971369232148480 := by
  rw [← show ((([(2, 1), (5, 1), (167, 1), (223, 1), (2837, 1), (7481, 1), (11667284899887053, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204810 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_5, prime_seventyEightBX_167, prime_seventyEightBX_223, prime_seventyEightBX_2837, prime_seventyEightBX_7481, prime_seventyEightBX_11667284899887053]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204811 : Nat.totient 92216816960020144065886204811 = 72962471081321627625046846080 := by
  rw [← show ((([(7, 1), (13, 1), (255839, 1), (16963103611, 1), (233505261949, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204811 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_7, prime_seventyEightBX_13, prime_seventyEightBX_255839, prime_seventyEightBX_16963103611, prime_seventyEightBX_233505261949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204812 : Nat.totient 92216816960020144065886204812 = 30158959005221151595377870528 := by
  rw [← show ((([(2, 2), (3, 1), (53, 1), (52763369723, 1), (2748023789635879, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204812 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_3, prime_seventyEightBX_53, prime_seventyEightBX_52763369723, prime_seventyEightBX_2748023789635879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204813 : Nat.totient 92216816960020144065886204813 = 92216816960020144065886204812 := by
  rw [← show ((([(92216816960020144065886204813, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204813 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_92216816960020144065886204813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204814 : Nat.totient 92216816960020144065886204814 = 45127348811102273941782908400 := by
  rw [← show ((([(2, 1), (47, 2), (2666267, 1), (3532219, 1), (2216323525151, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204814 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_47, prime_seventyEightBX_2666267, prime_seventyEightBX_3532219, prime_seventyEightBX_2216323525151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204815 : Nat.totient 92216816960020144065886204815 = 47853050944903000305597129600 := by
  rw [← show ((([(3, 1), (5, 1), (37, 1), (2638788283, 1), (62966941313719351, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204815 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_3, prime_seventyEightBX_5, prime_seventyEightBX_37, prime_seventyEightBX_2638788283, prime_seventyEightBX_62966941313719351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204816 : Nat.totient 92216816960020144065886204816 = 45748290334569616111604981760 := by
  rw [← show ((([(2, 4), (233, 1), (283, 1), (153038260961, 1), (571146824419, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204816 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_233, prime_seventyEightBX_283, prime_seventyEightBX_153038260961, prime_seventyEightBX_571146824419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204817 : Nat.totient 92216816960020144065886204817 = 83832268948297276027658048640 := by
  rw [← show ((([(11, 1), (70009, 1), (23625919, 1), (5068446393271957, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204817 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_11, prime_seventyEightBX_70009, prime_seventyEightBX_23625919, prime_seventyEightBX_5068446393271957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204818 : Nat.totient 92216816960020144065886204818 = 24339970026160837339169894400 := by
  rw [← show ((([(2, 1), (3, 2), (7, 1), (19, 1), (41, 1), (2539, 1), (10781, 1), (75997, 1), (451631192279, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204818 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_3, prime_seventyEightBX_7, prime_seventyEightBX_19, prime_seventyEightBX_41, prime_seventyEightBX_2539, prime_seventyEightBX_10781, prime_seventyEightBX_75997, prime_seventyEightBX_451631192279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204819 : Nat.totient 92216816960020144065886204819 = 92042100214491098880192378240 := by
  rw [← show ((([(757, 1), (1741, 1), (446794223, 1), (156605830836269, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204819 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_757, prime_seventyEightBX_1741, prime_seventyEightBX_446794223, prime_seventyEightBX_156605830836269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204820 : Nat.totient 92216816960020144065886204820 = 36886525198144159081193769600 := by
  rw [← show ((([(2, 2), (5, 1), (317651, 1), (574219, 1), (1738127, 1), (14543563807, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204820 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_5, prime_seventyEightBX_317651, prime_seventyEightBX_574219, prime_seventyEightBX_1738127, prime_seventyEightBX_14543563807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204821 : Nat.totient 92216816960020144065886204821 = 61217358344532891475306168320 := by
  rw [← show ((([(3, 1), (241, 1), (11287, 1), (119135249, 1), (94853427462929, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204821 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_3, prime_seventyEightBX_241, prime_seventyEightBX_11287, prime_seventyEightBX_119135249, prime_seventyEightBX_94853427462929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204822 : Nat.totient 92216816960020144065886204822 = 43393156938863346869198651520 := by
  rw [← show ((([(2, 1), (17, 1), (14503, 1), (187013674574469671722861, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204822 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_17, prime_seventyEightBX_14503, prime_seventyEightBX_187013674574469671722861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204823 : Nat.totient 92216816960020144065886204823 = 91452260355065689895131075200 := by
  rw [← show ((([(163, 1), (461, 1), (1227217664453377481147761, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204823 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_163, prime_seventyEightBX_461, prime_seventyEightBX_1227217664453377481147761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204824 : Nat.totient 92216816960020144065886204824 = 28307005033898556934417612800 := by
  rw [← show ((([(2, 3), (3, 1), (13, 2), (421, 1), (11111809, 1), (4860101258566261, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204824 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_3, prime_seventyEightBX_13, prime_seventyEightBX_421, prime_seventyEightBX_11111809, prime_seventyEightBX_4860101258566261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204825 : Nat.totient 92216816960020144065886204825 = 62891177355966204535211827200 := by
  rw [← show ((([(5, 2), (7, 1), (311, 1), (739, 1), (1153, 1), (1988556542649278027, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204825 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_5, prime_seventyEightBX_7, prime_seventyEightBX_311, prime_seventyEightBX_739, prime_seventyEightBX_1153, prime_seventyEightBX_1988556542649278027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204826 : Nat.totient 92216816960020144065886204826 = 43691510993428243636992178416 := by
  rw [← show ((([(2, 1), (23, 1), (107, 1), (5230683487, 1), (3581872122960559, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204826 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_23, prime_seventyEightBX_107, prime_seventyEightBX_5230683487, prime_seventyEightBX_3581872122960559]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204827 : Nat.totient 92216816960020144065886204827 = 59402765873433726944769777840 := by
  rw [← show ((([(3, 2), (31, 1), (647, 1), (510859699633932980261179, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204827 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_3, prime_seventyEightBX_31, prime_seventyEightBX_647, prime_seventyEightBX_510859699633932980261179]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204828 : Nat.totient 92216816960020144065886204828 = 41916732294922947670133007360 := by
  rw [← show ((([(2, 2), (11, 1), (16231273, 1), (401861413, 1), (321313195913, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204828 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_11, prime_seventyEightBX_16231273, prime_seventyEightBX_401861413, prime_seventyEightBX_321313195913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204829 : Nat.totient 92216816960020144065886204829 = 91804857883328951556448878592 := by
  rw [← show ((([(227, 1), (16193, 1), (2188157, 1), (15995339, 1), (716778593, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204829 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_227, prime_seventyEightBX_16193, prime_seventyEightBX_2188157, prime_seventyEightBX_15995339, prime_seventyEightBX_716778593]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204830 : Nat.totient 92216816960020144065886204830 = 23704440663365447221934358528 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (29, 1), (1087, 1), (1697, 1), (8123, 1), (7073967095719697, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204830 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_3, prime_seventyEightBX_5, prime_seventyEightBX_29, prime_seventyEightBX_1087, prime_seventyEightBX_1697, prime_seventyEightBX_8123, prime_seventyEightBX_7073967095719697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204831 : Nat.totient 92216816960020144065886204831 = 91085763684051306990677028864 := by
  rw [← show ((([(113, 1), (293, 1), (30089, 1), (4934066413, 1), (18760798487, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204831 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_113, prime_seventyEightBX_293, prime_seventyEightBX_30089, prime_seventyEightBX_4934066413, prime_seventyEightBX_18760798487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204832 : Nat.totient 92216816960020144065886204832 = 39338950970967698221043558400 := by
  rw [← show ((([(2, 5), (7, 1), (389, 1), (487, 1), (2173119189262831037801, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204832 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_7, prime_seventyEightBX_389, prime_seventyEightBX_487, prime_seventyEightBX_2173119189262831037801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204833 : Nat.totient 92216816960020144065886204833 = 61477877973346762710590803220 := by
  rw [← show ((([(3, 1), (30738938986673381355295401611, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204833 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_3, prime_seventyEightBX_30738938986673381355295401611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204834 : Nat.totient 92216816960020144065886204834 = 46091390780748148533837622800 := by
  rw [← show ((([(2, 1), (3547, 1), (11471, 1), (1133228957975860628941, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204834 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_3547, prime_seventyEightBX_11471, prime_seventyEightBX_1133228957975860628941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204835 : Nat.totient 92216816960020144065886204835 = 73773453568016115252708963864 := by
  rw [← show ((([(5, 1), (18443363392004028813177240967, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204835 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_5, prime_seventyEightBX_18443363392004028813177240967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204836 : Nat.totient 92216816960020144065886204836 = 30738938986673381355295401576 := by
  rw [← show ((([(2, 2), (3, 3), (853859416296482815424872267, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204836 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_3, prime_seventyEightBX_853859416296482815424872267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204837 : Nat.totient 92216816960020144065886204837 = 80463172925856811480316559360 := by
  rw [← show ((([(13, 1), (19, 1), (877, 1), (1063, 1), (7307, 1), (71233, 1), (769413804491, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204837 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_13, prime_seventyEightBX_19, prime_seventyEightBX_877, prime_seventyEightBX_1063, prime_seventyEightBX_7307, prime_seventyEightBX_71233, prime_seventyEightBX_769413804491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204838 : Nat.totient 92216816960020144065886204838 = 45012278660874238186483449600 := by
  rw [← show ((([(2, 1), (43, 1), (1889, 1), (84039987347, 1), (6754508306851, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204838 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_43, prime_seventyEightBX_1889, prime_seventyEightBX_84039987347, prime_seventyEightBX_6754508306851]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204839 : Nat.totient 92216816960020144065886204839 = 44558624398957045572206592000 := by
  rw [← show ((([(3, 1), (7, 2), (11, 1), (17, 1), (109, 1), (401, 1), (13763, 1), (5576570614480753, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204839 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_3, prime_seventyEightBX_7, prime_seventyEightBX_11, prime_seventyEightBX_17, prime_seventyEightBX_109, prime_seventyEightBX_401, prime_seventyEightBX_13763, prime_seventyEightBX_5576570614480753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204840 : Nat.totient 92216816960020144065886204840 = 36886726780902480861839176704 := by
  rw [← show ((([(2, 3), (5, 1), (11877577609, 1), (194098535904628969, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204840 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_5, prime_seventyEightBX_11877577609, prime_seventyEightBX_194098535904628969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204841 : Nat.totient 92216816960020144065886204841 = 91210986834585978302982239808 := by
  rw [← show ((([(103, 1), (839, 1), (54437, 1), (19602739051568953829, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204841 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_103, prime_seventyEightBX_839, prime_seventyEightBX_54437, prime_seventyEightBX_19602739051568953829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204842 : Nat.totient 92216816960020144065886204842 = 30305947736541474679562433840 := by
  rw [← show ((([(2, 1), (3, 1), (71, 1), (625543, 1), (346053590743723896119, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204842 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_3, prime_seventyEightBX_71, prime_seventyEightBX_625543, prime_seventyEightBX_346053590743723896119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204843 : Nat.totient 92216816960020144065886204843 = 92094078636998913253637398176 := by
  rw [← show ((([(1103, 1), (2447, 1), (62219, 1), (78404959, 1), (7003805663, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204843 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_1103, prime_seventyEightBX_2447, prime_seventyEightBX_62219, prime_seventyEightBX_78404959, prime_seventyEightBX_7003805663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204844 : Nat.totient 92216816960020144065886204844 = 46107865472361301996882106304 := by
  rw [← show ((([(2, 2), (84913, 1), (271503824385018030413147, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204844 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_84913, prime_seventyEightBX_271503824385018030413147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204845 : Nat.totient 92216816960020144065886204845 = 49182298189465906825503935616 := by
  rw [← show ((([(3, 2), (5, 1), (11740229, 1), (174550479305945289229, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204845 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_3, prime_seventyEightBX_5, prime_seventyEightBX_11740229, prime_seventyEightBX_174550479305945289229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204846 : Nat.totient 92216816960020144065886204846 = 38871801572934106952216156160 := by
  rw [← show ((([(2, 1), (7, 1), (61, 1), (42139, 1), (44809, 1), (4828303, 1), (11844269033, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204846 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_7, prime_seventyEightBX_61, prime_seventyEightBX_42139, prime_seventyEightBX_44809, prime_seventyEightBX_4828303, prime_seventyEightBX_11844269033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204847 : Nat.totient 92216816960020144065886204847 = 92121387866072710608730141824 := by
  rw [← show ((([(1109, 1), (7549, 1), (1293533, 1), (8515529217944699, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204847 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_1109, prime_seventyEightBX_7549, prime_seventyEightBX_1293533, prime_seventyEightBX_8515529217944699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204848 : Nat.totient 92216816960020144065886204848 = 30720453722183856110178576384 := by
  rw [← show ((([(2, 4), (3, 1), (2683, 1), (4373, 1), (18077177, 1), (9058121252407, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204848 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_3, prime_seventyEightBX_2683, prime_seventyEightBX_4373, prime_seventyEightBX_18077177, prime_seventyEightBX_9058121252407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204849 : Nat.totient 92216816960020144065886204849 = 88189421630856679175410883856 := by
  rw [← show ((([(23, 1), (4909, 1), (816750218852862480323507, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204849 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_23, prime_seventyEightBX_4909, prime_seventyEightBX_816750218852862480323507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204850 : Nat.totient 92216816960020144065886204850 = 30952522162055159442522316800 := by
  rw [← show ((([(2, 1), (5, 2), (11, 1), (13, 1), (23957, 1), (413087, 1), (4211653, 1), (309440777, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204850 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_5, prime_seventyEightBX_11, prime_seventyEightBX_13, prime_seventyEightBX_23957, prime_seventyEightBX_413087, prime_seventyEightBX_4211653, prime_seventyEightBX_309440777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204851 : Nat.totient 92216816960020144065886204851 = 61419611044608645360979497600 := by
  rw [← show ((([(3, 1), (1229, 1), (7451, 1), (45380784637, 1), (73969115579, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204851 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_3, prime_seventyEightBX_1229, prime_seventyEightBX_7451, prime_seventyEightBX_45380784637, prime_seventyEightBX_73969115579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204852 : Nat.totient 92216816960020144065886204852 = 44862233023143123345606177792 := by
  rw [← show ((([(2, 2), (37, 1), (37219873, 1), (42756079, 1), (391539565447, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204852 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_37, prime_seventyEightBX_37219873, prime_seventyEightBX_42756079, prime_seventyEightBX_391539565447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204853 : Nat.totient 92216816960020144065886204853 = 79042985965731552056473889868 := by
  rw [← show ((([(7, 1), (13173830994288592009412314979, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204853 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_7, prime_seventyEightBX_13173830994288592009412314979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204854 : Nat.totient 92216816960020144065886204854 = 29803995636951019396265031168 := by
  rw [← show ((([(2, 1), (3, 2), (59, 1), (73, 1), (1189495355880867632354129, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204854 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_3, prime_seventyEightBX_59, prime_seventyEightBX_73, prime_seventyEightBX_1189495355880867632354129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204855 : Nat.totient 92216816960020144065886204855 = 73690281692516660782300043808 := by
  rw [← show ((([(5, 1), (887, 1), (20792968874863617602229133, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204855 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_5, prime_seventyEightBX_887, prime_seventyEightBX_20792968874863617602229133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204856 : Nat.totient 92216816960020144065886204856 = 41111651035750151278477246464 := by
  rw [← show ((([(2, 3), (17, 1), (19, 1), (84809, 1), (7461329, 1), (56397452316869, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204856 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_17, prime_seventyEightBX_19, prime_seventyEightBX_84809, prime_seventyEightBX_7461329, prime_seventyEightBX_56397452316869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204857 : Nat.totient 92216816960020144065886204857 = 61477877539339026699860648400 := by
  rw [← show ((([(3, 1), (169781627, 1), (858431347, 1), (210907786451, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204857 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_3, prime_seventyEightBX_169781627, prime_seventyEightBX_858431347, prime_seventyEightBX_210907786451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204858 : Nat.totient 92216816960020144065886204858 = 44594305269520168625765288400 := by
  rw [← show ((([(2, 1), (31, 1), (1669, 1), (891173166856917838244711, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204858 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_31, prime_seventyEightBX_1669, prime_seventyEightBX_891173166856917838244711]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204859 : Nat.totient 92216816960020144065886204859 = 86865294360994584822365473600 := by
  rw [← show ((([(29, 1), (41, 1), (77558298536602307877112031, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204859 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_29, prime_seventyEightBX_41, prime_seventyEightBX_77558298536602307877112031]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204860 : Nat.totient 92216816960020144065886204860 = 20968914178229686245203558400 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (7, 1), (193, 1), (9093421, 1), (125105450193518611, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204860 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_3, prime_seventyEightBX_5, prime_seventyEightBX_7, prime_seventyEightBX_193, prime_seventyEightBX_9093421, prime_seventyEightBX_125105450193518611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204861 : Nat.totient 92216816960020144065886204861 = 82045123273705040927428104000 := by
  rw [← show ((([(11, 1), (47, 1), (17623, 1), (17930590291, 1), (564475576981, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204861 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_11, prime_seventyEightBX_47, prime_seventyEightBX_17623, prime_seventyEightBX_17930590291, prime_seventyEightBX_564475576981]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204862 : Nat.totient 92216816960020144065886204862 = 45524686177191930476464700640 := by
  rw [← show ((([(2, 1), (79, 1), (636653, 1), (810992503, 1), (1130403285971, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204862 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_79, prime_seventyEightBX_636653, prime_seventyEightBX_810992503, prime_seventyEightBX_1130403285971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204863 : Nat.totient 92216816960020144065886204863 = 56511320421201537225041342208 := by
  rw [← show ((([(3, 3), (13, 1), (239, 1), (1194889, 1), (919978222885966903, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204863 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_3, prime_seventyEightBX_13, prime_seventyEightBX_239, prime_seventyEightBX_1194889, prime_seventyEightBX_919978222885966903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204864 : Nat.totient 92216816960020144065886204864 = 46108408480010072032943102400 := by
  rw [← show ((([(2, 6), (1440887765000314751029471951, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204864 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_1440887765000314751029471951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204865 : Nat.totient 92216816960020144065886204865 = 72381497921962846099167949056 := by
  rw [← show ((([(5, 1), (53, 1), (19605277, 1), (17749710372792891533, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204865 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_5, prime_seventyEightBX_53, prime_seventyEightBX_19605277, prime_seventyEightBX_17749710372792891533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204866 : Nat.totient 92216816960020144065886204866 = 30738883771221526484291025648 := by
  rw [← show ((([(2, 1), (3, 1), (556709, 1), (27607725927435501631279, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204866 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_3, prime_seventyEightBX_556709, prime_seventyEightBX_27607725927435501631279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204867 : Nat.totient 92216816960020144065886204867 = 79042985965731552056473889880 := by
  rw [← show ((([(7, 1), (13173830994288592009412314981, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204867 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_7, prime_seventyEightBX_13173830994288592009412314981]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204868 : Nat.totient 92216816960020144065886204868 = 46107977966677049838266527200 := by
  rw [← show ((([(2, 2), (107101, 1), (215256666511097338180517, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204868 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_107101, prime_seventyEightBX_215256666511097338180517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204869 : Nat.totient 92216816960020144065886204869 = 61477877968724291190280240560 := by
  rw [← show ((([(3, 1), (13299785203, 1), (2311235746855496141, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204869 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_3, prime_seventyEightBX_13299785203, prime_seventyEightBX_2311235746855496141]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204870 : Nat.totient 92216816960020144065886204870 = 36849642675580384801921382400 := by
  rw [← show ((([(2, 1), (5, 1), (1129, 1), (8353, 1), (977853296795507446351, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204870 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_5, prime_seventyEightBX_1129, prime_seventyEightBX_8353, prime_seventyEightBX_977853296795507446351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204871 : Nat.totient 92216816960020144065886204871 = 91265662703411587059409540800 := by
  rw [← show ((([(127, 1), (443, 1), (4931, 1), (332405099619231428681, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204871 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_127, prime_seventyEightBX_443, prime_seventyEightBX_4931, prime_seventyEightBX_332405099619231428681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204872 : Nat.totient 92216816960020144065886204872 = 26318849194750105553836953600 := by
  rw [← show ((([(2, 3), (3, 2), (11, 1), (23, 1), (67, 1), (2281, 1), (153379, 1), (215968852178549, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204872 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_3, prime_seventyEightBX_11, prime_seventyEightBX_23, prime_seventyEightBX_67, prime_seventyEightBX_2281, prime_seventyEightBX_153379, prime_seventyEightBX_215968852178549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204873 : Nat.totient 92216816960020144065886204873 = 86792294150415285474253693696 := by
  rw [← show ((([(17, 1), (22537799, 1), (276556517, 1), (870293636243, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204873 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_17, prime_seventyEightBX_22537799, prime_seventyEightBX_276556517, prime_seventyEightBX_870293636243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204874 : Nat.totient 92216816960020144065886204874 = 39471158670546492257417280000 := by
  rw [← show ((([(2, 1), (7, 1), (881, 1), (7211, 1), (1036837480313182770601, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204874 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_7, prime_seventyEightBX_881, prime_seventyEightBX_7211, prime_seventyEightBX_1036837480313182770601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204875 : Nat.totient 92216816960020144065886204875 = 46593751752432756258080457600 := by
  rw [← show ((([(3, 1), (5, 3), (19, 1), (5549659, 1), (2332163318914464653, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204875 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_3, prime_seventyEightBX_5, prime_seventyEightBX_19, prime_seventyEightBX_5549659, prime_seventyEightBX_2332163318914464653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204876 : Nat.totient 92216816960020144065886204876 = 42559004436199013388161378304 := by
  rw [← show ((([(2, 2), (13, 1), (16417, 1), (3919277, 1), (27561765092259707, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204876 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_13, prime_seventyEightBX_16417, prime_seventyEightBX_3919277, prime_seventyEightBX_27561765092259707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204877 : Nat.totient 92216816960020144065886204877 = 92215960067558271881381792704 := by
  rw [← show ((([(110039, 1), (4890827, 1), (171348849023448209, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204877 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_110039, prime_seventyEightBX_4890827, prime_seventyEightBX_171348849023448209]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204878 : Nat.totient 92216816960020144065886204878 = 30737777586151449948888499200 := by
  rw [← show ((([(2, 1), (3, 1), (46957, 1), (60661, 1), (547215289, 1), (9860314021, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204878 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_3, prime_seventyEightBX_46957, prime_seventyEightBX_60661, prime_seventyEightBX_547215289, prime_seventyEightBX_9860314021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204879 : Nat.totient 92216816960020144065886204879 = 92008589229075476886417113856 := by
  rw [← show ((([(503, 1), (3697, 1), (49589838281654484274169, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204879 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_503, prime_seventyEightBX_3697, prime_seventyEightBX_49589838281654484274169]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204880 : Nat.totient 92216816960020144065886204880 = 36886726767521640468552662144 := by
  rw [← show ((([(2, 4), (5, 1), (2237401043, 1), (515200533943905827, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204880 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_5, prime_seventyEightBX_2237401043, prime_seventyEightBX_515200533943905827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204881 : Nat.totient 92216816960020144065886204881 = 51469851326522871106541136096 := by
  rw [← show ((([(3, 2), (7, 1), (43, 1), (34040906961986025864114509, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204881 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_3, prime_seventyEightBX_7, prime_seventyEightBX_43, prime_seventyEightBX_34040906961986025864114509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204882 : Nat.totient 92216816960020144065886204882 = 45969108152275902631030887300 := by
  rw [← show ((([(2, 1), (331, 1), (139300327734169401912214811, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204882 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_331, prime_seventyEightBX_139300327734169401912214811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204883 : Nat.totient 92216816960020144065886204883 = 83614441777581256387511487840 := by
  rw [← show ((([(11, 1), (383, 1), (589493, 1), (37131288166716682987, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204883 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_11, prime_seventyEightBX_383, prime_seventyEightBX_589493, prime_seventyEightBX_37131288166716682987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204884 : Nat.totient 92216816960020144065886204884 = 30422042708452954993738364928 := by
  rw [← show ((([(2, 2), (3, 1), (97, 1), (6172893972383, 1), (12834186024857, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204884 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_3, prime_seventyEightBX_97, prime_seventyEightBX_6172893972383, prime_seventyEightBX_12834186024857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204885 : Nat.totient 92216816960020144065886204885 = 73773453568013286501518785680 := by
  rw [← show ((([(5, 1), (27119884711471, 1), (680067912833087, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204885 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_5, prime_seventyEightBX_27119884711471, prime_seventyEightBX_680067912833087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204886 : Nat.totient 92216816960020144065886204886 = 45651757639687555384581696000 := by
  rw [← show ((([(2, 1), (101, 1), (346469, 1), (251943121, 1), (5229881765107, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204886 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_101, prime_seventyEightBX_346469, prime_seventyEightBX_251943121, prime_seventyEightBX_5229881765107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204887 : Nat.totient 92216816960020144065886204887 = 61460372601727479602173145952 := by
  rw [← show ((([(3, 1), (3559, 1), (265543, 1), (32525653229239405517, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204887 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_3, prime_seventyEightBX_3559, prime_seventyEightBX_265543, prime_seventyEightBX_32525653229239405517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204888 : Nat.totient 92216816960020144065886204888 = 37725953263489929005572967424 := by
  rw [← show ((([(2, 3), (7, 3), (29, 1), (89, 1), (9479, 1), (1373648109517237423, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204888 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_7, prime_seventyEightBX_29, prime_seventyEightBX_89, prime_seventyEightBX_9479, prime_seventyEightBX_1373648109517237423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204889 : Nat.totient 92216816960020144065886204889 = 80130502370732401610634758400 := by
  rw [← show ((([(13, 1), (31, 1), (37, 1), (3931, 1), (1573259321512510633829, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204889 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_13, prime_seventyEightBX_31, prime_seventyEightBX_37, prime_seventyEightBX_3931, prime_seventyEightBX_1573259321512510633829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204890 : Nat.totient 92216816960020144065886204890 = 23144612883458079096838909440 := by
  rw [← show ((([(2, 1), (3, 4), (5, 1), (17, 1), (37014790991, 1), (180925960112327, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204890 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_3, prime_seventyEightBX_5, prime_seventyEightBX_17, prime_seventyEightBX_37014790991, prime_seventyEightBX_180925960112327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204891 : Nat.totient 92216816960020144065886204891 = 91105770972550021848224925232 := by
  rw [← show ((([(83, 1), (1111045987470122217661279577, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204891 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_83, prime_seventyEightBX_1111045987470122217661279577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204892 : Nat.totient 92216816960020144065886204892 = 45924709641444294853528986000 := by
  rw [← show ((([(2, 2), (251, 1), (91849419282888589707057973, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204892 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_251, prime_seventyEightBX_91849419282888589707057973]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204893 : Nat.totient 92216816960020144065886204893 = 61374786516768287385518290560 := by
  rw [← show ((([(3, 1), (607, 1), (33911, 1), (4995887929, 1), (298914441407, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204893 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_3, prime_seventyEightBX_607, prime_seventyEightBX_33911, prime_seventyEightBX_4995887929, prime_seventyEightBX_298914441407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204894 : Nat.totient 92216816960020144065886204894 = 39642270743557960756804656000 := by
  rw [← show ((([(2, 1), (11, 1), (19, 1), (599, 1), (20611, 1), (388541, 1), (45990815088367, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204894 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_11, prime_seventyEightBX_19, prime_seventyEightBX_599, prime_seventyEightBX_20611, prime_seventyEightBX_388541, prime_seventyEightBX_45990815088367]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204895 : Nat.totient 92216816960020144065886204895 = 60455795495839607721357168768 := by
  rw [← show ((([(5, 1), (7, 1), (23, 1), (2203, 1), (33287, 1), (1562158492327693999, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204895 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_5, prime_seventyEightBX_7, prime_seventyEightBX_23, prime_seventyEightBX_2203, prime_seventyEightBX_33287, prime_seventyEightBX_1562158492327693999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204896 : Nat.totient 92216816960020144065886204896 = 30535367726102340256846579200 := by
  rw [← show ((([(2, 5), (3, 1), (151, 1), (14347919, 1), (443376867845076029, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204896 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_3, prime_seventyEightBX_151, prime_seventyEightBX_14347919, prime_seventyEightBX_443376867845076029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204897 : Nat.totient 92216816960020144065886204897 = 92216816959700610732816273600 := by
  rw [← show ((([(288598686601, 1), (319533044471244697, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204897 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_288598686601, prime_seventyEightBX_319533044471244697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204898 : Nat.totient 92216816960020144065886204898 = 46107830759583241891137738960 := by
  rw [← show ((([(2, 1), (79811, 1), (102641951197, 1), (5628497536247, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204898 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_79811, prime_seventyEightBX_102641951197, prime_seventyEightBX_5628497536247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204899 : Nat.totient 92216816960020144065886204899 = 61477877973346762710590803260 := by
  rw [← show ((([(3, 2), (10246312995557793785098467211, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204899 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_3, prime_seventyEightBX_10246312995557793785098467211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204900 : Nat.totient 92216816960020144065886204900 = 35678144375621952575757926400 := by
  rw [← show ((([(2, 2), (5, 2), (41, 1), (179, 1), (349, 1), (7013, 1), (152287, 1), (337117379789, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204900 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_5, prime_seventyEightBX_41, prime_seventyEightBX_179, prime_seventyEightBX_349, prime_seventyEightBX_7013, prime_seventyEightBX_152287, prime_seventyEightBX_337117379789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204901 : Nat.totient 92216816960020144065886204901 = 91753415281666751695047939600 := by
  rw [← show ((([(199, 1), (156016151, 1), (2970212297131708549, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204901 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_199, prime_seventyEightBX_156016151, prime_seventyEightBX_2970212297131708549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyEightBX_92216816960020144065886204902 : Nat.totient 92216816960020144065886204902 = 24314976681972022995248424960 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (13, 1), (4093, 1), (100290972241, 1), (411446998799, 1)] : List FactorBlock).map factorBlockValue).prod) = 92216816960020144065886204902 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyEightBX_2, prime_seventyEightBX_3, prime_seventyEightBX_7, prime_seventyEightBX_13, prime_seventyEightBX_4093, prime_seventyEightBX_100290972241, prime_seventyEightBX_411446998799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64SeventyEightBX : certifiedKill 2 92216816960020144065886204799 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_seventyEightBX_92216816960020144065886204800, phi_seventyEightBX_92216816960020144065886204801, phi_seventyEightBX_92216816960020144065886204802,
    phi_seventyEightBX_92216816960020144065886204803, phi_seventyEightBX_92216816960020144065886204804, phi_seventyEightBX_92216816960020144065886204805,
    phi_seventyEightBX_92216816960020144065886204806, phi_seventyEightBX_92216816960020144065886204807, phi_seventyEightBX_92216816960020144065886204808,
    phi_seventyEightBX_92216816960020144065886204809, phi_seventyEightBX_92216816960020144065886204810, phi_seventyEightBX_92216816960020144065886204811,
    phi_seventyEightBX_92216816960020144065886204812, phi_seventyEightBX_92216816960020144065886204813, phi_seventyEightBX_92216816960020144065886204814,
    phi_seventyEightBX_92216816960020144065886204815, phi_seventyEightBX_92216816960020144065886204816, phi_seventyEightBX_92216816960020144065886204817,
    phi_seventyEightBX_92216816960020144065886204818, phi_seventyEightBX_92216816960020144065886204819, phi_seventyEightBX_92216816960020144065886204820,
    phi_seventyEightBX_92216816960020144065886204821, phi_seventyEightBX_92216816960020144065886204822, phi_seventyEightBX_92216816960020144065886204823,
    phi_seventyEightBX_92216816960020144065886204824, phi_seventyEightBX_92216816960020144065886204825, phi_seventyEightBX_92216816960020144065886204826,
    phi_seventyEightBX_92216816960020144065886204827, phi_seventyEightBX_92216816960020144065886204828, phi_seventyEightBX_92216816960020144065886204829,
    phi_seventyEightBX_92216816960020144065886204830, phi_seventyEightBX_92216816960020144065886204831, phi_seventyEightBX_92216816960020144065886204832,
    phi_seventyEightBX_92216816960020144065886204833, phi_seventyEightBX_92216816960020144065886204834, phi_seventyEightBX_92216816960020144065886204835,
    phi_seventyEightBX_92216816960020144065886204836, phi_seventyEightBX_92216816960020144065886204837, phi_seventyEightBX_92216816960020144065886204838,
    phi_seventyEightBX_92216816960020144065886204839, phi_seventyEightBX_92216816960020144065886204840, phi_seventyEightBX_92216816960020144065886204841,
    phi_seventyEightBX_92216816960020144065886204842, phi_seventyEightBX_92216816960020144065886204843, phi_seventyEightBX_92216816960020144065886204844,
    phi_seventyEightBX_92216816960020144065886204845, phi_seventyEightBX_92216816960020144065886204846, phi_seventyEightBX_92216816960020144065886204847,
    phi_seventyEightBX_92216816960020144065886204848, phi_seventyEightBX_92216816960020144065886204849, phi_seventyEightBX_92216816960020144065886204850,
    phi_seventyEightBX_92216816960020144065886204851, phi_seventyEightBX_92216816960020144065886204852, phi_seventyEightBX_92216816960020144065886204853,
    phi_seventyEightBX_92216816960020144065886204854, phi_seventyEightBX_92216816960020144065886204855, phi_seventyEightBX_92216816960020144065886204856,
    phi_seventyEightBX_92216816960020144065886204857, phi_seventyEightBX_92216816960020144065886204858, phi_seventyEightBX_92216816960020144065886204859,
    phi_seventyEightBX_92216816960020144065886204860, phi_seventyEightBX_92216816960020144065886204861, phi_seventyEightBX_92216816960020144065886204862,
    phi_seventyEightBX_92216816960020144065886204863, phi_seventyEightBX_92216816960020144065886204864, phi_seventyEightBX_92216816960020144065886204865,
    phi_seventyEightBX_92216816960020144065886204866, phi_seventyEightBX_92216816960020144065886204867, phi_seventyEightBX_92216816960020144065886204868,
    phi_seventyEightBX_92216816960020144065886204869, phi_seventyEightBX_92216816960020144065886204870, phi_seventyEightBX_92216816960020144065886204871,
    phi_seventyEightBX_92216816960020144065886204872, phi_seventyEightBX_92216816960020144065886204873, phi_seventyEightBX_92216816960020144065886204874,
    phi_seventyEightBX_92216816960020144065886204875, phi_seventyEightBX_92216816960020144065886204876, phi_seventyEightBX_92216816960020144065886204877,
    phi_seventyEightBX_92216816960020144065886204878, phi_seventyEightBX_92216816960020144065886204879, phi_seventyEightBX_92216816960020144065886204880,
    phi_seventyEightBX_92216816960020144065886204881, phi_seventyEightBX_92216816960020144065886204882, phi_seventyEightBX_92216816960020144065886204883,
    phi_seventyEightBX_92216816960020144065886204884, phi_seventyEightBX_92216816960020144065886204885, phi_seventyEightBX_92216816960020144065886204886,
    phi_seventyEightBX_92216816960020144065886204887, phi_seventyEightBX_92216816960020144065886204888, phi_seventyEightBX_92216816960020144065886204889,
    phi_seventyEightBX_92216816960020144065886204890, phi_seventyEightBX_92216816960020144065886204891, phi_seventyEightBX_92216816960020144065886204892,
    phi_seventyEightBX_92216816960020144065886204893, phi_seventyEightBX_92216816960020144065886204894, phi_seventyEightBX_92216816960020144065886204895,
    phi_seventyEightBX_92216816960020144065886204896, phi_seventyEightBX_92216816960020144065886204897, phi_seventyEightBX_92216816960020144065886204898,
    phi_seventyEightBX_92216816960020144065886204899, phi_seventyEightBX_92216816960020144065886204900, phi_seventyEightBX_92216816960020144065886204901,
    phi_seventyEightBX_92216816960020144065886204902]

end TotientTailPeriodKiller
end Erdos249257
