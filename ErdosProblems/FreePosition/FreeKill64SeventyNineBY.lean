import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def seventyNineBYFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem seventyNineBYFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : seventyNineBYFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [seventyNineBYFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [seventyNineBYFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then seventyNineBYFastPow a n * seventyNineBYFastPow a n * a else seventyNineBYFastPow a n * seventyNineBYFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_seventyNineBY_2 : Nat.Prime 2 := by norm_num
private theorem prime_seventyNineBY_3 : Nat.Prime 3 := by norm_num
private theorem prime_seventyNineBY_5 : Nat.Prime 5 := by norm_num
private theorem prime_seventyNineBY_7 : Nat.Prime 7 := by norm_num
private theorem prime_seventyNineBY_11 : Nat.Prime 11 := by norm_num
private theorem prime_seventyNineBY_13 : Nat.Prime 13 := by norm_num
private theorem prime_seventyNineBY_17 : Nat.Prime 17 := by norm_num
private theorem prime_seventyNineBY_19 : Nat.Prime 19 := by norm_num
private theorem prime_seventyNineBY_23 : Nat.Prime 23 := by norm_num
private theorem prime_seventyNineBY_29 : Nat.Prime 29 := by norm_num
private theorem prime_seventyNineBY_31 : Nat.Prime 31 := by norm_num
private theorem prime_seventyNineBY_37 : Nat.Prime 37 := by norm_num
private theorem prime_seventyNineBY_41 : Nat.Prime 41 := by norm_num
private theorem prime_seventyNineBY_43 : Nat.Prime 43 := by norm_num
private theorem prime_seventyNineBY_47 : Nat.Prime 47 := by norm_num
private theorem prime_seventyNineBY_53 : Nat.Prime 53 := by norm_num
private theorem prime_seventyNineBY_59 : Nat.Prime 59 := by norm_num
private theorem prime_seventyNineBY_61 : Nat.Prime 61 := by norm_num
private theorem prime_seventyNineBY_67 : Nat.Prime 67 := by norm_num
private theorem prime_seventyNineBY_71 : Nat.Prime 71 := by norm_num
private theorem prime_seventyNineBY_73 : Nat.Prime 73 := by norm_num
private theorem prime_seventyNineBY_79 : Nat.Prime 79 := by norm_num
private theorem prime_seventyNineBY_83 : Nat.Prime 83 := by norm_num
private theorem prime_seventyNineBY_89 : Nat.Prime 89 := by norm_num
private theorem prime_seventyNineBY_97 : Nat.Prime 97 := by norm_num
private theorem prime_seventyNineBY_101 : Nat.Prime 101 := by norm_num
private theorem prime_seventyNineBY_103 : Nat.Prime 103 := by norm_num
private theorem prime_seventyNineBY_107 : Nat.Prime 107 := by norm_num
private theorem prime_seventyNineBY_109 : Nat.Prime 109 := by norm_num
private theorem prime_seventyNineBY_113 : Nat.Prime 113 := by norm_num
private theorem prime_seventyNineBY_127 : Nat.Prime 127 := by norm_num
private theorem prime_seventyNineBY_131 : Nat.Prime 131 := by norm_num
private theorem prime_seventyNineBY_137 : Nat.Prime 137 := by norm_num
private theorem prime_seventyNineBY_139 : Nat.Prime 139 := by norm_num
private theorem prime_seventyNineBY_149 : Nat.Prime 149 := by norm_num
private theorem prime_seventyNineBY_151 : Nat.Prime 151 := by norm_num
private theorem prime_seventyNineBY_157 : Nat.Prime 157 := by norm_num
private theorem prime_seventyNineBY_163 : Nat.Prime 163 := by norm_num
private theorem prime_seventyNineBY_167 : Nat.Prime 167 := by norm_num
private theorem prime_seventyNineBY_173 : Nat.Prime 173 := by norm_num
private theorem prime_seventyNineBY_179 : Nat.Prime 179 := by norm_num
private theorem prime_seventyNineBY_181 : Nat.Prime 181 := by norm_num
private theorem prime_seventyNineBY_191 : Nat.Prime 191 := by norm_num
private theorem prime_seventyNineBY_193 : Nat.Prime 193 := by norm_num
private theorem prime_seventyNineBY_197 : Nat.Prime 197 := by norm_num
private theorem prime_seventyNineBY_199 : Nat.Prime 199 := by norm_num
private theorem prime_seventyNineBY_211 : Nat.Prime 211 := by norm_num
private theorem prime_seventyNineBY_223 : Nat.Prime 223 := by norm_num
private theorem prime_seventyNineBY_227 : Nat.Prime 227 := by norm_num
private theorem prime_seventyNineBY_229 : Nat.Prime 229 := by norm_num
private theorem prime_seventyNineBY_233 : Nat.Prime 233 := by norm_num
private theorem prime_seventyNineBY_239 : Nat.Prime 239 := by norm_num
private theorem prime_seventyNineBY_241 : Nat.Prime 241 := by norm_num
private theorem prime_seventyNineBY_251 : Nat.Prime 251 := by norm_num
private theorem prime_seventyNineBY_269 : Nat.Prime 269 := by norm_num
private theorem prime_seventyNineBY_271 : Nat.Prime 271 := by norm_num
private theorem prime_seventyNineBY_277 : Nat.Prime 277 := by norm_num
private theorem prime_seventyNineBY_281 : Nat.Prime 281 := by norm_num
private theorem prime_seventyNineBY_293 : Nat.Prime 293 := by norm_num
private theorem prime_seventyNineBY_307 : Nat.Prime 307 := by norm_num
private theorem prime_seventyNineBY_317 : Nat.Prime 317 := by norm_num
private theorem prime_seventyNineBY_331 : Nat.Prime 331 := by norm_num
private theorem prime_seventyNineBY_337 : Nat.Prime 337 := by norm_num
private theorem prime_seventyNineBY_347 : Nat.Prime 347 := by norm_num
private theorem prime_seventyNineBY_349 : Nat.Prime 349 := by norm_num
private theorem prime_seventyNineBY_353 : Nat.Prime 353 := by norm_num
private theorem prime_seventyNineBY_359 : Nat.Prime 359 := by norm_num
private theorem prime_seventyNineBY_367 : Nat.Prime 367 := by norm_num
private theorem prime_seventyNineBY_373 : Nat.Prime 373 := by norm_num
private theorem prime_seventyNineBY_383 : Nat.Prime 383 := by norm_num
private theorem prime_seventyNineBY_389 : Nat.Prime 389 := by norm_num
private theorem prime_seventyNineBY_397 : Nat.Prime 397 := by norm_num
private theorem prime_seventyNineBY_401 : Nat.Prime 401 := by norm_num
private theorem prime_seventyNineBY_421 : Nat.Prime 421 := by norm_num
private theorem prime_seventyNineBY_433 : Nat.Prime 433 := by norm_num
private theorem prime_seventyNineBY_443 : Nat.Prime 443 := by norm_num
private theorem prime_seventyNineBY_449 : Nat.Prime 449 := by norm_num
private theorem prime_seventyNineBY_461 : Nat.Prime 461 := by norm_num
private theorem prime_seventyNineBY_463 : Nat.Prime 463 := by norm_num
private theorem prime_seventyNineBY_479 : Nat.Prime 479 := by norm_num
private theorem prime_seventyNineBY_487 : Nat.Prime 487 := by norm_num
private theorem prime_seventyNineBY_509 : Nat.Prime 509 := by norm_num
private theorem prime_seventyNineBY_521 : Nat.Prime 521 := by norm_num
private theorem prime_seventyNineBY_547 : Nat.Prime 547 := by norm_num
private theorem prime_seventyNineBY_557 : Nat.Prime 557 := by norm_num
private theorem prime_seventyNineBY_563 : Nat.Prime 563 := by norm_num
private theorem prime_seventyNineBY_587 : Nat.Prime 587 := by norm_num
private theorem prime_seventyNineBY_599 : Nat.Prime 599 := by norm_num
private theorem prime_seventyNineBY_607 : Nat.Prime 607 := by norm_num
private theorem prime_seventyNineBY_617 : Nat.Prime 617 := by norm_num
private theorem prime_seventyNineBY_647 : Nat.Prime 647 := by norm_num
private theorem prime_seventyNineBY_653 : Nat.Prime 653 := by norm_num
private theorem prime_seventyNineBY_673 : Nat.Prime 673 := by norm_num
private theorem prime_seventyNineBY_701 : Nat.Prime 701 := by norm_num
private theorem prime_seventyNineBY_733 : Nat.Prime 733 := by norm_num
private theorem prime_seventyNineBY_739 : Nat.Prime 739 := by norm_num
private theorem prime_seventyNineBY_757 : Nat.Prime 757 := by norm_num
private theorem prime_seventyNineBY_773 : Nat.Prime 773 := by norm_num
private theorem prime_seventyNineBY_809 : Nat.Prime 809 := by norm_num
private theorem prime_seventyNineBY_823 : Nat.Prime 823 := by norm_num
private theorem prime_seventyNineBY_827 : Nat.Prime 827 := by norm_num
private theorem prime_seventyNineBY_829 : Nat.Prime 829 := by norm_num
private theorem prime_seventyNineBY_839 : Nat.Prime 839 := by norm_num
private theorem prime_seventyNineBY_853 : Nat.Prime 853 := by norm_num
private theorem prime_seventyNineBY_863 : Nat.Prime 863 := by norm_num
private theorem prime_seventyNineBY_907 : Nat.Prime 907 := by norm_num
private theorem prime_seventyNineBY_911 : Nat.Prime 911 := by norm_num
private theorem prime_seventyNineBY_919 : Nat.Prime 919 := by norm_num
private theorem prime_seventyNineBY_941 : Nat.Prime 941 := by norm_num
private theorem prime_seventyNineBY_977 : Nat.Prime 977 := by norm_num
private theorem prime_seventyNineBY_983 : Nat.Prime 983 := by norm_num
private theorem prime_seventyNineBY_1009 : Nat.Prime 1009 := by norm_num
private theorem prime_seventyNineBY_1091 : Nat.Prime 1091 := by norm_num
private theorem prime_seventyNineBY_1097 : Nat.Prime 1097 := by norm_num
private theorem prime_seventyNineBY_1103 : Nat.Prime 1103 := by norm_num
private theorem prime_seventyNineBY_1213 : Nat.Prime 1213 := by norm_num
private theorem prime_seventyNineBY_1217 : Nat.Prime 1217 := by norm_num
private theorem prime_seventyNineBY_1229 : Nat.Prime 1229 := by norm_num
private theorem prime_seventyNineBY_1249 : Nat.Prime 1249 := by norm_num
private theorem prime_seventyNineBY_1277 : Nat.Prime 1277 := by norm_num
private theorem prime_seventyNineBY_1291 : Nat.Prime 1291 := by norm_num
private theorem prime_seventyNineBY_1361 : Nat.Prime 1361 := by norm_num
private theorem prime_seventyNineBY_1423 : Nat.Prime 1423 := by norm_num
private theorem prime_seventyNineBY_1429 : Nat.Prime 1429 := by norm_num
private theorem prime_seventyNineBY_1433 : Nat.Prime 1433 := by norm_num
private theorem prime_seventyNineBY_1451 : Nat.Prime 1451 := by norm_num
private theorem prime_seventyNineBY_1483 : Nat.Prime 1483 := by norm_num
private theorem prime_seventyNineBY_1487 : Nat.Prime 1487 := by norm_num
private theorem prime_seventyNineBY_1489 : Nat.Prime 1489 := by norm_num
private theorem prime_seventyNineBY_1531 : Nat.Prime 1531 := by norm_num
private theorem prime_seventyNineBY_1543 : Nat.Prime 1543 := by norm_num
private theorem prime_seventyNineBY_1549 : Nat.Prime 1549 := by norm_num
private theorem prime_seventyNineBY_1553 : Nat.Prime 1553 := by norm_num
private theorem prime_seventyNineBY_1613 : Nat.Prime 1613 := by norm_num
private theorem prime_seventyNineBY_1621 : Nat.Prime 1621 := by norm_num
private theorem prime_seventyNineBY_1693 : Nat.Prime 1693 := by norm_num
private theorem prime_seventyNineBY_1721 : Nat.Prime 1721 := by norm_num
private theorem prime_seventyNineBY_1723 : Nat.Prime 1723 := by norm_num
private theorem prime_seventyNineBY_1733 : Nat.Prime 1733 := by norm_num
private theorem prime_seventyNineBY_1747 : Nat.Prime 1747 := by norm_num
private theorem prime_seventyNineBY_1831 : Nat.Prime 1831 := by norm_num
private theorem prime_seventyNineBY_1873 : Nat.Prime 1873 := by norm_num
private theorem prime_seventyNineBY_1877 : Nat.Prime 1877 := by norm_num
private theorem prime_seventyNineBY_1931 : Nat.Prime 1931 := by norm_num
private theorem prime_seventyNineBY_1979 : Nat.Prime 1979 := by norm_num
private theorem prime_seventyNineBY_1999 : Nat.Prime 1999 := by norm_num
private theorem prime_seventyNineBY_2003 : Nat.Prime 2003 := by norm_num
private theorem prime_seventyNineBY_2087 : Nat.Prime 2087 := by norm_num
private theorem prime_seventyNineBY_2129 : Nat.Prime 2129 := by norm_num
private theorem prime_seventyNineBY_2287 : Nat.Prime 2287 := by norm_num
private theorem prime_seventyNineBY_2347 : Nat.Prime 2347 := by norm_num
private theorem prime_seventyNineBY_2351 : Nat.Prime 2351 := by norm_num
private theorem prime_seventyNineBY_2393 : Nat.Prime 2393 := by norm_num
private theorem prime_seventyNineBY_2447 : Nat.Prime 2447 := by norm_num
private theorem prime_seventyNineBY_2593 : Nat.Prime 2593 := by norm_num
private theorem prime_seventyNineBY_2617 : Nat.Prime 2617 := by norm_num
private theorem prime_seventyNineBY_2647 : Nat.Prime 2647 := by norm_num
private theorem prime_seventyNineBY_2689 : Nat.Prime 2689 := by norm_num
private theorem prime_seventyNineBY_2711 : Nat.Prime 2711 := by norm_num
private theorem prime_seventyNineBY_2729 : Nat.Prime 2729 := by norm_num
private theorem prime_seventyNineBY_2731 : Nat.Prime 2731 := by norm_num
private theorem prime_seventyNineBY_2789 : Nat.Prime 2789 := by norm_num
private theorem prime_seventyNineBY_2819 : Nat.Prime 2819 := by norm_num
private theorem prime_seventyNineBY_2903 : Nat.Prime 2903 := by norm_num
private theorem prime_seventyNineBY_3163 : Nat.Prime 3163 := by norm_num
private theorem prime_seventyNineBY_3331 : Nat.Prime 3331 := by norm_num
private theorem prime_seventyNineBY_3571 : Nat.Prime 3571 := by norm_num
private theorem prime_seventyNineBY_3593 : Nat.Prime 3593 := by norm_num
private theorem prime_seventyNineBY_3613 : Nat.Prime 3613 := by norm_num
private theorem prime_seventyNineBY_3701 : Nat.Prime 3701 := by norm_num
private theorem prime_seventyNineBY_3709 : Nat.Prime 3709 := by norm_num
private theorem prime_seventyNineBY_3797 : Nat.Prime 3797 := by norm_num
private theorem prime_seventyNineBY_3853 : Nat.Prime 3853 := by norm_num
private theorem prime_seventyNineBY_3931 : Nat.Prime 3931 := by norm_num
private theorem prime_seventyNineBY_3943 : Nat.Prime 3943 := by norm_num
private theorem prime_seventyNineBY_3967 : Nat.Prime 3967 := by norm_num
private theorem prime_seventyNineBY_4007 : Nat.Prime 4007 := by norm_num
private theorem prime_seventyNineBY_4027 : Nat.Prime 4027 := by norm_num
private theorem prime_seventyNineBY_4049 : Nat.Prime 4049 := by norm_num
private theorem prime_seventyNineBY_4051 : Nat.Prime 4051 := by norm_num
private theorem prime_seventyNineBY_4139 : Nat.Prime 4139 := by norm_num
private theorem prime_seventyNineBY_4229 : Nat.Prime 4229 := by norm_num
private theorem prime_seventyNineBY_4241 : Nat.Prime 4241 := by norm_num
private theorem prime_seventyNineBY_4243 : Nat.Prime 4243 := by norm_num
private theorem prime_seventyNineBY_4409 : Nat.Prime 4409 := by norm_num
private theorem prime_seventyNineBY_4567 : Nat.Prime 4567 := by norm_num
private theorem prime_seventyNineBY_4591 : Nat.Prime 4591 := by norm_num
private theorem prime_seventyNineBY_4789 : Nat.Prime 4789 := by norm_num
private theorem prime_seventyNineBY_4817 : Nat.Prime 4817 := by norm_num
private theorem prime_seventyNineBY_4861 : Nat.Prime 4861 := by norm_num
private theorem prime_seventyNineBY_4877 : Nat.Prime 4877 := by norm_num
private theorem prime_seventyNineBY_5077 : Nat.Prime 5077 := by norm_num
private theorem prime_seventyNineBY_5099 : Nat.Prime 5099 := by norm_num
private theorem prime_seventyNineBY_5167 : Nat.Prime 5167 := by norm_num
private theorem prime_seventyNineBY_5227 : Nat.Prime 5227 := by norm_num
private theorem prime_seventyNineBY_5441 : Nat.Prime 5441 := by norm_num
private theorem prime_seventyNineBY_5521 : Nat.Prime 5521 := by norm_num
private theorem prime_seventyNineBY_5651 : Nat.Prime 5651 := by norm_num
private theorem prime_seventyNineBY_5827 : Nat.Prime 5827 := by norm_num
private theorem prime_seventyNineBY_6247 : Nat.Prime 6247 := by norm_num
private theorem prime_seventyNineBY_6791 : Nat.Prime 6791 := by norm_num
private theorem prime_seventyNineBY_7451 : Nat.Prime 7451 := by norm_num
private theorem prime_seventyNineBY_7547 : Nat.Prime 7547 := by norm_num
private theorem prime_seventyNineBY_7549 : Nat.Prime 7549 := by norm_num
private theorem prime_seventyNineBY_7559 : Nat.Prime 7559 := by norm_num
private theorem prime_seventyNineBY_7649 : Nat.Prime 7649 := by norm_num
private theorem prime_seventyNineBY_7699 : Nat.Prime 7699 := by norm_num
private theorem prime_seventyNineBY_7741 : Nat.Prime 7741 := by norm_num
private theorem prime_seventyNineBY_8419 : Nat.Prime 8419 := by norm_num
private theorem prime_seventyNineBY_8501 : Nat.Prime 8501 := by norm_num
private theorem prime_seventyNineBY_8537 : Nat.Prime 8537 := by norm_num
private theorem prime_seventyNineBY_8689 : Nat.Prime 8689 := by norm_num
private theorem prime_seventyNineBY_8713 : Nat.Prime 8713 := by norm_num
private theorem prime_seventyNineBY_9029 : Nat.Prime 9029 := by norm_num
private theorem prime_seventyNineBY_9067 : Nat.Prime 9067 := by norm_num
private theorem prime_seventyNineBY_9311 : Nat.Prime 9311 := by norm_num
private theorem prime_seventyNineBY_9511 : Nat.Prime 9511 := by norm_num
private theorem prime_seventyNineBY_10093 : Nat.Prime 10093 := by norm_num
private theorem prime_seventyNineBY_10333 : Nat.Prime 10333 := by norm_num
private theorem prime_seventyNineBY_10789 : Nat.Prime 10789 := by norm_num
private theorem prime_seventyNineBY_11399 : Nat.Prime 11399 := by norm_num
private theorem prime_seventyNineBY_11497 : Nat.Prime 11497 := by norm_num
private theorem prime_seventyNineBY_12401 : Nat.Prime 12401 := by norm_num
private theorem prime_seventyNineBY_12409 : Nat.Prime 12409 := by norm_num
private theorem prime_seventyNineBY_12547 : Nat.Prime 12547 := by norm_num
private theorem prime_seventyNineBY_13001 : Nat.Prime 13001 := by norm_num
private theorem prime_seventyNineBY_13033 : Nat.Prime 13033 := by norm_num
private theorem prime_seventyNineBY_13567 : Nat.Prime 13567 := by norm_num
private theorem prime_seventyNineBY_14009 : Nat.Prime 14009 := by norm_num
private theorem prime_seventyNineBY_14621 : Nat.Prime 14621 := by norm_num
private theorem prime_seventyNineBY_15359 : Nat.Prime 15359 := by norm_num
private theorem prime_seventyNineBY_15401 : Nat.Prime 15401 := by norm_num
private theorem prime_seventyNineBY_15727 : Nat.Prime 15727 := by norm_num
private theorem prime_seventyNineBY_15737 : Nat.Prime 15737 := by norm_num
private theorem prime_seventyNineBY_16273 : Nat.Prime 16273 := by norm_num
private theorem prime_seventyNineBY_16657 : Nat.Prime 16657 := by norm_num
private theorem prime_seventyNineBY_16831 : Nat.Prime 16831 := by norm_num
private theorem prime_seventyNineBY_17123 : Nat.Prime 17123 := by norm_num
private theorem prime_seventyNineBY_18757 : Nat.Prime 18757 := by norm_num
private theorem prime_seventyNineBY_18787 : Nat.Prime 18787 := by norm_num
private theorem prime_seventyNineBY_19013 : Nat.Prime 19013 := by norm_num
private theorem prime_seventyNineBY_19441 : Nat.Prime 19441 := by norm_num
private theorem prime_seventyNineBY_21617 : Nat.Prime 21617 := by norm_num
private theorem prime_seventyNineBY_22051 : Nat.Prime 22051 := by norm_num
private theorem prime_seventyNineBY_22921 : Nat.Prime 22921 := by norm_num
private theorem prime_seventyNineBY_25189 : Nat.Prime 25189 := by norm_num
private theorem prime_seventyNineBY_25261 : Nat.Prime 25261 := by norm_num
private theorem prime_seventyNineBY_25889 : Nat.Prime 25889 := by norm_num
private theorem prime_seventyNineBY_26561 : Nat.Prime 26561 := by norm_num
private theorem prime_seventyNineBY_26723 : Nat.Prime 26723 := by norm_num
private theorem prime_seventyNineBY_27427 : Nat.Prime 27427 := by norm_num
private theorem prime_seventyNineBY_27691 : Nat.Prime 27691 := by norm_num
private theorem prime_seventyNineBY_28759 : Nat.Prime 28759 := by norm_num
private theorem prime_seventyNineBY_29131 : Nat.Prime 29131 := by norm_num
private theorem prime_seventyNineBY_30187 : Nat.Prime 30187 := by norm_num
private theorem prime_seventyNineBY_31063 : Nat.Prime 31063 := by norm_num
private theorem prime_seventyNineBY_31307 : Nat.Prime 31307 := by norm_num
private theorem prime_seventyNineBY_32069 : Nat.Prime 32069 := by norm_num
private theorem prime_seventyNineBY_32401 : Nat.Prime 32401 := by norm_num
private theorem prime_seventyNineBY_33349 : Nat.Prime 33349 := by norm_num
private theorem prime_seventyNineBY_33863 : Nat.Prime 33863 := by norm_num
private theorem prime_seventyNineBY_36713 : Nat.Prime 36713 := by norm_num
private theorem prime_seventyNineBY_37003 : Nat.Prime 37003 := by norm_num
private theorem prime_seventyNineBY_38047 : Nat.Prime 38047 := by norm_num
private theorem prime_seventyNineBY_38239 : Nat.Prime 38239 := by norm_num
private theorem prime_seventyNineBY_38711 : Nat.Prime 38711 := by norm_num
private theorem prime_seventyNineBY_41011 : Nat.Prime 41011 := by norm_num
private theorem prime_seventyNineBY_42331 : Nat.Prime 42331 := by norm_num
private theorem prime_seventyNineBY_43291 : Nat.Prime 43291 := by norm_num
private theorem prime_seventyNineBY_44111 : Nat.Prime 44111 := by norm_num
private theorem prime_seventyNineBY_46957 : Nat.Prime 46957 := by norm_num
private theorem prime_seventyNineBY_47041 : Nat.Prime 47041 := by norm_num
private theorem prime_seventyNineBY_47777 : Nat.Prime 47777 := by norm_num
private theorem prime_seventyNineBY_49451 : Nat.Prime 49451 := by norm_num
private theorem prime_seventyNineBY_49943 : Nat.Prime 49943 := by norm_num
private theorem prime_seventyNineBY_50101 : Nat.Prime 50101 := by norm_num
private theorem prime_seventyNineBY_50441 : Nat.Prime 50441 := by norm_num
private theorem prime_seventyNineBY_51647 : Nat.Prime 51647 := by norm_num
private theorem prime_seventyNineBY_53171 : Nat.Prime 53171 := by norm_num
private theorem prime_seventyNineBY_53959 : Nat.Prime 53959 := by norm_num
private theorem prime_seventyNineBY_57397 : Nat.Prime 57397 := by norm_num
private theorem prime_seventyNineBY_59209 : Nat.Prime 59209 := by norm_num
private theorem prime_seventyNineBY_59509 : Nat.Prime 59509 := by norm_num
private theorem prime_seventyNineBY_60089 : Nat.Prime 60089 := by norm_num
private theorem prime_seventyNineBY_61379 : Nat.Prime 61379 := by norm_num
private theorem prime_seventyNineBY_62581 : Nat.Prime 62581 := by norm_num
private theorem prime_seventyNineBY_62639 : Nat.Prime 62639 := by norm_num
private theorem prime_seventyNineBY_64271 : Nat.Prime 64271 := by norm_num
private theorem prime_seventyNineBY_65809 : Nat.Prime 65809 := by norm_num
private theorem prime_seventyNineBY_66467 : Nat.Prime 66467 := by norm_num
private theorem prime_seventyNineBY_67867 : Nat.Prime 67867 := by norm_num
private theorem prime_seventyNineBY_72073 : Nat.Prime 72073 := by norm_num
private theorem prime_seventyNineBY_74441 : Nat.Prime 74441 := by norm_num
private theorem prime_seventyNineBY_75269 : Nat.Prime 75269 := by norm_num
private theorem prime_seventyNineBY_75289 : Nat.Prime 75289 := by norm_num
private theorem prime_seventyNineBY_75731 : Nat.Prime 75731 := by norm_num
private theorem prime_seventyNineBY_81233 : Nat.Prime 81233 := by norm_num
private theorem prime_seventyNineBY_83089 : Nat.Prime 83089 := by norm_num
private theorem prime_seventyNineBY_93497 : Nat.Prime 93497 := by norm_num
private theorem prime_seventyNineBY_94903 : Nat.Prime 94903 := by norm_num
private theorem prime_seventyNineBY_95419 : Nat.Prime 95419 := by norm_num
private theorem prime_seventyNineBY_95723 : Nat.Prime 95723 := by norm_num
private theorem prime_seventyNineBY_96443 : Nat.Prime 96443 := by norm_num
private theorem prime_seventyNineBY_97561 : Nat.Prime 97561 := by norm_num
private theorem prime_seventyNineBY_101161 : Nat.Prime 101161 := by norm_num
private theorem prime_seventyNineBY_101723 : Nat.Prime 101723 := by norm_num
private theorem prime_seventyNineBY_103393 : Nat.Prime 103393 := by norm_num
private theorem prime_seventyNineBY_112691 : Nat.Prime 112691 := by norm_num
private theorem prime_seventyNineBY_114113 : Nat.Prime 114113 := by norm_num
private theorem prime_seventyNineBY_116849 : Nat.Prime 116849 := by norm_num
private theorem prime_seventyNineBY_124679 : Nat.Prime 124679 := by norm_num
private theorem prime_seventyNineBY_128473 : Nat.Prime 128473 := by norm_num
private theorem prime_seventyNineBY_128621 : Nat.Prime 128621 := by norm_num
private theorem prime_seventyNineBY_129461 : Nat.Prime 129461 := by norm_num
private theorem prime_seventyNineBY_130183 : Nat.Prime 130183 := by norm_num
private theorem prime_seventyNineBY_137933 : Nat.Prime 137933 := by norm_num
private theorem prime_seventyNineBY_145303 : Nat.Prime 145303 := by norm_num
private theorem prime_seventyNineBY_146203 : Nat.Prime 146203 := by norm_num
private theorem prime_seventyNineBY_150343 : Nat.Prime 150343 := by norm_num
private theorem prime_seventyNineBY_155167 : Nat.Prime 155167 := by norm_num
private theorem prime_seventyNineBY_161873 : Nat.Prime 161873 := by norm_num
private theorem prime_seventyNineBY_164893 : Nat.Prime 164893 := by norm_num
private theorem prime_seventyNineBY_167021 : Nat.Prime 167021 := by norm_num
private theorem prime_seventyNineBY_170641 : Nat.Prime 170641 := by norm_num
private theorem prime_seventyNineBY_181277 : Nat.Prime 181277 := by norm_num
private theorem prime_seventyNineBY_181717 : Nat.Prime 181717 := by norm_num
private theorem prime_seventyNineBY_183871 : Nat.Prime 183871 := by norm_num
private theorem prime_seventyNineBY_190543 : Nat.Prime 190543 := by norm_num
private theorem prime_seventyNineBY_192629 : Nat.Prime 192629 := by norm_num
private theorem prime_seventyNineBY_194027 : Nat.Prime 194027 := by norm_num
private theorem prime_seventyNineBY_197479 : Nat.Prime 197479 := by norm_num
private theorem prime_seventyNineBY_214507 : Nat.Prime 214507 := by norm_num
private theorem prime_seventyNineBY_234293 : Nat.Prime 234293 := by norm_num
private theorem prime_seventyNineBY_234809 : Nat.Prime 234809 := by norm_num
private theorem prime_seventyNineBY_271723 : Nat.Prime 271723 := by norm_num
private theorem prime_seventyNineBY_284129 : Nat.Prime 284129 := by norm_num
private theorem prime_seventyNineBY_296027 : Nat.Prime 296027 := by norm_num
private theorem prime_seventyNineBY_303617 : Nat.Prime 303617 := by norm_num
private theorem prime_seventyNineBY_306827 : Nat.Prime 306827 := by norm_num
private theorem prime_seventyNineBY_329801 : Nat.Prime 329801 := by norm_num
private theorem prime_seventyNineBY_338119 : Nat.Prime 338119 := by norm_num
private theorem prime_seventyNineBY_351587 : Nat.Prime 351587 := by norm_num
private theorem prime_seventyNineBY_355853 : Nat.Prime 355853 := by norm_num
private theorem prime_seventyNineBY_367261 : Nat.Prime 367261 := by norm_num
private theorem prime_seventyNineBY_371897 : Nat.Prime 371897 := by norm_num
private theorem prime_seventyNineBY_375149 : Nat.Prime 375149 := by norm_num
private theorem prime_seventyNineBY_386927 : Nat.Prime 386927 := by norm_num
private theorem prime_seventyNineBY_393779 : Nat.Prime 393779 := by norm_num
private theorem prime_seventyNineBY_417733 : Nat.Prime 417733 := by norm_num
private theorem prime_seventyNineBY_423053 : Nat.Prime 423053 := by norm_num
private theorem prime_seventyNineBY_442061 : Nat.Prime 442061 := by norm_num
private theorem prime_seventyNineBY_449261 : Nat.Prime 449261 := by norm_num
private theorem prime_seventyNineBY_449417 : Nat.Prime 449417 := by norm_num
private theorem prime_seventyNineBY_456503 : Nat.Prime 456503 := by norm_num
private theorem prime_seventyNineBY_465529 : Nat.Prime 465529 := by norm_num
private theorem prime_seventyNineBY_472111 : Nat.Prime 472111 := by norm_num
private theorem prime_seventyNineBY_521243 : Nat.Prime 521243 := by norm_num
private theorem prime_seventyNineBY_541507 : Nat.Prime 541507 := by norm_num
private theorem prime_seventyNineBY_547441 : Nat.Prime 547441 := by norm_num
private theorem prime_seventyNineBY_547831 : Nat.Prime 547831 := by norm_num
private theorem prime_seventyNineBY_562417 : Nat.Prime 562417 := by norm_num
private theorem prime_seventyNineBY_566557 : Nat.Prime 566557 := by norm_num
private theorem prime_seventyNineBY_572497 : Nat.Prime 572497 := by norm_num
private theorem prime_seventyNineBY_582677 : Nat.Prime 582677 := by norm_num
private theorem prime_seventyNineBY_612169 : Nat.Prime 612169 := by norm_num
private theorem prime_seventyNineBY_646549 : Nat.Prime 646549 := by norm_num
private theorem prime_seventyNineBY_656377 : Nat.Prime 656377 := by norm_num
private theorem prime_seventyNineBY_703117 : Nat.Prime 703117 := by norm_num
private theorem prime_seventyNineBY_740143 : Nat.Prime 740143 := by norm_num
private theorem prime_seventyNineBY_767813 : Nat.Prime 767813 := by norm_num
private theorem prime_seventyNineBY_788497 : Nat.Prime 788497 := by norm_num
private theorem prime_seventyNineBY_922853 : Nat.Prime 922853 := by norm_num
private theorem prime_seventyNineBY_1100303 : Nat.Prime 1100303 := by norm_num
private theorem prime_seventyNineBY_1291957 : Nat.Prime 1291957 := by norm_num
private theorem prime_seventyNineBY_1328647 : Nat.Prime 1328647 := by norm_num
private theorem prime_seventyNineBY_1372187 : Nat.Prime 1372187 := by norm_num
private theorem prime_seventyNineBY_1479617 : Nat.Prime 1479617 := by norm_num
private theorem prime_seventyNineBY_1505201 : Nat.Prime 1505201 := by norm_num
private theorem prime_seventyNineBY_1585313 : Nat.Prime 1585313 := by norm_num
private theorem prime_seventyNineBY_1622207 : Nat.Prime 1622207 := by norm_num
private theorem prime_seventyNineBY_1699361 : Nat.Prime 1699361 := by norm_num
private theorem prime_seventyNineBY_1736177 : Nat.Prime 1736177 := by norm_num
private theorem prime_seventyNineBY_1775747 : Nat.Prime 1775747 := by norm_num
private theorem prime_seventyNineBY_1835299 : Nat.Prime 1835299 := by norm_num
private theorem prime_seventyNineBY_1934411 : Nat.Prime 1934411 := by norm_num
private theorem prime_seventyNineBY_1973527 : Nat.Prime 1973527 := by norm_num
private theorem prime_seventyNineBY_2007403 : Nat.Prime 2007403 := by norm_num
private theorem prime_seventyNineBY_2012113 : Nat.Prime 2012113 := by norm_num
private theorem prime_seventyNineBY_2029669 : Nat.Prime 2029669 := by norm_num
private theorem prime_seventyNineBY_2098441 : Nat.Prime 2098441 := by norm_num
private theorem prime_seventyNineBY_2190821 : Nat.Prime 2190821 := by norm_num
private theorem prime_seventyNineBY_2202983 : Nat.Prime 2202983 := by norm_num
private theorem prime_seventyNineBY_2234119 : Nat.Prime 2234119 := by norm_num
private theorem prime_seventyNineBY_2287057 : Nat.Prime 2287057 := by norm_num
private theorem prime_seventyNineBY_2379757 : Nat.Prime 2379757 := by norm_num
private theorem prime_seventyNineBY_2381317 : Nat.Prime 2381317 := by norm_num
private theorem prime_seventyNineBY_2417477 : Nat.Prime 2417477 := by norm_num
private theorem prime_seventyNineBY_2488223 : Nat.Prime 2488223 := by norm_num
private theorem prime_seventyNineBY_2510303 : Nat.Prime 2510303 := by norm_num
private theorem prime_seventyNineBY_2515673 : Nat.Prime 2515673 := by norm_num
private theorem prime_seventyNineBY_2693443 : Nat.Prime 2693443 := by norm_num
private theorem prime_seventyNineBY_2772331 : Nat.Prime 2772331 := by norm_num
private theorem prime_seventyNineBY_2784973 : Nat.Prime 2784973 := by norm_num
private theorem prime_seventyNineBY_2802853 : Nat.Prime 2802853 := by norm_num
private theorem prime_seventyNineBY_2889877 : Nat.Prime 2889877 := by norm_num
private theorem prime_seventyNineBY_3046577 : Nat.Prime 3046577 := by norm_num
private theorem prime_seventyNineBY_3106783 : Nat.Prime 3106783 := by norm_num
private theorem prime_seventyNineBY_3467039 : Nat.Prime 3467039 := by norm_num
private theorem prime_seventyNineBY_3486631 : Nat.Prime 3486631 := by norm_num
private theorem prime_seventyNineBY_3558829 : Nat.Prime 3558829 := by norm_num
private theorem prime_seventyNineBY_3652153 : Nat.Prime 3652153 := by norm_num
private theorem prime_seventyNineBY_3697081 : Nat.Prime 3697081 := by norm_num
private theorem prime_seventyNineBY_3730147 : Nat.Prime 3730147 := by norm_num
private theorem prime_seventyNineBY_3878389 : Nat.Prime 3878389 := by norm_num
private theorem prime_seventyNineBY_3996541 : Nat.Prime 3996541 := by norm_num
private theorem prime_seventyNineBY_4487789 : Nat.Prime 4487789 := by norm_num
private theorem prime_seventyNineBY_4771297 : Nat.Prime 4771297 := by norm_num
private theorem prime_seventyNineBY_4874747 : Nat.Prime 4874747 := by norm_num
private theorem prime_seventyNineBY_5149853 : Nat.Prime 5149853 := by norm_num
private theorem prime_seventyNineBY_5471393 : Nat.Prime 5471393 := by norm_num
private theorem prime_seventyNineBY_5550439 : Nat.Prime 5550439 := by norm_num
private theorem prime_seventyNineBY_5707183 : Nat.Prime 5707183 := by norm_num
private theorem prime_seventyNineBY_5731777 : Nat.Prime 5731777 := by norm_num
private theorem prime_seventyNineBY_7516693 : Nat.Prime 7516693 := by norm_num
private theorem prime_seventyNineBY_8385389 : Nat.Prime 8385389 := by norm_num
private theorem prime_seventyNineBY_8620231 : Nat.Prime 8620231 := by norm_num
private theorem prime_seventyNineBY_8771599 : Nat.Prime 8771599 := by norm_num
private theorem prime_seventyNineBY_8894563 : Nat.Prime 8894563 := by norm_num
private theorem prime_seventyNineBY_8946317 : Nat.Prime 8946317 := by norm_num
private theorem prime_seventyNineBY_10307849 : Nat.Prime 10307849 := by norm_num
private theorem prime_seventyNineBY_10543523 : Nat.Prime 10543523 := by norm_num
private theorem prime_seventyNineBY_11630029 : Nat.Prime 11630029 := by norm_num
private theorem prime_seventyNineBY_11766427 : Nat.Prime 11766427 := by norm_num
private theorem prime_seventyNineBY_12741923 : Nat.Prime 12741923 := by norm_num
private theorem prime_seventyNineBY_12760679 : Nat.Prime 12760679 := by norm_num
private theorem prime_seventyNineBY_13186819 : Nat.Prime 13186819 := by norm_num
private theorem prime_seventyNineBY_13908359 : Nat.Prime 13908359 := by norm_num
private theorem prime_seventyNineBY_14565101 : Nat.Prime 14565101 := by norm_num
private theorem prime_seventyNineBY_14869223 : Nat.Prime 14869223 := by norm_num
private theorem prime_seventyNineBY_15076681 : Nat.Prime 15076681 := by norm_num
private theorem prime_seventyNineBY_15167641 : Nat.Prime 15167641 := by norm_num
private theorem prime_seventyNineBY_16509343 : Nat.Prime 16509343 := by norm_num
private theorem prime_seventyNineBY_18267869 : Nat.Prime 18267869 := by norm_num
private theorem prime_seventyNineBY_18335633 : Nat.Prime 18335633 := by norm_num
private theorem prime_seventyNineBY_18661469 : Nat.Prime 18661469 := by norm_num
private theorem prime_seventyNineBY_18764111 : Nat.Prime 18764111 := by norm_num
private theorem prime_seventyNineBY_19994309 : Nat.Prime 19994309 := by norm_num
private theorem prime_seventyNineBY_20305063 : Nat.Prime 20305063 := by norm_num
private theorem prime_seventyNineBY_20910793 : Nat.Prime 20910793 := by norm_num
private theorem prime_seventyNineBY_21951731 : Nat.Prime 21951731 := by norm_num
private theorem prime_seventyNineBY_23278043 : Nat.Prime 23278043 := by norm_num
private theorem prime_seventyNineBY_24879053 : Nat.Prime 24879053 := by norm_num
private theorem prime_seventyNineBY_25779779 : Nat.Prime 25779779 := by norm_num
private theorem prime_seventyNineBY_26117363 : Nat.Prime 26117363 := by norm_num
private theorem prime_seventyNineBY_26969743 : Nat.Prime 26969743 := by norm_num
private theorem prime_seventyNineBY_27984641 : Nat.Prime 27984641 := by norm_num
private theorem prime_seventyNineBY_29185817 : Nat.Prime 29185817 := by norm_num
private theorem prime_seventyNineBY_30236483 : Nat.Prime 30236483 := by
  apply lucas_primality 30236483 (2 : ZMod 30236483)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (351587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (351587, 1)] : List FactorBlock).map factorBlockValue).prod) = 30236483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_43
      · exact prime_seventyNineBY_351587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30236483) ^ 15118241 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 30236483) ^ 703174 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 30236483) ^ 86 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_30354557 : Nat.Prime 30354557 := by
  apply lucas_primality 30354557 (2 : ZMod 30354557)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (59, 1), (128621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (59, 1), (128621, 1)] : List FactorBlock).map factorBlockValue).prod) = 30354557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_59
      · exact prime_seventyNineBY_128621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30354557) ^ 15177278 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 30354557) ^ 514484 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 30354557) ^ 236 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_33077437 : Nat.Prime 33077437 := by
  apply lucas_primality 33077437 (11 : ZMod 33077437)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (393779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (393779, 1)] : List FactorBlock).map factorBlockValue).prod) = 33077437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_393779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 33077437) ^ 16538718 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (11 : ZMod 33077437) ^ 11025812 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (11 : ZMod 33077437) ^ 4725348 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (11 : ZMod 33077437) ^ 84 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_33987221 : Nat.Prime 33987221 := by
  apply lucas_primality 33987221 (2 : ZMod 33987221)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1699361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1699361, 1)] : List FactorBlock).map factorBlockValue).prod) = 33987221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_1699361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 33987221) ^ 16993610 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 33987221) ^ 6797444 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 33987221) ^ 20 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_36259649 : Nat.Prime 36259649 := by
  apply lucas_primality 36259649 (3 : ZMod 36259649)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (566557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (566557, 1)] : List FactorBlock).map factorBlockValue).prod) = 36259649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_566557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 36259649) ^ 18129824 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 36259649) ^ 64 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_36535739 : Nat.Prime 36535739 := by
  apply lucas_primality 36535739 (2 : ZMod 36535739)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (18267869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (18267869, 1)] : List FactorBlock).map factorBlockValue).prod) = 36535739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_18267869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 36535739) ^ 18267869 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 36535739) ^ 2 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_37429571 : Nat.Prime 37429571 := by
  apply lucas_primality 37429571 (2 : ZMod 37429571)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37, 1), (101161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37, 1), (101161, 1)] : List FactorBlock).map factorBlockValue).prod) = 37429571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_37
      · exact prime_seventyNineBY_101161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 37429571) ^ 18714785 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 37429571) ^ 7485914 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 37429571) ^ 1011610 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 37429571) ^ 370 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_37528223 : Nat.Prime 37528223 := by
  apply lucas_primality 37528223 (5 : ZMod 37528223)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (18764111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (18764111, 1)] : List FactorBlock).map factorBlockValue).prod) = 37528223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_18764111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 37528223) ^ 18764111 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 37528223) ^ 2 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_38915167 : Nat.Prime 38915167 := by
  apply lucas_primality 38915167 (3 : ZMod 38915167)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (113, 1), (57397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (113, 1), (57397, 1)] : List FactorBlock).map factorBlockValue).prod) = 38915167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_113
      · exact prime_seventyNineBY_57397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 38915167) ^ 19457583 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 38915167) ^ 12971722 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 38915167) ^ 344382 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 38915167) ^ 678 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_41703989 : Nat.Prime 41703989 := by
  apply lucas_primality 41703989 (2 : ZMod 41703989)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1009, 1), (10333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1009, 1), (10333, 1)] : List FactorBlock).map factorBlockValue).prod) = 41703989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_1009
      · exact prime_seventyNineBY_10333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 41703989) ^ 20851994 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 41703989) ^ 41332 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 41703989) ^ 4036 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_47328773 : Nat.Prime 47328773 := by
  apply lucas_primality 47328773 (2 : ZMod 47328773)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (37, 1), (16831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (37, 1), (16831, 1)] : List FactorBlock).map factorBlockValue).prod) = 47328773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_19
      · exact prime_seventyNineBY_37
      · exact prime_seventyNineBY_16831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 47328773) ^ 23664386 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 47328773) ^ 2490988 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 47328773) ^ 1279156 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 47328773) ^ 2812 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_48779611 : Nat.Prime 48779611 := by
  apply lucas_primality 48779611 (14 : ZMod 48779611)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (53, 1), (2789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (53, 1), (2789, 1)] : List FactorBlock).map factorBlockValue).prod) = 48779611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_11
      · exact prime_seventyNineBY_53
      · exact prime_seventyNineBY_2789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 48779611) ^ 24389805 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (14 : ZMod 48779611) ^ 16259870 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (14 : ZMod 48779611) ^ 9755922 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (14 : ZMod 48779611) ^ 4434510 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (14 : ZMod 48779611) ^ 920370 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (14 : ZMod 48779611) ^ 17490 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_51932173 : Nat.Prime 51932173 := by
  apply lucas_primality 51932173 (2 : ZMod 51932173)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (281, 1), (15401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (281, 1), (15401, 1)] : List FactorBlock).map factorBlockValue).prod) = 51932173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_281
      · exact prime_seventyNineBY_15401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 51932173) ^ 25966086 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 51932173) ^ 17310724 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 51932173) ^ 184812 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 51932173) ^ 3372 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_52954849 : Nat.Prime 52954849 := by
  apply lucas_primality 52954849 (7 : ZMod 52954849)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (183871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (183871, 1)] : List FactorBlock).map factorBlockValue).prod) = 52954849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_183871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 52954849) ^ 26477424 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 52954849) ^ 17651616 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 52954849) ^ 288 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_55017503 : Nat.Prime 55017503 := by
  apply lucas_primality 55017503 (5 : ZMod 55017503)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (773, 1), (1873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (773, 1), (1873, 1)] : List FactorBlock).map factorBlockValue).prod) = 55017503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_19
      · exact prime_seventyNineBY_773
      · exact prime_seventyNineBY_1873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 55017503) ^ 27508751 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 55017503) ^ 2895658 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 55017503) ^ 71174 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 55017503) ^ 29374 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_57663869 : Nat.Prime 57663869 := by
  apply lucas_primality 57663869 (2 : ZMod 57663869)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (73, 1), (197479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (73, 1), (197479, 1)] : List FactorBlock).map factorBlockValue).prod) = 57663869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_73
      · exact prime_seventyNineBY_197479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 57663869) ^ 28831934 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 57663869) ^ 789916 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 57663869) ^ 292 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_67652813 : Nat.Prime 67652813 := by
  apply lucas_primality 67652813 (2 : ZMod 67652813)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (109, 1), (155167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (109, 1), (155167, 1)] : List FactorBlock).map factorBlockValue).prod) = 67652813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_109
      · exact prime_seventyNineBY_155167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 67652813) ^ 33826406 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 67652813) ^ 620668 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 67652813) ^ 436 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_84403243 : Nat.Prime 84403243 := by
  apply lucas_primality 84403243 (2 : ZMod 84403243)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (11, 1), (53, 1), (383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (11, 1), (53, 1), (383, 1)] : List FactorBlock).map factorBlockValue).prod) = 84403243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_11
      · exact prime_seventyNineBY_53
      · exact prime_seventyNineBY_383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 84403243) ^ 42201621 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 84403243) ^ 28134414 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 84403243) ^ 12057606 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 84403243) ^ 7673022 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 84403243) ^ 1592514 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 84403243) ^ 220374 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_89025941 : Nat.Prime 89025941 := by
  apply lucas_primality 89025941 (12 : ZMod 89025941)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 1), (29, 1), (9029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 1), (29, 1), (9029, 1)] : List FactorBlock).map factorBlockValue).prod) = 89025941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_17
      · exact prime_seventyNineBY_29
      · exact prime_seventyNineBY_9029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 89025941) ^ 44512970 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (12 : ZMod 89025941) ^ 17805188 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (12 : ZMod 89025941) ^ 5236820 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (12 : ZMod 89025941) ^ 3069860 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (12 : ZMod 89025941) ^ 9860 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_91708433 : Nat.Prime 91708433 := by
  apply lucas_primality 91708433 (3 : ZMod 91708433)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5731777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5731777, 1)] : List FactorBlock).map factorBlockValue).prod) = 91708433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_5731777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 91708433) ^ 45854216 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 91708433) ^ 16 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_124528007 : Nat.Prime 124528007 := by
  apply lucas_primality 124528007 (5 : ZMod 124528007)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (827, 1), (75289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (827, 1), (75289, 1)] : List FactorBlock).map factorBlockValue).prod) = 124528007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_827
      · exact prime_seventyNineBY_75289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 124528007) ^ 62264003 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 124528007) ^ 150578 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 124528007) ^ 1654 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_125906461 : Nat.Prime 125906461 := by
  apply lucas_primality 125906461 (2 : ZMod 125906461)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (2098441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (2098441, 1)] : List FactorBlock).map factorBlockValue).prod) = 125906461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_2098441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 125906461) ^ 62953230 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 125906461) ^ 41968820 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 125906461) ^ 25181292 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 125906461) ^ 60 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_135305627 : Nat.Prime 135305627 := by
  apply lucas_primality 135305627 (2 : ZMod 135305627)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67652813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67652813, 1)] : List FactorBlock).map factorBlockValue).prod) = 135305627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_67652813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 135305627) ^ 67652813 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 135305627) ^ 2 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_139340489 : Nat.Prime 139340489 := by
  apply lucas_primality 139340489 (3 : ZMod 139340489)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (2488223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (2488223, 1)] : List FactorBlock).map factorBlockValue).prod) = 139340489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_2488223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 139340489) ^ 69670244 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 139340489) ^ 19905784 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 139340489) ^ 56 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_144184451 : Nat.Prime 144184451 := by
  apply lucas_primality 144184451 (2 : ZMod 144184451)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (89, 1), (32401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (89, 1), (32401, 1)] : List FactorBlock).map factorBlockValue).prod) = 144184451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_89
      · exact prime_seventyNineBY_32401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 144184451) ^ 72092225 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 144184451) ^ 28836890 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 144184451) ^ 1620050 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 144184451) ^ 4450 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_144895181 : Nat.Prime 144895181 := by
  apply lucas_primality 144895181 (3 : ZMod 144895181)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (941, 1), (7699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (941, 1), (7699, 1)] : List FactorBlock).map factorBlockValue).prod) = 144895181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_941
      · exact prime_seventyNineBY_7699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 144895181) ^ 72447590 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 144895181) ^ 28979036 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 144895181) ^ 153980 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 144895181) ^ 18820 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_146413213 : Nat.Prime 146413213 := by
  apply lucas_primality 146413213 (2 : ZMod 146413213)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (307, 1), (3613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (307, 1), (3613, 1)] : List FactorBlock).map factorBlockValue).prod) = 146413213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_11
      · exact prime_seventyNineBY_307
      · exact prime_seventyNineBY_3613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 146413213) ^ 73206606 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 146413213) ^ 48804404 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 146413213) ^ 13310292 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 146413213) ^ 476916 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 146413213) ^ 40524 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_166339861 : Nat.Prime 166339861 := by
  apply lucas_primality 166339861 (10 : ZMod 166339861)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (2772331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (2772331, 1)] : List FactorBlock).map factorBlockValue).prod) = 166339861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_2772331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 166339861) ^ 83169930 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (10 : ZMod 166339861) ^ 55446620 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (10 : ZMod 166339861) ^ 33267972 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (10 : ZMod 166339861) ^ 60 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_167907847 : Nat.Prime 167907847 := by
  apply lucas_primality 167907847 (3 : ZMod 167907847)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (27984641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (27984641, 1)] : List FactorBlock).map factorBlockValue).prod) = 167907847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_27984641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 167907847) ^ 83953923 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 167907847) ^ 55969282 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 167907847) ^ 6 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_172066493 : Nat.Prime 172066493 := by
  apply lucas_primality 172066493 (2 : ZMod 172066493)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (31, 1), (173, 1), (617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (31, 1), (173, 1), (617, 1)] : List FactorBlock).map factorBlockValue).prod) = 172066493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_13
      · exact prime_seventyNineBY_31
      · exact prime_seventyNineBY_173
      · exact prime_seventyNineBY_617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 172066493) ^ 86033246 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 172066493) ^ 13235884 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 172066493) ^ 5550532 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 172066493) ^ 994604 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 172066493) ^ 278876 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_183416867 : Nat.Prime 183416867 := by
  apply lucas_primality 183416867 (2 : ZMod 183416867)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (91708433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (91708433, 1)] : List FactorBlock).map factorBlockValue).prod) = 183416867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_91708433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 183416867) ^ 91708433 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 183416867) ^ 2 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_221362769 : Nat.Prime 221362769 := by
  apply lucas_primality 221362769 (6 : ZMod 221362769)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (19, 1), (53, 1), (1249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (19, 1), (53, 1), (1249, 1)] : List FactorBlock).map factorBlockValue).prod) = 221362769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_11
      · exact prime_seventyNineBY_19
      · exact prime_seventyNineBY_53
      · exact prime_seventyNineBY_1249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 221362769) ^ 110681384 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 221362769) ^ 20123888 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 221362769) ^ 11650672 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 221362769) ^ 4176656 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 221362769) ^ 177232 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_227558351 : Nat.Prime 227558351 := by
  apply lucas_primality 227558351 (11 : ZMod 227558351)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (367, 1), (12401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (367, 1), (12401, 1)] : List FactorBlock).map factorBlockValue).prod) = 227558351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_367
      · exact prime_seventyNineBY_12401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 227558351) ^ 113779175 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (11 : ZMod 227558351) ^ 45511670 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (11 : ZMod 227558351) ^ 620050 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (11 : ZMod 227558351) ^ 18350 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_230187037 : Nat.Prime 230187037 := by
  apply lucas_primality 230187037 (2 : ZMod 230187037)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (29, 1), (28759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (29, 1), (28759, 1)] : List FactorBlock).map factorBlockValue).prod) = 230187037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_23
      · exact prime_seventyNineBY_29
      · exact prime_seventyNineBY_28759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 230187037) ^ 115093518 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 230187037) ^ 76729012 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 230187037) ^ 10008132 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 230187037) ^ 7937484 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 230187037) ^ 8004 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_241658617 : Nat.Prime 241658617 := by
  apply lucas_primality 241658617 (10 : ZMod 241658617)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (73, 1), (137933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (73, 1), (137933, 1)] : List FactorBlock).map factorBlockValue).prod) = 241658617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_73
      · exact prime_seventyNineBY_137933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 241658617) ^ 120829308 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (10 : ZMod 241658617) ^ 80552872 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (10 : ZMod 241658617) ^ 3310392 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (10 : ZMod 241658617) ^ 1752 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_242836457 : Nat.Prime 242836457 := by
  apply lucas_primality 242836457 (3 : ZMod 242836457)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (30354557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (30354557, 1)] : List FactorBlock).map factorBlockValue).prod) = 242836457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_30354557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 242836457) ^ 121418228 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 242836457) ^ 8 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_245577671 : Nat.Prime 245577671 := by
  apply lucas_primality 245577671 (11 : ZMod 245577671)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (23, 2), (3571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (23, 2), (3571, 1)] : List FactorBlock).map factorBlockValue).prod) = 245577671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_13
      · exact prime_seventyNineBY_23
      · exact prime_seventyNineBY_3571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 245577671) ^ 122788835 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (11 : ZMod 245577671) ^ 49115534 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (11 : ZMod 245577671) ^ 18890590 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (11 : ZMod 245577671) ^ 10677290 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (11 : ZMod 245577671) ^ 68770 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_245981377 : Nat.Prime 245981377 := by
  apply lucas_primality 245981377 (7 : ZMod 245981377)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (509, 1), (839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (509, 1), (839, 1)] : List FactorBlock).map factorBlockValue).prod) = 245981377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_509
      · exact prime_seventyNineBY_839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 245981377) ^ 122990688 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 245981377) ^ 81993792 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 245981377) ^ 483264 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 245981377) ^ 293184 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_289594309 : Nat.Prime 289594309 := by
  apply lucas_primality 289594309 (2 : ZMod 289594309)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1483, 1), (16273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1483, 1), (16273, 1)] : List FactorBlock).map factorBlockValue).prod) = 289594309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_1483
      · exact prime_seventyNineBY_16273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 289594309) ^ 144797154 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 289594309) ^ 96531436 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 289594309) ^ 195276 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 289594309) ^ 17796 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_302988503 : Nat.Prime 302988503 := by
  apply lucas_primality 302988503 (5 : ZMod 302988503)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4877, 1), (31063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4877, 1), (31063, 1)] : List FactorBlock).map factorBlockValue).prod) = 302988503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_4877
      · exact prime_seventyNineBY_31063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 302988503) ^ 151494251 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 302988503) ^ 62126 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 302988503) ^ 9754 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_350744311 : Nat.Prime 350744311 := by
  apply lucas_primality 350744311 (7 : ZMod 350744311)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (7, 1), (151, 1), (1229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (7, 1), (151, 1), (1229, 1)] : List FactorBlock).map factorBlockValue).prod) = 350744311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_151
      · exact prime_seventyNineBY_1229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 350744311) ^ 175372155 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 350744311) ^ 116914770 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 350744311) ^ 70148862 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 350744311) ^ 50106330 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 350744311) ^ 2322810 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 350744311) ^ 285390 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_389151671 : Nat.Prime 389151671 := by
  apply lucas_primality 389151671 (38 : ZMod 389151671)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (38915167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (38915167, 1)] : List FactorBlock).map factorBlockValue).prod) = 389151671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_38915167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (38 : ZMod 389151671) ^ 194575835 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (38 : ZMod 389151671) ^ 77830334 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (38 : ZMod 389151671) ^ 10 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_407563301 : Nat.Prime 407563301 := by
  apply lucas_primality 407563301 (2 : ZMod 407563301)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (19, 1), (214507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (19, 1), (214507, 1)] : List FactorBlock).map factorBlockValue).prod) = 407563301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_19
      · exact prime_seventyNineBY_214507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 407563301) ^ 203781650 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 407563301) ^ 81512660 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 407563301) ^ 21450700 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 407563301) ^ 1900 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_411018967 : Nat.Prime 411018967 := by
  apply lucas_primality 411018967 (3 : ZMod 411018967)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1451, 1), (15737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1451, 1), (15737, 1)] : List FactorBlock).map factorBlockValue).prod) = 411018967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_1451
      · exact prime_seventyNineBY_15737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 411018967) ^ 205509483 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 411018967) ^ 137006322 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 411018967) ^ 283266 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 411018967) ^ 26118 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_460178041 : Nat.Prime 460178041 := by
  apply lucas_primality 460178041 (23 : ZMod 460178041)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (547831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (547831, 1)] : List FactorBlock).map factorBlockValue).prod) = 460178041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_547831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 460178041) ^ 230089020 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (23 : ZMod 460178041) ^ 153392680 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (23 : ZMod 460178041) ^ 92035608 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (23 : ZMod 460178041) ^ 65739720 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (23 : ZMod 460178041) ^ 840 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_483613511 : Nat.Prime 483613511 := by
  apply lucas_primality 483613511 (17 : ZMod 483613511)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (79, 1), (612169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (79, 1), (612169, 1)] : List FactorBlock).map factorBlockValue).prod) = 483613511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_79
      · exact prime_seventyNineBY_612169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 483613511) ^ 241806755 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (17 : ZMod 483613511) ^ 96722702 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (17 : ZMod 483613511) ^ 6121690 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (17 : ZMod 483613511) ^ 790 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_513385283 : Nat.Prime 513385283 := by
  apply lucas_primality 513385283 (5 : ZMod 513385283)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (349, 1), (38711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (349, 1), (38711, 1)] : List FactorBlock).map factorBlockValue).prod) = 513385283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_19
      · exact prime_seventyNineBY_349
      · exact prime_seventyNineBY_38711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 513385283) ^ 256692641 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 513385283) ^ 27020278 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 513385283) ^ 1471018 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 513385283) ^ 13262 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_513895169 : Nat.Prime 513895169 := by
  apply lucas_primality 513895169 (3 : ZMod 513895169)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (2007403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (2007403, 1)] : List FactorBlock).map factorBlockValue).prod) = 513895169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_2007403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 513895169) ^ 256947584 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 513895169) ^ 256 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_755438767 : Nat.Prime 755438767 := by
  apply lucas_primality 755438767 (3 : ZMod 755438767)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (125906461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (125906461, 1)] : List FactorBlock).map factorBlockValue).prod) = 755438767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_125906461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 755438767) ^ 377719383 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 755438767) ^ 251812922 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 755438767) ^ 6 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_778303343 : Nat.Prime 778303343 := by
  apply lucas_primality 778303343 (5 : ZMod 778303343)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (389151671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (389151671, 1)] : List FactorBlock).map factorBlockValue).prod) = 778303343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_389151671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 778303343) ^ 389151671 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 778303343) ^ 2 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_851953007 : Nat.Prime 851953007 := by
  apply lucas_primality 851953007 (5 : ZMod 851953007)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (179, 1), (2379757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (179, 1), (2379757, 1)] : List FactorBlock).map factorBlockValue).prod) = 851953007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_179
      · exact prime_seventyNineBY_2379757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 851953007) ^ 425976503 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 851953007) ^ 4759514 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 851953007) ^ 358 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_871260007 : Nat.Prime 871260007 := by
  apply lucas_primality 871260007 (3 : ZMod 871260007)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2731, 1), (53171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2731, 1), (53171, 1)] : List FactorBlock).map factorBlockValue).prod) = 871260007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_2731
      · exact prime_seventyNineBY_53171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 871260007) ^ 435630003 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 871260007) ^ 290420002 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 871260007) ^ 319026 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 871260007) ^ 16386 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_920804393 : Nat.Prime 920804393 := by
  apply lucas_primality 920804393 (3 : ZMod 920804393)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (349, 1), (329801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (349, 1), (329801, 1)] : List FactorBlock).map factorBlockValue).prod) = 920804393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_349
      · exact prime_seventyNineBY_329801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 920804393) ^ 460402196 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 920804393) ^ 2638408 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 920804393) ^ 2792 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_946382137 : Nat.Prime 946382137 := by
  apply lucas_primality 946382137 (10 : ZMod 946382137)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (31, 1), (181717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (31, 1), (181717, 1)] : List FactorBlock).map factorBlockValue).prod) = 946382137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_31
      · exact prime_seventyNineBY_181717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 946382137) ^ 473191068 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (10 : ZMod 946382137) ^ 315460712 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (10 : ZMod 946382137) ^ 135197448 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (10 : ZMod 946382137) ^ 30528456 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (10 : ZMod 946382137) ^ 5208 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_1032398959 : Nat.Prime 1032398959 := by
  apply lucas_primality 1032398959 (6 : ZMod 1032398959)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (172066493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (172066493, 1)] : List FactorBlock).map factorBlockValue).prod) = 1032398959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_172066493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 1032398959) ^ 516199479 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1032398959) ^ 344132986 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1032398959) ^ 6 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_1086549553 : Nat.Prime 1086549553 := by
  apply lucas_primality 1086549553 (7 : ZMod 1086549553)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (11, 1), (199, 1), (383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (11, 1), (199, 1), (383, 1)] : List FactorBlock).map factorBlockValue).prod) = 1086549553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_11
      · exact prime_seventyNineBY_199
      · exact prime_seventyNineBY_383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1086549553) ^ 543274776 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 1086549553) ^ 362183184 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 1086549553) ^ 98777232 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 1086549553) ^ 5460048 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 1086549553) ^ 2836944 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_1233327703 : Nat.Prime 1233327703 := by
  apply lucas_primality 1233327703 (3 : ZMod 1233327703)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (53, 1), (3878389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (53, 1), (3878389, 1)] : List FactorBlock).map factorBlockValue).prod) = 1233327703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_53
      · exact prime_seventyNineBY_3878389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1233327703) ^ 616663851 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1233327703) ^ 411109234 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1233327703) ^ 23270334 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1233327703) ^ 318 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_1408251209 : Nat.Prime 1408251209 := by
  apply lucas_primality 1408251209 (3 : ZMod 1408251209)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (13, 1), (1934411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (13, 1), (1934411, 1)] : List FactorBlock).map factorBlockValue).prod) = 1408251209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_13
      · exact prime_seventyNineBY_1934411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1408251209) ^ 704125604 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1408251209) ^ 201178744 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1408251209) ^ 108327016 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1408251209) ^ 728 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_1579327507 : Nat.Prime 1579327507 := by
  apply lucas_primality 1579327507 (3 : ZMod 1579327507)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (101, 1), (137, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (101, 1), (137, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod) = 1579327507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_17
      · exact prime_seventyNineBY_101
      · exact prime_seventyNineBY_137
      · exact prime_seventyNineBY_373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1579327507) ^ 789663753 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1579327507) ^ 526442502 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1579327507) ^ 92901618 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1579327507) ^ 15636906 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1579327507) ^ 11527938 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1579327507) ^ 4234122 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_1762145767 : Nat.Prime 1762145767 := by
  apply lucas_primality 1762145767 (5 : ZMod 1762145767)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (19, 1), (572497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (19, 1), (572497, 1)] : List FactorBlock).map factorBlockValue).prod) = 1762145767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_19
      · exact prime_seventyNineBY_572497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1762145767) ^ 881072883 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1762145767) ^ 587381922 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1762145767) ^ 92744514 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1762145767) ^ 3078 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_1768513427 : Nat.Prime 1768513427 := by
  apply lucas_primality 1768513427 (2 : ZMod 1768513427)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (193, 1), (293, 1), (823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (193, 1), (293, 1), (823, 1)] : List FactorBlock).map factorBlockValue).prod) = 1768513427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_19
      · exact prime_seventyNineBY_193
      · exact prime_seventyNineBY_293
      · exact prime_seventyNineBY_823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1768513427) ^ 884256713 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1768513427) ^ 93079654 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1768513427) ^ 9163282 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1768513427) ^ 6035882 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1768513427) ^ 2148862 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_1771373161 : Nat.Prime 1771373161 := by
  apply lucas_primality 1771373161 (7 : ZMod 1771373161)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (163, 1), (30187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (163, 1), (30187, 1)] : List FactorBlock).map factorBlockValue).prod) = 1771373161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_163
      · exact prime_seventyNineBY_30187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1771373161) ^ 885686580 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 1771373161) ^ 590457720 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 1771373161) ^ 354274632 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 1771373161) ^ 10867320 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 1771373161) ^ 58680 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_1783904461 : Nat.Prime 1783904461 := by
  apply lucas_primality 1783904461 (2 : ZMod 1783904461)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 1), (2287057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 1), (2287057, 1)] : List FactorBlock).map factorBlockValue).prod) = 1783904461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_13
      · exact prime_seventyNineBY_2287057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1783904461) ^ 891952230 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1783904461) ^ 594634820 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1783904461) ^ 356780892 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1783904461) ^ 137223420 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1783904461) ^ 780 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_1919242993 : Nat.Prime 1919242993 := by
  apply lucas_primality 1919242993 (5 : ZMod 1919242993)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (89, 1), (449261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (89, 1), (449261, 1)] : List FactorBlock).map factorBlockValue).prod) = 1919242993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_89
      · exact prime_seventyNineBY_449261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1919242993) ^ 959621496 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1919242993) ^ 639747664 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1919242993) ^ 21564528 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1919242993) ^ 4272 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_1939676933 : Nat.Prime 1939676933 := by
  apply lucas_primality 1939676933 (2 : ZMod 1939676933)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (241, 1), (2012113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (241, 1), (2012113, 1)] : List FactorBlock).map factorBlockValue).prod) = 1939676933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_241
      · exact prime_seventyNineBY_2012113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1939676933) ^ 969838466 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1939676933) ^ 8048452 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1939676933) ^ 964 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_2030770127 : Nat.Prime 2030770127 := by
  apply lucas_primality 2030770127 (5 : ZMod 2030770127)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (13186819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (13186819, 1)] : List FactorBlock).map factorBlockValue).prod) = 2030770127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_11
      · exact prime_seventyNineBY_13186819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2030770127) ^ 1015385063 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2030770127) ^ 290110018 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2030770127) ^ 184615466 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2030770127) ^ 154 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_2046314483 : Nat.Prime 2046314483 := by
  apply lucas_primality 2046314483 (2 : ZMod 2046314483)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (3943, 1), (5521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (3943, 1), (5521, 1)] : List FactorBlock).map factorBlockValue).prod) = 2046314483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_47
      · exact prime_seventyNineBY_3943
      · exact prime_seventyNineBY_5521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2046314483) ^ 1023157241 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2046314483) ^ 43538606 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2046314483) ^ 518974 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2046314483) ^ 370642 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_2153805023 : Nat.Prime 2153805023 := by
  apply lucas_primality 2153805023 (5 : ZMod 2153805023)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (15167641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (15167641, 1)] : List FactorBlock).map factorBlockValue).prod) = 2153805023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_71
      · exact prime_seventyNineBY_15167641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2153805023) ^ 1076902511 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2153805023) ^ 30335282 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2153805023) ^ 142 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_2197520723 : Nat.Prime 2197520723 := by
  apply lucas_primality 2197520723 (2 : ZMod 2197520723)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (13908359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (13908359, 1)] : List FactorBlock).map factorBlockValue).prod) = 2197520723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_79
      · exact prime_seventyNineBY_13908359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2197520723) ^ 1098760361 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2197520723) ^ 27816718 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2197520723) ^ 158 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_2204720521 : Nat.Prime 2204720521 := by
  apply lucas_primality 2204720521 (7 : ZMod 2204720521)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (1103, 1), (16657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (1103, 1), (16657, 1)] : List FactorBlock).map factorBlockValue).prod) = 2204720521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_1103
      · exact prime_seventyNineBY_16657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2204720521) ^ 1102360260 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2204720521) ^ 734906840 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2204720521) ^ 440944104 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2204720521) ^ 1998840 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2204720521) ^ 132360 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_2698563047 : Nat.Prime 2698563047 := by
  apply lucas_primality 2698563047 (5 : ZMod 2698563047)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (101, 1), (703117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (101, 1), (703117, 1)] : List FactorBlock).map factorBlockValue).prod) = 2698563047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_19
      · exact prime_seventyNineBY_101
      · exact prime_seventyNineBY_703117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2698563047) ^ 1349281523 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2698563047) ^ 142029634 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2698563047) ^ 26718446 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2698563047) ^ 3838 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_2843011943 : Nat.Prime 2843011943 := by
  apply lucas_primality 2843011943 (5 : ZMod 2843011943)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3163, 1), (449417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3163, 1), (449417, 1)] : List FactorBlock).map factorBlockValue).prod) = 2843011943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3163
      · exact prime_seventyNineBY_449417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2843011943) ^ 1421505971 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2843011943) ^ 898834 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2843011943) ^ 6326 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_2890770011 : Nat.Prime 2890770011 := by
  apply lucas_primality 2890770011 (2 : ZMod 2890770011)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (3797, 1), (4007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (3797, 1), (4007, 1)] : List FactorBlock).map factorBlockValue).prod) = 2890770011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_19
      · exact prime_seventyNineBY_3797
      · exact prime_seventyNineBY_4007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2890770011) ^ 1445385005 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2890770011) ^ 578154002 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2890770011) ^ 152145790 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2890770011) ^ 761330 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2890770011) ^ 721430 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_3021762923 : Nat.Prime 3021762923 := by
  apply lucas_primality 3021762923 (2 : ZMod 3021762923)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2593, 1), (582677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2593, 1), (582677, 1)] : List FactorBlock).map factorBlockValue).prod) = 3021762923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_2593
      · exact prime_seventyNineBY_582677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3021762923) ^ 1510881461 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3021762923) ^ 1165354 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3021762923) ^ 5186 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_3635252111 : Nat.Prime 3635252111 := by
  apply lucas_primality 3635252111 (7 : ZMod 3635252111)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (51932173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (51932173, 1)] : List FactorBlock).map factorBlockValue).prod) = 3635252111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_51932173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 3635252111) ^ 1817626055 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 3635252111) ^ 727050422 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 3635252111) ^ 519321730 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 3635252111) ^ 70 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_4267390129 : Nat.Prime 4267390129 := by
  apply lucas_primality 4267390129 (11 : ZMod 4267390129)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (521, 1), (170641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (521, 1), (170641, 1)] : List FactorBlock).map factorBlockValue).prod) = 4267390129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_521
      · exact prime_seventyNineBY_170641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 4267390129) ^ 2133695064 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (11 : ZMod 4267390129) ^ 1422463376 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (11 : ZMod 4267390129) ^ 8190768 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (11 : ZMod 4267390129) ^ 25008 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_4295580931 : Nat.Prime 4295580931 := by
  apply lucas_primality 4295580931 (2 : ZMod 4295580931)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (1831, 1), (8689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (1831, 1), (8689, 1)] : List FactorBlock).map factorBlockValue).prod) = 4295580931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_1831
      · exact prime_seventyNineBY_8689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4295580931) ^ 2147790465 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4295580931) ^ 1431860310 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4295580931) ^ 859116186 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4295580931) ^ 2346030 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4295580931) ^ 494370 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_4373808169 : Nat.Prime 4373808169 := by
  apply lucas_primality 4373808169 (7 : ZMod 4373808169)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (41, 1), (89, 1), (49943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (41, 1), (89, 1), (49943, 1)] : List FactorBlock).map factorBlockValue).prod) = 4373808169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_41
      · exact prime_seventyNineBY_89
      · exact prime_seventyNineBY_49943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4373808169) ^ 2186904084 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 4373808169) ^ 1457936056 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 4373808169) ^ 106678248 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 4373808169) ^ 49143912 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 4373808169) ^ 87576 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_4657438129 : Nat.Prime 4657438129 := by
  apply lucas_primality 4657438129 (26 : ZMod 4657438129)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (739, 1), (18757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (739, 1), (18757, 1)] : List FactorBlock).map factorBlockValue).prod) = 4657438129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_739
      · exact prime_seventyNineBY_18757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 4657438129) ^ 2328719064 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (26 : ZMod 4657438129) ^ 1552479376 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (26 : ZMod 4657438129) ^ 665348304 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (26 : ZMod 4657438129) ^ 6302352 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (26 : ZMod 4657438129) ^ 248304 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_5600482861 : Nat.Prime 5600482861 := by
  apply lucas_primality 5600482861 (2 : ZMod 5600482861)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (103, 1), (129461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (103, 1), (129461, 1)] : List FactorBlock).map factorBlockValue).prod) = 5600482861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_103
      · exact prime_seventyNineBY_129461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5600482861) ^ 2800241430 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 5600482861) ^ 1866827620 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 5600482861) ^ 1120096572 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 5600482861) ^ 800068980 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 5600482861) ^ 54373620 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 5600482861) ^ 43260 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_5686023887 : Nat.Prime 5686023887 := by
  apply lucas_primality 5686023887 (5 : ZMod 5686023887)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2843011943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2843011943, 1)] : List FactorBlock).map factorBlockValue).prod) = 5686023887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_2843011943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 5686023887) ^ 2843011943 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 5686023887) ^ 2 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_5711218589 : Nat.Prime 5711218589 := by
  apply lucas_primality 5711218589 (3 : ZMod 5711218589)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (29, 1), (191, 1), (13567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (29, 1), (191, 1), (13567, 1)] : List FactorBlock).map factorBlockValue).prod) = 5711218589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_19
      · exact prime_seventyNineBY_29
      · exact prime_seventyNineBY_191
      · exact prime_seventyNineBY_13567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5711218589) ^ 2855609294 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 5711218589) ^ 300590452 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 5711218589) ^ 196938572 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 5711218589) ^ 29901668 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 5711218589) ^ 420964 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_5852300539 : Nat.Prime 5852300539 := by
  apply lucas_primality 5852300539 (3 : ZMod 5852300539)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (139340489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (139340489, 1)] : List FactorBlock).map factorBlockValue).prod) = 5852300539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_139340489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5852300539) ^ 2926150269 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 5852300539) ^ 1950766846 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 5852300539) ^ 836042934 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 5852300539) ^ 42 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_6059770061 : Nat.Prime 6059770061 := by
  apply lucas_primality 6059770061 (3 : ZMod 6059770061)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (302988503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (302988503, 1)] : List FactorBlock).map factorBlockValue).prod) = 6059770061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_302988503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 6059770061) ^ 3029885030 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 6059770061) ^ 1211954012 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 6059770061) ^ 20 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_8286733333 : Nat.Prime 8286733333 := by
  apply lucas_primality 8286733333 (5 : ZMod 8286733333)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (230187037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (230187037, 1)] : List FactorBlock).map factorBlockValue).prod) = 8286733333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_230187037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 8286733333) ^ 4143366666 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 8286733333) ^ 2762244444 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 8286733333) ^ 36 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_8643192331 : Nat.Prime 8643192331 := by
  apply lucas_primality 8643192331 (3 : ZMod 8643192331)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (223, 1), (1291957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (223, 1), (1291957, 1)] : List FactorBlock).map factorBlockValue).prod) = 8643192331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_223
      · exact prime_seventyNineBY_1291957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8643192331) ^ 4321596165 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 8643192331) ^ 2881064110 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 8643192331) ^ 1728638466 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 8643192331) ^ 38758710 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 8643192331) ^ 6690 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_9276928057 : Nat.Prime 9276928057 := by
  apply lucas_primality 9276928057 (5 : ZMod 9276928057)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (11, 1), (47, 1), (27691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (11, 1), (47, 1), (27691, 1)] : List FactorBlock).map factorBlockValue).prod) = 9276928057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_11
      · exact prime_seventyNineBY_47
      · exact prime_seventyNineBY_27691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 9276928057) ^ 4638464028 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 9276928057) ^ 3092309352 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 9276928057) ^ 843357096 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 9276928057) ^ 197381448 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 9276928057) ^ 335016 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_9435507247 : Nat.Prime 9435507247 := by
  apply lucas_primality 9435507247 (3 : ZMod 9435507247)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (17, 2), (164893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (17, 2), (164893, 1)] : List FactorBlock).map factorBlockValue).prod) = 9435507247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_11
      · exact prime_seventyNineBY_17
      · exact prime_seventyNineBY_164893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9435507247) ^ 4717753623 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 9435507247) ^ 3145169082 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 9435507247) ^ 857773386 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 9435507247) ^ 555029838 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 9435507247) ^ 57222 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_9447259687 : Nat.Prime 9447259687 := by
  apply lucas_primality 9447259687 (6 : ZMod 9447259687)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (19, 1), (4874747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (19, 1), (4874747, 1)] : List FactorBlock).map factorBlockValue).prod) = 9447259687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_17
      · exact prime_seventyNineBY_19
      · exact prime_seventyNineBY_4874747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 9447259687) ^ 4723629843 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 9447259687) ^ 3149086562 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 9447259687) ^ 555721158 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 9447259687) ^ 497224194 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 9447259687) ^ 1938 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_11427322337 : Nat.Prime 11427322337 := by
  apply lucas_primality 11427322337 (3 : ZMod 11427322337)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (163, 1), (2190821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (163, 1), (2190821, 1)] : List FactorBlock).map factorBlockValue).prod) = 11427322337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_163
      · exact prime_seventyNineBY_2190821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 11427322337) ^ 5713661168 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 11427322337) ^ 70106272 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 11427322337) ^ 5216 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_11515457959 : Nat.Prime 11515457959 := by
  apply lucas_primality 11515457959 (3 : ZMod 11515457959)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1919242993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1919242993, 1)] : List FactorBlock).map factorBlockValue).prod) = 11515457959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_1919242993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 11515457959) ^ 5757728979 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 11515457959) ^ 3838485986 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 11515457959) ^ 6 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_18105532019 : Nat.Prime 18105532019 := by
  apply lucas_primality 18105532019 (2 : ZMod 18105532019)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (233, 1), (5550439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (233, 1), (5550439, 1)] : List FactorBlock).map factorBlockValue).prod) = 18105532019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_233
      · exact prime_seventyNineBY_5550439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 18105532019) ^ 9052766009 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 18105532019) ^ 2586504574 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 18105532019) ^ 77706146 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 18105532019) ^ 3262 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_18695447611 : Nat.Prime 18695447611 := by
  apply lucas_primality 18695447611 (2 : ZMod 18695447611)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (89025941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (89025941, 1)] : List FactorBlock).map factorBlockValue).prod) = 18695447611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_89025941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18695447611) ^ 9347723805 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 18695447611) ^ 6231815870 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 18695447611) ^ 3739089522 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 18695447611) ^ 2670778230 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 18695447611) ^ 210 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_19502743301 : Nat.Prime 19502743301 := by
  apply lucas_primality 19502743301 (2 : ZMod 19502743301)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (461, 1), (423053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (461, 1), (423053, 1)] : List FactorBlock).map factorBlockValue).prod) = 19502743301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_461
      · exact prime_seventyNineBY_423053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 19502743301) ^ 9751371650 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 19502743301) ^ 3900548660 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 19502743301) ^ 42305300 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 19502743301) ^ 46100 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_22434889093 : Nat.Prime 22434889093 := by
  apply lucas_primality 22434889093 (13 : ZMod 22434889093)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (11, 1), (229, 2), (463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (11, 1), (229, 2), (463, 1)] : List FactorBlock).map factorBlockValue).prod) = 22434889093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_11
      · exact prime_seventyNineBY_229
      · exact prime_seventyNineBY_463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 22434889093) ^ 11217444546 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (13 : ZMod 22434889093) ^ 7478296364 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (13 : ZMod 22434889093) ^ 3204984156 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (13 : ZMod 22434889093) ^ 2039535372 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (13 : ZMod 22434889093) ^ 97968948 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (13 : ZMod 22434889093) ^ 48455484 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_24041465443 : Nat.Prime 24041465443 := by
  apply lucas_primality 24041465443 (3 : ZMod 24041465443)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (10093, 1), (44111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (10093, 1), (44111, 1)] : List FactorBlock).map factorBlockValue).prod) = 24041465443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_10093
      · exact prime_seventyNineBY_44111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 24041465443) ^ 12020732721 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 24041465443) ^ 8013821814 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 24041465443) ^ 2381994 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 24041465443) ^ 545022 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_25958239049 : Nat.Prime 25958239049 := by
  apply lucas_primality 25958239049 (3 : ZMod 25958239049)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (3967, 1), (116849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (3967, 1), (116849, 1)] : List FactorBlock).map factorBlockValue).prod) = 25958239049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_3967
      · exact prime_seventyNineBY_116849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 25958239049) ^ 12979119524 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 25958239049) ^ 3708319864 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 25958239049) ^ 6543544 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 25958239049) ^ 222152 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_26947955591 : Nat.Prime 26947955591 := by
  apply lucas_primality 26947955591 (7 : ZMod 26947955591)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (31, 1), (59, 1), (563, 1), (2617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (31, 1), (59, 1), (563, 1), (2617, 1)] : List FactorBlock).map factorBlockValue).prod) = 26947955591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_31
      · exact prime_seventyNineBY_59
      · exact prime_seventyNineBY_563
      · exact prime_seventyNineBY_2617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 26947955591) ^ 13473977795 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 26947955591) ^ 5389591118 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 26947955591) ^ 869288890 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 26947955591) ^ 456745010 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 26947955591) ^ 47864930 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 26947955591) ^ 10297270 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_29325044831 : Nat.Prime 29325044831 := by
  apply lucas_primality 29325044831 (22 : ZMod 29325044831)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (47777, 1), (61379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (47777, 1), (61379, 1)] : List FactorBlock).map factorBlockValue).prod) = 29325044831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_47777
      · exact prime_seventyNineBY_61379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (22 : ZMod 29325044831) ^ 14662522415 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (22 : ZMod 29325044831) ^ 5865008966 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (22 : ZMod 29325044831) ^ 613790 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (22 : ZMod 29325044831) ^ 477770 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_30341418251 : Nat.Prime 30341418251 := by
  apply lucas_primality 30341418251 (6 : ZMod 30341418251)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (11, 1), (13, 1), (19, 2), (2351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (11, 1), (13, 1), (19, 2), (2351, 1)] : List FactorBlock).map factorBlockValue).prod) = 30341418251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_11
      · exact prime_seventyNineBY_13
      · exact prime_seventyNineBY_19
      · exact prime_seventyNineBY_2351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 30341418251) ^ 15170709125 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 30341418251) ^ 6068283650 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 30341418251) ^ 2758310750 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 30341418251) ^ 2333955250 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 30341418251) ^ 1596916750 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 30341418251) ^ 12905750 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_40893744337 : Nat.Prime 40893744337 := by
  apply lucas_primality 40893744337 (5 : ZMod 40893744337)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (851953007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (851953007, 1)] : List FactorBlock).map factorBlockValue).prod) = 40893744337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_851953007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 40893744337) ^ 20446872168 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 40893744337) ^ 13631248112 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 40893744337) ^ 48 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_54872598679 : Nat.Prime 54872598679 := by
  apply lucas_primality 54872598679 (13 : ZMod 54872598679)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (61, 1), (3486631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (61, 1), (3486631, 1)] : List FactorBlock).map factorBlockValue).prod) = 54872598679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_43
      · exact prime_seventyNineBY_61
      · exact prime_seventyNineBY_3486631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 54872598679) ^ 27436299339 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (13 : ZMod 54872598679) ^ 18290866226 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (13 : ZMod 54872598679) ^ 1276106946 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (13 : ZMod 54872598679) ^ 899550798 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (13 : ZMod 54872598679) ^ 15738 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_55287973151 : Nat.Prime 55287973151 := by
  apply lucas_primality 55287973151 (13 : ZMod 55287973151)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (41, 1), (26969743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (41, 1), (26969743, 1)] : List FactorBlock).map factorBlockValue).prod) = 55287973151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_41
      · exact prime_seventyNineBY_26969743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 55287973151) ^ 27643986575 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (13 : ZMod 55287973151) ^ 11057594630 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (13 : ZMod 55287973151) ^ 1348487150 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (13 : ZMod 55287973151) ^ 2050 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_56855790253 : Nat.Prime 56855790253 := by
  apply lucas_primality 56855790253 (7 : ZMod 56855790253)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (1579327507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (1579327507, 1)] : List FactorBlock).map factorBlockValue).prod) = 56855790253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_1579327507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 56855790253) ^ 28427895126 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 56855790253) ^ 18951930084 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 56855790253) ^ 36 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_58603991911 : Nat.Prime 58603991911 := by
  apply lucas_primality 58603991911 (3 : ZMod 58603991911)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (223, 1), (557, 1), (15727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (223, 1), (557, 1), (15727, 1)] : List FactorBlock).map factorBlockValue).prod) = 58603991911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_223
      · exact prime_seventyNineBY_557
      · exact prime_seventyNineBY_15727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 58603991911) ^ 29301995955 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 58603991911) ^ 19534663970 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 58603991911) ^ 11720798382 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 58603991911) ^ 262798170 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 58603991911) ^ 105213630 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 58603991911) ^ 3726330 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_72667686431 : Nat.Prime 72667686431 := by
  apply lucas_primality 72667686431 (7 : ZMod 72667686431)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (193, 1), (547, 1), (4049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (193, 1), (547, 1), (4049, 1)] : List FactorBlock).map factorBlockValue).prod) = 72667686431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_17
      · exact prime_seventyNineBY_193
      · exact prime_seventyNineBY_547
      · exact prime_seventyNineBY_4049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 72667686431) ^ 36333843215 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 72667686431) ^ 14533537286 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 72667686431) ^ 4274569790 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 72667686431) ^ 376516510 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 72667686431) ^ 132847690 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 72667686431) ^ 17947070 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_87535209887 : Nat.Prime 87535209887 := by
  apply lucas_primality 87535209887 (5 : ZMod 87535209887)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2903, 1), (15076681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2903, 1), (15076681, 1)] : List FactorBlock).map factorBlockValue).prod) = 87535209887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_2903
      · exact prime_seventyNineBY_15076681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 87535209887) ^ 43767604943 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 87535209887) ^ 30153362 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 87535209887) ^ 5806 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_92471716307 : Nat.Prime 92471716307 := by
  apply lucas_primality 92471716307 (2 : ZMod 92471716307)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (50101, 1), (922853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (50101, 1), (922853, 1)] : List FactorBlock).map factorBlockValue).prod) = 92471716307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_50101
      · exact prime_seventyNineBY_922853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 92471716307) ^ 46235858153 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 92471716307) ^ 1845706 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 92471716307) ^ 100202 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_95565115073 : Nat.Prime 95565115073 := by
  apply lucas_primality 95565115073 (3 : ZMod 95565115073)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (4229, 1), (50441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (4229, 1), (50441, 1)] : List FactorBlock).map factorBlockValue).prod) = 95565115073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_4229
      · exact prime_seventyNineBY_50441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 95565115073) ^ 47782557536 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 95565115073) ^ 13652159296 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 95565115073) ^ 22597568 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 95565115073) ^ 1894592 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_100604082277 : Nat.Prime 100604082277 := by
  apply lucas_primality 100604082277 (6 : ZMod 100604082277)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (107, 1), (26117363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (107, 1), (26117363, 1)] : List FactorBlock).map factorBlockValue).prod) = 100604082277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_107
      · exact prime_seventyNineBY_26117363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 100604082277) ^ 50302041138 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 100604082277) ^ 33534694092 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 100604082277) ^ 940225068 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 100604082277) ^ 3852 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_118785459223 : Nat.Prime 118785459223 := by
  apply lucas_primality 118785459223 (7 : ZMod 118785459223)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (29, 1), (227558351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (29, 1), (227558351, 1)] : List FactorBlock).map factorBlockValue).prod) = 118785459223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_29
      · exact prime_seventyNineBY_227558351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 118785459223) ^ 59392729611 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 118785459223) ^ 39595153074 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 118785459223) ^ 4096050318 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 118785459223) ^ 522 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_147377116847 : Nat.Prime 147377116847 := by
  apply lucas_primality 147377116847 (5 : ZMod 147377116847)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (443, 1), (166339861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (443, 1), (166339861, 1)] : List FactorBlock).map factorBlockValue).prod) = 147377116847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_443
      · exact prime_seventyNineBY_166339861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 147377116847) ^ 73688558423 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 147377116847) ^ 332679722 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 147377116847) ^ 886 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_153253320491 : Nat.Prime 153253320491 := by
  apply lucas_primality 153253320491 (2 : ZMod 153253320491)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1723, 1), (8894563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1723, 1), (8894563, 1)] : List FactorBlock).map factorBlockValue).prod) = 153253320491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_1723
      · exact prime_seventyNineBY_8894563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 153253320491) ^ 76626660245 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 153253320491) ^ 30650664098 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 153253320491) ^ 88945630 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 153253320491) ^ 17230 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_261634097603 : Nat.Prime 261634097603 := by
  apply lucas_primality 261634097603 (2 : ZMod 261634097603)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (197, 1), (1213, 1), (547441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (197, 1), (1213, 1), (547441, 1)] : List FactorBlock).map factorBlockValue).prod) = 261634097603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_197
      · exact prime_seventyNineBY_1213
      · exact prime_seventyNineBY_547441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 261634097603) ^ 130817048801 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 261634097603) ^ 1328091866 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 261634097603) ^ 215691754 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 261634097603) ^ 477922 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_266764874087 : Nat.Prime 266764874087 := by
  apply lucas_primality 266764874087 (5 : ZMod 266764874087)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (911, 1), (146413213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (911, 1), (146413213, 1)] : List FactorBlock).map factorBlockValue).prod) = 266764874087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_911
      · exact prime_seventyNineBY_146413213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 266764874087) ^ 133382437043 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 266764874087) ^ 292826426 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 266764874087) ^ 1822 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_283417790611 : Nat.Prime 283417790611 := by
  apply lucas_primality 283417790611 (2 : ZMod 283417790611)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (9447259687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (9447259687, 1)] : List FactorBlock).map factorBlockValue).prod) = 283417790611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_9447259687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 283417790611) ^ 141708895305 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 283417790611) ^ 94472596870 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 283417790611) ^ 56683558122 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 283417790611) ^ 30 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_325451253779 : Nat.Prime 325451253779 := by
  apply lucas_primality 325451253779 (2 : ZMod 325451253779)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (41, 1), (269, 1), (353, 1), (853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (41, 1), (269, 1), (353, 1), (853, 1)] : List FactorBlock).map factorBlockValue).prod) = 325451253779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_41
      · exact prime_seventyNineBY_269
      · exact prime_seventyNineBY_353
      · exact prime_seventyNineBY_853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 325451253779) ^ 162725626889 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 325451253779) ^ 46493036254 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 325451253779) ^ 7937835458 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 325451253779) ^ 1209855962 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 325451253779) ^ 921958226 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 325451253779) ^ 381537226 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_336695436983 : Nat.Prime 336695436983 := by
  apply lucas_primality 336695436983 (5 : ZMod 336695436983)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (241, 1), (359, 1), (36713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (241, 1), (359, 1), (36713, 1)] : List FactorBlock).map factorBlockValue).prod) = 336695436983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_53
      · exact prime_seventyNineBY_241
      · exact prime_seventyNineBY_359
      · exact prime_seventyNineBY_36713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 336695436983) ^ 168347718491 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 336695436983) ^ 6352744094 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 336695436983) ^ 1397076502 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 336695436983) ^ 937870298 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 336695436983) ^ 9171014 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_366748976423 : Nat.Prime 366748976423 := by
  apply lucas_primality 366748976423 (5 : ZMod 366748976423)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (103, 1), (29185817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (103, 1), (29185817, 1)] : List FactorBlock).map factorBlockValue).prod) = 366748976423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_61
      · exact prime_seventyNineBY_103
      · exact prime_seventyNineBY_29185817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 366748976423) ^ 183374488211 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 366748976423) ^ 6012278302 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 366748976423) ^ 3560669674 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 366748976423) ^ 12566 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_421866874879 : Nat.Prime 421866874879 := by
  apply lucas_primality 421866874879 (3 : ZMod 421866874879)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (73, 1), (241, 1), (3996541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (73, 1), (241, 1), (3996541, 1)] : List FactorBlock).map factorBlockValue).prod) = 421866874879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_73
      · exact prime_seventyNineBY_241
      · exact prime_seventyNineBY_3996541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 421866874879) ^ 210933437439 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 421866874879) ^ 140622291626 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 421866874879) ^ 5778998286 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 421866874879) ^ 1750484958 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 421866874879) ^ 105558 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_465312270209 : Nat.Prime 465312270209 := by
  apply lucas_primality 465312270209 (3 : ZMod 465312270209)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3635252111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3635252111, 1)] : List FactorBlock).map factorBlockValue).prod) = 465312270209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3635252111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 465312270209) ^ 232656135104 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 465312270209) ^ 128 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_470424571583 : Nat.Prime 470424571583 := by
  apply lucas_primality 470424571583 (5 : ZMod 470424571583)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (1768513427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (1768513427, 1)] : List FactorBlock).map factorBlockValue).prod) = 470424571583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_19
      · exact prime_seventyNineBY_1768513427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 470424571583) ^ 235212285791 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 470424571583) ^ 67203510226 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 470424571583) ^ 24759187978 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 470424571583) ^ 266 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_511758652417 : Nat.Prime 511758652417 := by
  apply lucas_primality 511758652417 (7 : ZMod 511758652417)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (3, 1), (11, 1), (23, 1), (113, 1), (5827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (3, 1), (11, 1), (23, 1), (113, 1), (5827, 1)] : List FactorBlock).map factorBlockValue).prod) = 511758652417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_11
      · exact prime_seventyNineBY_23
      · exact prime_seventyNineBY_113
      · exact prime_seventyNineBY_5827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 511758652417) ^ 255879326208 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 511758652417) ^ 170586217472 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 511758652417) ^ 46523513856 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 511758652417) ^ 22250376192 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 511758652417) ^ 4528837632 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 511758652417) ^ 87825408 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_519082709317 : Nat.Prime 519082709317 := by
  apply lucas_primality 519082709317 (5 : ZMod 519082709317)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (179, 1), (241658617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (179, 1), (241658617, 1)] : List FactorBlock).map factorBlockValue).prod) = 519082709317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_179
      · exact prime_seventyNineBY_241658617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 519082709317) ^ 259541354658 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 519082709317) ^ 173027569772 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 519082709317) ^ 2899903404 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 519082709317) ^ 2148 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_532010438077 : Nat.Prime 532010438077 := by
  apply lucas_primality 532010438077 (5 : ZMod 532010438077)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (23, 1), (1549, 1), (95723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (23, 1), (1549, 1), (95723, 1)] : List FactorBlock).map factorBlockValue).prod) = 532010438077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_13
      · exact prime_seventyNineBY_23
      · exact prime_seventyNineBY_1549
      · exact prime_seventyNineBY_95723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 532010438077) ^ 266005219038 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 532010438077) ^ 177336812692 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 532010438077) ^ 40923879852 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 532010438077) ^ 23130888612 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 532010438077) ^ 343454124 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 532010438077) ^ 5557812 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_539683141139 : Nat.Prime 539683141139 := by
  apply lucas_primality 539683141139 (2 : ZMod 539683141139)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1097, 1), (245981377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1097, 1), (245981377, 1)] : List FactorBlock).map factorBlockValue).prod) = 539683141139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_1097
      · exact prime_seventyNineBY_245981377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 539683141139) ^ 269841570569 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 539683141139) ^ 491962754 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 539683141139) ^ 2194 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_560863428331 : Nat.Prime 560863428331 := by
  apply lucas_primality 560863428331 (3 : ZMod 560863428331)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (18695447611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (18695447611, 1)] : List FactorBlock).map factorBlockValue).prod) = 560863428331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_18695447611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 560863428331) ^ 280431714165 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 560863428331) ^ 186954476110 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 560863428331) ^ 112172685666 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 560863428331) ^ 30 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_581341491449 : Nat.Prime 581341491449 := by
  apply lucas_primality 581341491449 (3 : ZMod 581341491449)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (72667686431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (72667686431, 1)] : List FactorBlock).map factorBlockValue).prod) = 581341491449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_72667686431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 581341491449) ^ 290670745724 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 581341491449) ^ 8 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_604942115969 : Nat.Prime 604942115969 := by
  apply lucas_primality 604942115969 (3 : ZMod 604942115969)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (9067, 1), (521243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (9067, 1), (521243, 1)] : List FactorBlock).map factorBlockValue).prod) = 604942115969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_9067
      · exact prime_seventyNineBY_521243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 604942115969) ^ 302471057984 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 604942115969) ^ 66719104 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 604942115969) ^ 1160576 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_651351762233 : Nat.Prime 651351762233 := by
  apply lucas_primality 651351762233 (3 : ZMod 651351762233)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3709, 1), (21951731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3709, 1), (21951731, 1)] : List FactorBlock).map factorBlockValue).prod) = 651351762233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3709
      · exact prime_seventyNineBY_21951731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 651351762233) ^ 325675881116 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 651351762233) ^ 175613848 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 651351762233) ^ 29672 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_913172008129 : Nat.Prime 913172008129 := by
  apply lucas_primality 913172008129 (21 : ZMod 913172008129)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (37, 1), (131, 1), (401, 1), (2447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (37, 1), (131, 1), (401, 1), (2447, 1)] : List FactorBlock).map factorBlockValue).prod) = 913172008129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_37
      · exact prime_seventyNineBY_131
      · exact prime_seventyNineBY_401
      · exact prime_seventyNineBY_2447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (21 : ZMod 913172008129) ^ 456586004064 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (21 : ZMod 913172008129) ^ 304390669376 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (21 : ZMod 913172008129) ^ 24680324544 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (21 : ZMod 913172008129) ^ 6970778688 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (21 : ZMod 913172008129) ^ 2277236928 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (21 : ZMod 913172008129) ^ 373180224 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_987706776223 : Nat.Prime 987706776223 := by
  apply lucas_primality 987706776223 (3 : ZMod 987706776223)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (54872598679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (54872598679, 1)] : List FactorBlock).map factorBlockValue).prod) = 987706776223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_54872598679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 987706776223) ^ 493853388111 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 987706776223) ^ 329235592074 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 987706776223) ^ 18 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_1006796278157 : Nat.Prime 1006796278157 := by
  apply lucas_primality 1006796278157 (2 : ZMod 1006796278157)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (647, 1), (4789, 1), (81233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (647, 1), (4789, 1), (81233, 1)] : List FactorBlock).map factorBlockValue).prod) = 1006796278157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_647
      · exact prime_seventyNineBY_4789
      · exact prime_seventyNineBY_81233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1006796278157) ^ 503398139078 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1006796278157) ^ 1556099348 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1006796278157) ^ 210231004 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1006796278157) ^ 12393932 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_1277165570099 : Nat.Prime 1277165570099 := by
  apply lucas_primality 1277165570099 (2 : ZMod 1277165570099)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (31, 1), (43, 1), (47, 1), (109, 1), (8501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (31, 1), (43, 1), (47, 1), (109, 1), (8501, 1)] : List FactorBlock).map factorBlockValue).prod) = 1277165570099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_11
      · exact prime_seventyNineBY_31
      · exact prime_seventyNineBY_43
      · exact prime_seventyNineBY_47
      · exact prime_seventyNineBY_109
      · exact prime_seventyNineBY_8501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1277165570099) ^ 638582785049 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1277165570099) ^ 116105960918 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1277165570099) ^ 41198889358 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1277165570099) ^ 29701524886 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1277165570099) ^ 27173735534 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1277165570099) ^ 11717115322 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1277165570099) ^ 150237098 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_1304742033277 : Nat.Prime 1304742033277 := by
  apply lucas_primality 1304742033277 (2 : ZMod 1304742033277)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (71, 1), (1489, 1), (93497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (71, 1), (1489, 1), (93497, 1)] : List FactorBlock).map factorBlockValue).prod) = 1304742033277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_11
      · exact prime_seventyNineBY_71
      · exact prime_seventyNineBY_1489
      · exact prime_seventyNineBY_93497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1304742033277) ^ 652371016638 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1304742033277) ^ 434914011092 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1304742033277) ^ 118612912116 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1304742033277) ^ 18376648356 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1304742033277) ^ 876253884 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1304742033277) ^ 13954908 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_1569794302441 : Nat.Prime 1569794302441 := by
  apply lucas_primality 1569794302441 (11 : ZMod 1569794302441)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (7, 1), (13, 1), (17, 1), (19, 1), (49451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (7, 1), (13, 1), (17, 1), (19, 1), (49451, 1)] : List FactorBlock).map factorBlockValue).prod) = 1569794302441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_13
      · exact prime_seventyNineBY_17
      · exact prime_seventyNineBY_19
      · exact prime_seventyNineBY_49451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1569794302441) ^ 784897151220 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (11 : ZMod 1569794302441) ^ 523264767480 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (11 : ZMod 1569794302441) ^ 313958860488 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (11 : ZMod 1569794302441) ^ 224256328920 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (11 : ZMod 1569794302441) ^ 120753407880 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (11 : ZMod 1569794302441) ^ 92340841320 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (11 : ZMod 1569794302441) ^ 82620752760 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (11 : ZMod 1569794302441) ^ 31744440 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_1678943581867 : Nat.Prime 1678943581867 := by
  apply lucas_primality 1678943581867 (2 : ZMod 1678943581867)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (12409, 1), (7516693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (12409, 1), (7516693, 1)] : List FactorBlock).map factorBlockValue).prod) = 1678943581867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_12409
      · exact prime_seventyNineBY_7516693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1678943581867) ^ 839471790933 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1678943581867) ^ 559647860622 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1678943581867) ^ 135300474 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1678943581867) ^ 223362 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_2030480365583 : Nat.Prime 2030480365583 := by
  apply lucas_primality 2030480365583 (5 : ZMod 2030480365583)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (53, 1), (407563301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (53, 1), (407563301, 1)] : List FactorBlock).map factorBlockValue).prod) = 2030480365583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_47
      · exact prime_seventyNineBY_53
      · exact prime_seventyNineBY_407563301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2030480365583) ^ 1015240182791 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2030480365583) ^ 43201709906 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2030480365583) ^ 38310950294 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2030480365583) ^ 4982 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_3166905163979 : Nat.Prime 3166905163979 := by
  apply lucas_primality 3166905163979 (2 : ZMod 3166905163979)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (25958239049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (25958239049, 1)] : List FactorBlock).map factorBlockValue).prod) = 3166905163979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_61
      · exact prime_seventyNineBY_25958239049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3166905163979) ^ 1583452581989 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3166905163979) ^ 51916478098 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3166905163979) ^ 122 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_3201848328761 : Nat.Prime 3201848328761 := by
  apply lucas_primality 3201848328761 (3 : ZMod 3201848328761)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (31, 1), (38047, 1), (67867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (31, 1), (38047, 1), (67867, 1)] : List FactorBlock).map factorBlockValue).prod) = 3201848328761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_31
      · exact prime_seventyNineBY_38047
      · exact prime_seventyNineBY_67867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3201848328761) ^ 1600924164380 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3201848328761) ^ 640369665752 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3201848328761) ^ 103285429960 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3201848328761) ^ 84155080 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3201848328761) ^ 47178280 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_3557130138013 : Nat.Prime 3557130138013 := by
  apply lucas_primality 3557130138013 (2 : ZMod 3557130138013)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (26947955591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (26947955591, 1)] : List FactorBlock).map factorBlockValue).prod) = 3557130138013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_11
      · exact prime_seventyNineBY_26947955591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3557130138013) ^ 1778565069006 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3557130138013) ^ 1185710046004 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3557130138013) ^ 323375467092 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3557130138013) ^ 132 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_3652688032517 : Nat.Prime 3652688032517 := by
  apply lucas_primality 3652688032517 (2 : ZMod 3652688032517)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (913172008129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (913172008129, 1)] : List FactorBlock).map factorBlockValue).prod) = 3652688032517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_913172008129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 3652688032517) ^ 1826344016258 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3652688032517) ^ 4 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_3706346648111 : Nat.Prime 3706346648111 := by
  apply lucas_primality 3706346648111 (7 : ZMod 3706346648111)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37, 1), (25889, 1), (386927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37, 1), (25889, 1), (386927, 1)] : List FactorBlock).map factorBlockValue).prod) = 3706346648111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_37
      · exact prime_seventyNineBY_25889
      · exact prime_seventyNineBY_386927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3706346648111) ^ 1853173324055 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 3706346648111) ^ 741269329622 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 3706346648111) ^ 100171531030 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 3706346648111) ^ 143162990 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 3706346648111) ^ 9578930 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_5238694497481 : Nat.Prime 5238694497481 := by
  apply lucas_primality 5238694497481 (23 : ZMod 5238694497481)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (31, 1), (1408251209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (31, 1), (1408251209, 1)] : List FactorBlock).map factorBlockValue).prod) = 5238694497481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_31
      · exact prime_seventyNineBY_1408251209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 5238694497481) ^ 2619347248740 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (23 : ZMod 5238694497481) ^ 1746231499160 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (23 : ZMod 5238694497481) ^ 1047738899496 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (23 : ZMod 5238694497481) ^ 168990145080 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (23 : ZMod 5238694497481) ^ 3720 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_5484396664753 : Nat.Prime 5484396664753 := by
  apply lucas_primality 5484396664753 (11 : ZMod 5484396664753)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (72073, 1), (1585313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (72073, 1), (1585313, 1)] : List FactorBlock).map factorBlockValue).prod) = 5484396664753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_72073
      · exact prime_seventyNineBY_1585313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 5484396664753) ^ 2742198332376 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (11 : ZMod 5484396664753) ^ 1828132221584 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (11 : ZMod 5484396664753) ^ 76095024 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (11 : ZMod 5484396664753) ^ 3459504 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_6067110949279 : Nat.Prime 6067110949279 := by
  apply lucas_primality 6067110949279 (3 : ZMod 6067110949279)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (109, 1), (9276928057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (109, 1), (9276928057, 1)] : List FactorBlock).map factorBlockValue).prod) = 6067110949279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_109
      · exact prime_seventyNineBY_9276928057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6067110949279) ^ 3033555474639 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 6067110949279) ^ 2022370316426 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 6067110949279) ^ 55661568342 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 6067110949279) ^ 654 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_6313983472681 : Nat.Prime 6313983472681 := by
  apply lucas_primality 6313983472681 (7 : ZMod 6313983472681)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (13, 1), (157, 1), (25779779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (13, 1), (157, 1), (25779779, 1)] : List FactorBlock).map factorBlockValue).prod) = 6313983472681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_13
      · exact prime_seventyNineBY_157
      · exact prime_seventyNineBY_25779779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6313983472681) ^ 3156991736340 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 6313983472681) ^ 2104661157560 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 6313983472681) ^ 1262796694536 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 6313983472681) ^ 485691036360 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 6313983472681) ^ 40216455240 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 6313983472681) ^ 244920 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_6978051400253 : Nat.Prime 6978051400253 := by
  apply lucas_primality 6978051400253 (2 : ZMod 6978051400253)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (14009, 1), (124528007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (14009, 1), (124528007, 1)] : List FactorBlock).map factorBlockValue).prod) = 6978051400253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_14009
      · exact prime_seventyNineBY_124528007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6978051400253) ^ 3489025700126 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 6978051400253) ^ 498112028 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 6978051400253) ^ 56036 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_7851602000873 : Nat.Prime 7851602000873 := by
  apply lucas_primality 7851602000873 (3 : ZMod 7851602000873)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (101, 1), (173, 1), (251, 1), (4567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (101, 1), (173, 1), (251, 1), (4567, 1)] : List FactorBlock).map factorBlockValue).prod) = 7851602000873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_101
      · exact prime_seventyNineBY_173
      · exact prime_seventyNineBY_251
      · exact prime_seventyNineBY_4567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7851602000873) ^ 3925801000436 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 7851602000873) ^ 1121657428696 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 7851602000873) ^ 77738633672 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 7851602000873) ^ 45384982664 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 7851602000873) ^ 31281282872 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 7851602000873) ^ 1719203416 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_8275904472347 : Nat.Prime 8275904472347 := by
  apply lucas_primality 8275904472347 (2 : ZMod 8275904472347)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 1), (2729, 1), (12741923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 1), (2729, 1), (12741923, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275904472347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_17
      · exact prime_seventyNineBY_2729
      · exact prime_seventyNineBY_12741923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8275904472347) ^ 4137952236173 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 8275904472347) ^ 1182272067478 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 8275904472347) ^ 486817910138 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 8275904472347) ^ 3032577674 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 8275904472347) ^ 649502 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_8352155131517 : Nat.Prime 8352155131517 := by
  apply lucas_primality 8352155131517 (2 : ZMod 8352155131517)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (103, 1), (607, 1), (1747, 1), (2731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (103, 1), (607, 1), (1747, 1), (2731, 1)] : List FactorBlock).map factorBlockValue).prod) = 8352155131517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_103
      · exact prime_seventyNineBY_607
      · exact prime_seventyNineBY_1747
      · exact prime_seventyNineBY_2731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8352155131517) ^ 4176077565758 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 8352155131517) ^ 1193165018788 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 8352155131517) ^ 81088884772 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 8352155131517) ^ 13759728388 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 8352155131517) ^ 4780855828 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 8352155131517) ^ 3058277236 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_8792102686511 : Nat.Prime 8792102686511 := by
  apply lucas_primality 8792102686511 (7 : ZMod 8792102686511)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (13, 1), (1979, 1), (3106783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (13, 1), (1979, 1), (3106783, 1)] : List FactorBlock).map factorBlockValue).prod) = 8792102686511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_11
      · exact prime_seventyNineBY_13
      · exact prime_seventyNineBY_1979
      · exact prime_seventyNineBY_3106783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 8792102686511) ^ 4396051343255 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 8792102686511) ^ 1758420537302 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 8792102686511) ^ 799282062410 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 8792102686511) ^ 676315591270 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 8792102686511) ^ 4442699690 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 8792102686511) ^ 2829970 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_9245136975587 : Nat.Prime 9245136975587 := by
  apply lucas_primality 9245136975587 (2 : ZMod 9245136975587)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (151, 1), (12547, 1), (59509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (151, 1), (12547, 1), (59509, 1)] : List FactorBlock).map factorBlockValue).prod) = 9245136975587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_41
      · exact prime_seventyNineBY_151
      · exact prime_seventyNineBY_12547
      · exact prime_seventyNineBY_59509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9245136975587) ^ 4622568487793 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 9245136975587) ^ 225491145746 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 9245136975587) ^ 61226072686 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 9245136975587) ^ 736840438 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 9245136975587) ^ 155356954 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_9849424786697 : Nat.Prime 9849424786697 := by
  apply lucas_primality 9849424786697 (3 : ZMod 9849424786697)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (31, 1), (21617, 1), (167021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (31, 1), (21617, 1), (167021, 1)] : List FactorBlock).map factorBlockValue).prod) = 9849424786697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_11
      · exact prime_seventyNineBY_31
      · exact prime_seventyNineBY_21617
      · exact prime_seventyNineBY_167021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9849424786697) ^ 4924712393348 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 9849424786697) ^ 895402253336 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 9849424786697) ^ 317723380216 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 9849424786697) ^ 455633288 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 9849424786697) ^ 58971176 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_10095541709959 : Nat.Prime 10095541709959 := by
  apply lucas_primality 10095541709959 (3 : ZMod 10095541709959)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (560863428331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (560863428331, 1)] : List FactorBlock).map factorBlockValue).prod) = 10095541709959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_560863428331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 10095541709959) ^ 5047770854979 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 10095541709959) ^ 3365180569986 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 10095541709959) ^ 18 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_11835834585121 : Nat.Prime 11835834585121 := by
  apply lucas_primality 11835834585121 (11 : ZMod 11835834585121)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (7, 1), (13, 1), (41, 1), (2202983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (7, 1), (13, 1), (41, 1), (2202983, 1)] : List FactorBlock).map factorBlockValue).prod) = 11835834585121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_13
      · exact prime_seventyNineBY_41
      · exact prime_seventyNineBY_2202983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 11835834585121) ^ 5917917292560 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (11 : ZMod 11835834585121) ^ 3945278195040 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (11 : ZMod 11835834585121) ^ 2367166917024 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (11 : ZMod 11835834585121) ^ 1690833512160 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (11 : ZMod 11835834585121) ^ 910448814240 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (11 : ZMod 11835834585121) ^ 288678892320 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (11 : ZMod 11835834585121) ^ 5372640 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_13207631245021 : Nat.Prime 13207631245021 := by
  apply lucas_primality 13207631245021 (2 : ZMod 13207631245021)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (19, 1), (23, 1), (167907847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (19, 1), (23, 1), (167907847, 1)] : List FactorBlock).map factorBlockValue).prod) = 13207631245021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_19
      · exact prime_seventyNineBY_23
      · exact prime_seventyNineBY_167907847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13207631245021) ^ 6603815622510 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 13207631245021) ^ 4402543748340 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 13207631245021) ^ 2641526249004 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 13207631245021) ^ 695138486580 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 13207631245021) ^ 574244836740 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 13207631245021) ^ 78660 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_15087309795557 : Nat.Prime 15087309795557 := by
  apply lucas_primality 15087309795557 (2 : ZMod 15087309795557)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (15359, 1), (245577671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (15359, 1), (245577671, 1)] : List FactorBlock).map factorBlockValue).prod) = 15087309795557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_15359
      · exact prime_seventyNineBY_245577671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 15087309795557) ^ 7543654897778 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 15087309795557) ^ 982310684 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 15087309795557) ^ 61436 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_15817041965731 : Nat.Prime 15817041965731 := by
  apply lucas_primality 15817041965731 (2 : ZMod 15817041965731)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (61, 1), (8643192331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (61, 1), (8643192331, 1)] : List FactorBlock).map factorBlockValue).prod) = 15817041965731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_61
      · exact prime_seventyNineBY_8643192331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15817041965731) ^ 7908520982865 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 15817041965731) ^ 5272347321910 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 15817041965731) ^ 3163408393146 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 15817041965731) ^ 259295769930 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 15817041965731) ^ 1830 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_18423311487013 : Nat.Prime 18423311487013 := by
  apply lucas_primality 18423311487013 (5 : ZMod 18423311487013)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (511758652417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (511758652417, 1)] : List FactorBlock).map factorBlockValue).prod) = 18423311487013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_511758652417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 18423311487013) ^ 9211655743506 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 18423311487013) ^ 6141103829004 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 18423311487013) ^ 36 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_20483412891343 : Nat.Prime 20483412891343 := by
  apply lucas_primality 20483412891343 (3 : ZMod 20483412891343)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (733, 1), (4657438129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (733, 1), (4657438129, 1)] : List FactorBlock).map factorBlockValue).prod) = 20483412891343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_733
      · exact prime_seventyNineBY_4657438129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 20483412891343) ^ 10241706445671 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 20483412891343) ^ 6827804297114 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 20483412891343) ^ 27944628774 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 20483412891343) ^ 4398 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_22357543421251 : Nat.Prime 22357543421251 := by
  apply lucas_primality 22357543421251 (2 : ZMod 22357543421251)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 4), (79, 1), (8385389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 4), (79, 1), (8385389, 1)] : List FactorBlock).map factorBlockValue).prod) = 22357543421251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_79
      · exact prime_seventyNineBY_8385389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22357543421251) ^ 11178771710625 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 22357543421251) ^ 7452514473750 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 22357543421251) ^ 4471508684250 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 22357543421251) ^ 283006878750 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 22357543421251) ^ 2666250 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_22458979260511 : Nat.Prime 22458979260511 := by
  apply lucas_primality 22458979260511 (3 : ZMod 22458979260511)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (53, 1), (1086549553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (53, 1), (1086549553, 1)] : List FactorBlock).map factorBlockValue).prod) = 22458979260511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_13
      · exact prime_seventyNineBY_53
      · exact prime_seventyNineBY_1086549553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 22458979260511) ^ 11229489630255 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 22458979260511) ^ 7486326420170 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 22458979260511) ^ 4491795852102 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 22458979260511) ^ 1727613789270 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 22458979260511) ^ 423754325670 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 22458979260511) ^ 20670 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_30425105413337 : Nat.Prime 30425105413337 := by
  apply lucas_primality 30425105413337 (3 : ZMod 30425105413337)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (113, 1), (1771373161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (113, 1), (1771373161, 1)] : List FactorBlock).map factorBlockValue).prod) = 30425105413337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_19
      · exact prime_seventyNineBY_113
      · exact prime_seventyNineBY_1771373161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 30425105413337) ^ 15212552706668 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 30425105413337) ^ 1601321337544 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 30425105413337) ^ 269248720472 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 30425105413337) ^ 17176 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_30802642328807 : Nat.Prime 30802642328807 := by
  apply lucas_primality 30802642328807 (5 : ZMod 30802642328807)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (127, 1), (3931, 1), (656377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (127, 1), (3931, 1), (656377, 1)] : List FactorBlock).map factorBlockValue).prod) = 30802642328807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_47
      · exact prime_seventyNineBY_127
      · exact prime_seventyNineBY_3931
      · exact prime_seventyNineBY_656377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 30802642328807) ^ 15401321164403 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 30802642328807) ^ 655375368698 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 30802642328807) ^ 242540490778 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 30802642328807) ^ 7835828626 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 30802642328807) ^ 46928278 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_35016325446233 : Nat.Prime 35016325446233 := by
  apply lucas_primality 35016325446233 (3 : ZMod 35016325446233)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (336695436983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (336695436983, 1)] : List FactorBlock).map factorBlockValue).prod) = 35016325446233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_13
      · exact prime_seventyNineBY_336695436983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 35016325446233) ^ 17508162723116 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 35016325446233) ^ 2693563495864 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 35016325446233) ^ 104 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_39675103098143 : Nat.Prime 39675103098143 := by
  apply lucas_primality 39675103098143 (5 : ZMod 39675103098143)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1277, 1), (5099, 1), (3046577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1277, 1), (5099, 1), (3046577, 1)] : List FactorBlock).map factorBlockValue).prod) = 39675103098143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_1277
      · exact prime_seventyNineBY_5099
      · exact prime_seventyNineBY_3046577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 39675103098143) ^ 19837551549071 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 39675103098143) ^ 31068992246 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 39675103098143) ^ 7780957658 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 39675103098143) ^ 13022846 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_52752616119067 : Nat.Prime 52752616119067 := by
  apply lucas_primality 52752616119067 (2 : ZMod 52752616119067)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (8792102686511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (8792102686511, 1)] : List FactorBlock).map factorBlockValue).prod) = 52752616119067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_8792102686511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 52752616119067) ^ 26376308059533 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 52752616119067) ^ 17584205373022 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 52752616119067) ^ 6 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_53927402483707 : Nat.Prime 53927402483707 := by
  apply lucas_primality 53927402483707 (3 : ZMod 53927402483707)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (271723, 1), (33077437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (271723, 1), (33077437, 1)] : List FactorBlock).map factorBlockValue).prod) = 53927402483707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_271723
      · exact prime_seventyNineBY_33077437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 53927402483707) ^ 26963701241853 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 53927402483707) ^ 17975800827902 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 53927402483707) ^ 198464622 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 53927402483707) ^ 1630338 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_65866097440903 : Nat.Prime 65866097440903 := by
  apply lucas_primality 65866097440903 (3 : ZMod 65866097440903)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (5441, 1), (183416867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (5441, 1), (183416867, 1)] : List FactorBlock).map factorBlockValue).prod) = 65866097440903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_11
      · exact prime_seventyNineBY_5441
      · exact prime_seventyNineBY_183416867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 65866097440903) ^ 32933048720451 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 65866097440903) ^ 21955365813634 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 65866097440903) ^ 5987827040082 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 65866097440903) ^ 12105513222 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 65866097440903) ^ 359106 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_70032650892467 : Nat.Prime 70032650892467 := by
  apply lucas_primality 70032650892467 (2 : ZMod 70032650892467)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (35016325446233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (35016325446233, 1)] : List FactorBlock).map factorBlockValue).prod) = 70032650892467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_35016325446233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 70032650892467) ^ 35016325446233 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 70032650892467) ^ 2 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_73961095804697 : Nat.Prime 73961095804697 := by
  apply lucas_primality 73961095804697 (3 : ZMod 73961095804697)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (9245136975587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (9245136975587, 1)] : List FactorBlock).map factorBlockValue).prod) = 73961095804697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_9245136975587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 73961095804697) ^ 36980547902348 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 73961095804697) ^ 8 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_90901676817599 : Nat.Prime 90901676817599 := by
  apply lucas_primality 90901676817599 (7 : ZMod 90901676817599)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4817, 1), (9435507247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4817, 1), (9435507247, 1)] : List FactorBlock).map factorBlockValue).prod) = 90901676817599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_4817
      · exact prime_seventyNineBY_9435507247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 90901676817599) ^ 45450838408799 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 90901676817599) ^ 18871014494 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 90901676817599) ^ 9634 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_120255410145887 : Nat.Prime 120255410145887 := by
  apply lucas_primality 120255410145887 (5 : ZMod 120255410145887)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (61, 1), (24041465443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (61, 1), (24041465443, 1)] : List FactorBlock).map factorBlockValue).prod) = 120255410145887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_41
      · exact prime_seventyNineBY_61
      · exact prime_seventyNineBY_24041465443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 120255410145887) ^ 60127705072943 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 120255410145887) ^ 2933058784046 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 120255410145887) ^ 1971400166326 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 120255410145887) ^ 5002 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_145505492449357 : Nat.Prime 145505492449357 := by
  apply lucas_primality 145505492449357 (2 : ZMod 145505492449357)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (17, 1), (19, 1), (9511, 1), (303617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (17, 1), (19, 1), (9511, 1), (303617, 1)] : List FactorBlock).map factorBlockValue).prod) = 145505492449357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_13
      · exact prime_seventyNineBY_17
      · exact prime_seventyNineBY_19
      · exact prime_seventyNineBY_9511
      · exact prime_seventyNineBY_303617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 145505492449357) ^ 72752746224678 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 145505492449357) ^ 48501830816452 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 145505492449357) ^ 11192730188412 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 145505492449357) ^ 8559146614668 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 145505492449357) ^ 7658183813124 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 145505492449357) ^ 15298653396 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 145505492449357) ^ 479240268 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_149517847272323 : Nat.Prime 149517847272323 := by
  apply lucas_primality 149517847272323 (2 : ZMod 149517847272323)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (151, 1), (46957, 1), (10543523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (151, 1), (46957, 1), (10543523, 1)] : List FactorBlock).map factorBlockValue).prod) = 149517847272323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_151
      · exact prime_seventyNineBY_46957
      · exact prime_seventyNineBY_10543523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 149517847272323) ^ 74758923636161 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 149517847272323) ^ 990184419022 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 149517847272323) ^ 3184143946 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 149517847272323) ^ 14181014 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_254667657911617 : Nat.Prime 254667657911617 := by
  apply lucas_primality 254667657911617 (7 : ZMod 254667657911617)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (147377116847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (147377116847, 1)] : List FactorBlock).map factorBlockValue).prod) = 254667657911617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_147377116847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 254667657911617) ^ 127333828955808 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 254667657911617) ^ 84889219303872 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 254667657911617) ^ 1728 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_264057651101467 : Nat.Prime 264057651101467 := by
  apply lucas_primality 264057651101467 (3 : ZMod 264057651101467)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5167, 1), (946382137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5167, 1), (946382137, 1)] : List FactorBlock).map factorBlockValue).prod) = 264057651101467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_5167
      · exact prime_seventyNineBY_946382137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 264057651101467) ^ 132028825550733 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 264057651101467) ^ 88019217033822 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 264057651101467) ^ 51104635398 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 264057651101467) ^ 279018 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_346077501923033 : Nat.Prime 346077501923033 := by
  apply lucas_primality 346077501923033 (3 : ZMod 346077501923033)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 2), (83, 1), (2347, 1), (1835299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 2), (83, 1), (2347, 1), (1835299, 1)] : List FactorBlock).map factorBlockValue).prod) = 346077501923033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_11
      · exact prime_seventyNineBY_83
      · exact prime_seventyNineBY_2347
      · exact prime_seventyNineBY_1835299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 346077501923033) ^ 173038750961516 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 346077501923033) ^ 31461591083912 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 346077501923033) ^ 4169608456904 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 346077501923033) ^ 147455262856 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 346077501923033) ^ 188567368 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_346370014534391 : Nat.Prime 346370014534391 := by
  apply lucas_primality 346370014534391 (7 : ZMod 346370014534391)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (11, 2), (40893744337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (11, 2), (40893744337, 1)] : List FactorBlock).map factorBlockValue).prod) = 346370014534391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_11
      · exact prime_seventyNineBY_40893744337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 346370014534391) ^ 173185007267195 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 346370014534391) ^ 69274002906878 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 346370014534391) ^ 49481430647770 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 346370014534391) ^ 31488183139490 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 346370014534391) ^ 8470 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_365625350975977 : Nat.Prime 365625350975977 := by
  apply lucas_primality 365625350975977 (10 : ZMod 365625350975977)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (13, 1), (47041, 1), (3558829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (13, 1), (47041, 1), (3558829, 1)] : List FactorBlock).map factorBlockValue).prod) = 365625350975977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_13
      · exact prime_seventyNineBY_47041
      · exact prime_seventyNineBY_3558829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 365625350975977) ^ 182812675487988 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (10 : ZMod 365625350975977) ^ 121875116991992 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (10 : ZMod 365625350975977) ^ 52232192996568 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (10 : ZMod 365625350975977) ^ 28125026998152 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (10 : ZMod 365625350975977) ^ 7772482536 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (10 : ZMod 365625350975977) ^ 102737544 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_392872798156879 : Nat.Prime 392872798156879 := by
  apply lucas_primality 392872798156879 (3 : ZMod 392872798156879)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (1678943581867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (1678943581867, 1)] : List FactorBlock).map factorBlockValue).prod) = 392872798156879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_13
      · exact prime_seventyNineBY_1678943581867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 392872798156879) ^ 196436399078439 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 392872798156879) ^ 130957599385626 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 392872798156879) ^ 30220984473606 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 392872798156879) ^ 234 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_414073399688027 : Nat.Prime 414073399688027 := by
  apply lucas_primality 414073399688027 (2 : ZMod 414073399688027)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (17, 1), (1217, 1), (13001, 1), (59209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (17, 1), (1217, 1), (13001, 1), (59209, 1)] : List FactorBlock).map factorBlockValue).prod) = 414073399688027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_13
      · exact prime_seventyNineBY_17
      · exact prime_seventyNineBY_1217
      · exact prime_seventyNineBY_13001
      · exact prime_seventyNineBY_59209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 414073399688027) ^ 207036699844013 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 414073399688027) ^ 31851799976002 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 414073399688027) ^ 24357258805178 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 414073399688027) ^ 340241084378 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 414073399688027) ^ 31849350026 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 414073399688027) ^ 6993419914 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_490186919774413 : Nat.Prime 490186919774413 := by
  apply lucas_primality 490186919774413 (14 : ZMod 490186919774413)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (107, 1), (6059770061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (107, 1), (6059770061, 1)] : List FactorBlock).map factorBlockValue).prod) = 490186919774413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_107
      · exact prime_seventyNineBY_6059770061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 490186919774413) ^ 245093459887206 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (14 : ZMod 490186919774413) ^ 163395639924804 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (14 : ZMod 490186919774413) ^ 70026702824916 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (14 : ZMod 490186919774413) ^ 4581186166116 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (14 : ZMod 490186919774413) ^ 80892 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_563474057680349 : Nat.Prime 563474057680349 := by
  apply lucas_primality 563474057680349 (2 : ZMod 563474057680349)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 2), (79, 1), (2689, 1), (788497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 2), (79, 1), (2689, 1), (788497, 1)] : List FactorBlock).map factorBlockValue).prod) = 563474057680349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_29
      · exact prime_seventyNineBY_79
      · exact prime_seventyNineBY_2689
      · exact prime_seventyNineBY_788497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 563474057680349) ^ 281737028840174 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 563474057680349) ^ 19430139920012 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 563474057680349) ^ 7132583008612 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 563474057680349) ^ 209547808732 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 563474057680349) ^ 714617884 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_603607939583809 : Nat.Prime 603607939583809 := by
  apply lucas_primality 603607939583809 (14 : ZMod 603607939583809)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (150343, 1), (20910793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (150343, 1), (20910793, 1)] : List FactorBlock).map factorBlockValue).prod) = 603607939583809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_150343
      · exact prime_seventyNineBY_20910793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 603607939583809) ^ 301803969791904 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (14 : ZMod 603607939583809) ^ 201202646527936 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (14 : ZMod 603607939583809) ^ 4014872256 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (14 : ZMod 603607939583809) ^ 28865856 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_636739089760909 : Nat.Prime 636739089760909 := by
  apply lucas_primality 636739089760909 (2 : ZMod 636739089760909)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (73, 1), (167, 1), (483613511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (73, 1), (167, 1), (483613511, 1)] : List FactorBlock).map factorBlockValue).prod) = 636739089760909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_73
      · exact prime_seventyNineBY_167
      · exact prime_seventyNineBY_483613511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 636739089760909) ^ 318369544880454 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 636739089760909) ^ 212246363253636 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 636739089760909) ^ 8722453284396 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 636739089760909) ^ 3812808920724 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 636739089760909) ^ 1316628 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_759957047030939 : Nat.Prime 759957047030939 := by
  apply lucas_primality 759957047030939 (2 : ZMod 759957047030939)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (740143, 1), (513385283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (740143, 1), (513385283, 1)] : List FactorBlock).map factorBlockValue).prod) = 759957047030939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_740143
      · exact prime_seventyNineBY_513385283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 759957047030939) ^ 379978523515469 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 759957047030939) ^ 1026770566 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 759957047030939) ^ 1480286 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_823223359986133 : Nat.Prime 823223359986133 := by
  apply lucas_primality 823223359986133 (2 : ZMod 823223359986133)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (17, 1), (19, 1), (30341418251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (17, 1), (19, 1), (30341418251, 1)] : List FactorBlock).map factorBlockValue).prod) = 823223359986133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_17
      · exact prime_seventyNineBY_19
      · exact prime_seventyNineBY_30341418251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 823223359986133) ^ 411611679993066 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 823223359986133) ^ 274407786662044 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 823223359986133) ^ 117603337140876 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 823223359986133) ^ 48424903528596 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 823223359986133) ^ 43327545262428 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 823223359986133) ^ 27132 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_960004918792253 : Nat.Prime 960004918792253 := by
  apply lucas_primality 960004918792253 (2 : ZMod 960004918792253)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (8275904472347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (8275904472347, 1)] : List FactorBlock).map factorBlockValue).prod) = 960004918792253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_29
      · exact prime_seventyNineBY_8275904472347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 960004918792253) ^ 480002459396126 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 960004918792253) ^ 33103617889388 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 960004918792253) ^ 116 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_1060663812838457 : Nat.Prime 1060663812838457 := by
  apply lucas_primality 1060663812838457 (3 : ZMod 1060663812838457)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (6978051400253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (6978051400253, 1)] : List FactorBlock).map factorBlockValue).prod) = 1060663812838457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_19
      · exact prime_seventyNineBY_6978051400253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1060663812838457) ^ 530331906419228 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1060663812838457) ^ 55824411202024 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1060663812838457) ^ 152 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_1064744353947041 : Nat.Prime 1064744353947041 := by
  apply lucas_primality 1064744353947041 (3 : ZMod 1064744353947041)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (13, 1), (139, 1), (25189, 1), (146203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (13, 1), (139, 1), (25189, 1), (146203, 1)] : List FactorBlock).map factorBlockValue).prod) = 1064744353947041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_13
      · exact prime_seventyNineBY_139
      · exact prime_seventyNineBY_25189
      · exact prime_seventyNineBY_146203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1064744353947041) ^ 532372176973520 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1064744353947041) ^ 212948870789408 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1064744353947041) ^ 81903411842080 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1064744353947041) ^ 7660031323360 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1064744353947041) ^ 42270211360 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1064744353947041) ^ 7282643680 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_1094828315729933 : Nat.Prime 1094828315729933 := by
  apply lucas_primality 1094828315729933 (2 : ZMod 1094828315729933)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (73, 1), (355853, 1), (1505201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (73, 1), (355853, 1), (1505201, 1)] : List FactorBlock).map factorBlockValue).prod) = 1094828315729933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_73
      · exact prime_seventyNineBY_355853
      · exact prime_seventyNineBY_1505201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1094828315729933) ^ 547414157864966 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1094828315729933) ^ 156404045104276 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1094828315729933) ^ 14997648160684 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1094828315729933) ^ 3076630844 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1094828315729933) ^ 727363532 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_1177049037693547 : Nat.Prime 1177049037693547 := by
  apply lucas_primality 1177049037693547 (2 : ZMod 1177049037693547)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (131, 1), (4409, 1), (3652153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (131, 1), (4409, 1), (3652153, 1)] : List FactorBlock).map factorBlockValue).prod) = 1177049037693547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_31
      · exact prime_seventyNineBY_131
      · exact prime_seventyNineBY_4409
      · exact prime_seventyNineBY_3652153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1177049037693547) ^ 588524518846773 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1177049037693547) ^ 392349679231182 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1177049037693547) ^ 37969323796566 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1177049037693547) ^ 8985107157966 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1177049037693547) ^ 266965079994 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1177049037693547) ^ 322289082 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_1260814454270237 : Nat.Prime 1260814454270237 := by
  apply lucas_primality 1260814454270237 (2 : ZMod 1260814454270237)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (456503, 1), (18661469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (456503, 1), (18661469, 1)] : List FactorBlock).map factorBlockValue).prod) = 1260814454270237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_37
      · exact prime_seventyNineBY_456503
      · exact prime_seventyNineBY_18661469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1260814454270237) ^ 630407227135118 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1260814454270237) ^ 34076066331628 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1260814454270237) ^ 2761897412 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1260814454270237) ^ 67562444 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_1267334022826789 : Nat.Prime 1267334022826789 := by
  apply lucas_primality 1267334022826789 (18 : ZMod 1267334022826789)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (15087309795557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (15087309795557, 1)] : List FactorBlock).map factorBlockValue).prod) = 1267334022826789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_15087309795557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (18 : ZMod 1267334022826789) ^ 633667011413394 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (18 : ZMod 1267334022826789) ^ 422444674275596 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (18 : ZMod 1267334022826789) ^ 181047717546684 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (18 : ZMod 1267334022826789) ^ 84 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_2405108202917741 : Nat.Prime 2405108202917741 := by
  apply lucas_primality 2405108202917741 (2 : ZMod 2405108202917741)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (120255410145887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (120255410145887, 1)] : List FactorBlock).map factorBlockValue).prod) = 2405108202917741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_120255410145887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2405108202917741) ^ 1202554101458870 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2405108202917741) ^ 481021640583548 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2405108202917741) ^ 20 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_4887740285640073 : Nat.Prime 4887740285640073 := by
  apply lucas_primality 4887740285640073 (5 : ZMod 4887740285640073)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (17, 1), (181, 1), (271, 1), (11630029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (17, 1), (181, 1), (271, 1), (11630029, 1)] : List FactorBlock).map factorBlockValue).prod) = 4887740285640073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_17
      · exact prime_seventyNineBY_181
      · exact prime_seventyNineBY_271
      · exact prime_seventyNineBY_11630029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4887740285640073) ^ 2443870142820036 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 4887740285640073) ^ 1629246761880024 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 4887740285640073) ^ 698248612234296 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 4887740285640073) ^ 287514134449416 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 4887740285640073) ^ 27004089975912 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 4887740285640073) ^ 18035942013432 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 4887740285640073) ^ 420268968 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_6113977255479143 : Nat.Prime 6113977255479143 := by
  apply lucas_primality 6113977255479143 (5 : ZMod 6113977255479143)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (487, 1), (4051, 1), (221362769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (487, 1), (4051, 1), (221362769, 1)] : List FactorBlock).map factorBlockValue).prod) = 6113977255479143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_487
      · exact prime_seventyNineBY_4051
      · exact prime_seventyNineBY_221362769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6113977255479143) ^ 3056988627739571 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 6113977255479143) ^ 873425322211306 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 6113977255479143) ^ 12554368081066 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 6113977255479143) ^ 1509251359042 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 6113977255479143) ^ 27619718 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_6201877127138213 : Nat.Prime 6201877127138213 := by
  apply lucas_primality 6201877127138213 (2 : ZMod 6201877127138213)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (103, 1), (347, 1), (373, 1), (8946317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (103, 1), (347, 1), (373, 1), (8946317, 1)] : List FactorBlock).map factorBlockValue).prod) = 6201877127138213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_13
      · exact prime_seventyNineBY_103
      · exact prime_seventyNineBY_347
      · exact prime_seventyNineBY_373
      · exact prime_seventyNineBY_8946317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6201877127138213) ^ 3100938563569106 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 6201877127138213) ^ 477067471318324 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 6201877127138213) ^ 60212399292604 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 6201877127138213) ^ 17872844746796 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 6201877127138213) ^ 16627016426644 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 6201877127138213) ^ 693232436 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_6547941224199853 : Nat.Prime 6547941224199853 := by
  apply lucas_primality 6547941224199853 (2 : ZMod 6547941224199853)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (9311, 1), (58603991911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (9311, 1), (58603991911, 1)] : List FactorBlock).map factorBlockValue).prod) = 6547941224199853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_9311
      · exact prime_seventyNineBY_58603991911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6547941224199853) ^ 3273970612099926 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 6547941224199853) ^ 2182647074733284 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 6547941224199853) ^ 703247902932 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 6547941224199853) ^ 111732 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_6742022460886901 : Nat.Prime 6742022460886901 := by
  apply lucas_primality 6742022460886901 (2 : ZMod 6742022460886901)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (11, 1), (19, 1), (701, 1), (460178041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (11, 1), (19, 1), (701, 1), (460178041, 1)] : List FactorBlock).map factorBlockValue).prod) = 6742022460886901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_11
      · exact prime_seventyNineBY_19
      · exact prime_seventyNineBY_701
      · exact prime_seventyNineBY_460178041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6742022460886901) ^ 3371011230443450 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 6742022460886901) ^ 1348404492177380 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 6742022460886901) ^ 612911132807900 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 6742022460886901) ^ 354843287415100 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 6742022460886901) ^ 9617721056900 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 6742022460886901) ^ 14650900 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_8010724139263283 : Nat.Prime 8010724139263283 := by
  apply lucas_primality 8010724139263283 (2 : ZMod 8010724139263283)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (907, 1), (2003, 1), (2204720521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (907, 1), (2003, 1), (2204720521, 1)] : List FactorBlock).map factorBlockValue).prod) = 8010724139263283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_907
      · exact prime_seventyNineBY_2003
      · exact prime_seventyNineBY_2204720521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8010724139263283) ^ 4005362069631641 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 8010724139263283) ^ 8832110407126 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 8010724139263283) ^ 3999363025094 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 8010724139263283) ^ 3633442 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_8363477051136341 : Nat.Prime 8363477051136341 := by
  apply lucas_primality 8363477051136341 (3 : ZMod 8363477051136341)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (181, 1), (941, 1), (350744311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (181, 1), (941, 1), (350744311, 1)] : List FactorBlock).map factorBlockValue).prod) = 8363477051136341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_181
      · exact prime_seventyNineBY_941
      · exact prime_seventyNineBY_350744311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8363477051136341) ^ 4181738525568170 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 8363477051136341) ^ 1672695410227268 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 8363477051136341) ^ 1194782435876620 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 8363477051136341) ^ 46207055531140 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 8363477051136341) ^ 8887860840740 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 8363477051136341) ^ 23844940 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_8549797674932039 : Nat.Prime 8549797674932039 := by
  apply lucas_primality 8549797674932039 (7 : ZMod 8549797674932039)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (137, 1), (1775747, 1), (2510303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (137, 1), (1775747, 1), (2510303, 1)] : List FactorBlock).map factorBlockValue).prod) = 8549797674932039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_137
      · exact prime_seventyNineBY_1775747
      · exact prime_seventyNineBY_2510303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 8549797674932039) ^ 4274898837466019 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 8549797674932039) ^ 1221399667847434 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 8549797674932039) ^ 62407282298774 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 8549797674932039) ^ 4814761154 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 8549797674932039) ^ 3405882746 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_13128432222091171 : Nat.Prime 13128432222091171 := by
  apply lucas_primality 13128432222091171 (2 : ZMod 13128432222091171)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (127, 1), (767813, 1), (4487789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (127, 1), (767813, 1), (4487789, 1)] : List FactorBlock).map factorBlockValue).prod) = 13128432222091171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_127
      · exact prime_seventyNineBY_767813
      · exact prime_seventyNineBY_4487789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13128432222091171) ^ 6564216111045585 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 13128432222091171) ^ 4376144074030390 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 13128432222091171) ^ 2625686444418234 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 13128432222091171) ^ 103373482063710 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 13128432222091171) ^ 17098476090 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 13128432222091171) ^ 2925367530 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_15564110458748149 : Nat.Prime 15564110458748149 := by
  apply lucas_primality 15564110458748149 (2 : ZMod 15564110458748149)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (449, 1), (87535209887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (449, 1), (87535209887, 1)] : List FactorBlock).map factorBlockValue).prod) = 15564110458748149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_11
      · exact prime_seventyNineBY_449
      · exact prime_seventyNineBY_87535209887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15564110458748149) ^ 7782055229374074 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 15564110458748149) ^ 5188036819582716 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 15564110458748149) ^ 1414919132613468 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 15564110458748149) ^ 34663943115252 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 15564110458748149) ^ 177804 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_22630302906269089 : Nat.Prime 22630302906269089 := by
  apply lucas_primality 22630302906269089 (13 : ZMod 22630302906269089)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (17, 1), (53, 1), (261634097603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (17, 1), (53, 1), (261634097603, 1)] : List FactorBlock).map factorBlockValue).prod) = 22630302906269089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_17
      · exact prime_seventyNineBY_53
      · exact prime_seventyNineBY_261634097603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 22630302906269089) ^ 11315151453134544 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (13 : ZMod 22630302906269089) ^ 7543434302089696 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (13 : ZMod 22630302906269089) ^ 1331194288604064 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (13 : ZMod 22630302906269089) ^ 426986847288096 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (13 : ZMod 22630302906269089) ^ 86496 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_30710570677609217 : Nat.Prime 30710570677609217 := by
  apply lucas_primality 30710570677609217 (3 : ZMod 30710570677609217)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (37, 1), (919, 1), (31307, 1), (112691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (37, 1), (919, 1), (31307, 1), (112691, 1)] : List FactorBlock).map factorBlockValue).prod) = 30710570677609217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_37
      · exact prime_seventyNineBY_919
      · exact prime_seventyNineBY_31307
      · exact prime_seventyNineBY_112691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 30710570677609217) ^ 15355285338804608 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 30710570677609217) ^ 830015423719168 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 30710570677609217) ^ 33417378321664 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 30710570677609217) ^ 980949010688 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 30710570677609217) ^ 272520171776 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_32088124896863743 : Nat.Prime 32088124896863743 := by
  apply lucas_primality 32088124896863743 (10 : ZMod 32088124896863743)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (254667657911617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (254667657911617, 1)] : List FactorBlock).map factorBlockValue).prod) = 32088124896863743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_254667657911617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 32088124896863743) ^ 16044062448431871 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (10 : ZMod 32088124896863743) ^ 10696041632287914 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (10 : ZMod 32088124896863743) ^ 4584017842409106 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (10 : ZMod 32088124896863743) ^ 126 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_44982756200363453 : Nat.Prime 44982756200363453 := by
  apply lucas_primality 44982756200363453 (2 : ZMod 44982756200363453)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (66467, 1), (75731, 1), (2234119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (66467, 1), (75731, 1), (2234119, 1)] : List FactorBlock).map factorBlockValue).prod) = 44982756200363453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_66467
      · exact prime_seventyNineBY_75731
      · exact prime_seventyNineBY_2234119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 44982756200363453) ^ 22491378100181726 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 44982756200363453) ^ 676768263956 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 44982756200363453) ^ 593980750292 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 44982756200363453) ^ 20134449508 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_88232805698677301 : Nat.Prime 88232805698677301 := by
  apply lucas_primality 88232805698677301 (2 : ZMod 88232805698677301)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (29, 1), (30425105413337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (29, 1), (30425105413337, 1)] : List FactorBlock).map factorBlockValue).prod) = 88232805698677301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_29
      · exact prime_seventyNineBY_30425105413337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 88232805698677301) ^ 44116402849338650 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 88232805698677301) ^ 17646561139735460 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 88232805698677301) ^ 3042510541333700 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 88232805698677301) ^ 2900 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_101894103778367561 : Nat.Prime 101894103778367561 := by
  apply lucas_primality 101894103778367561 (3 : ZMod 101894103778367561)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 1), (7559, 1), (65809, 1), (465529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 1), (7559, 1), (65809, 1), (465529, 1)] : List FactorBlock).map factorBlockValue).prod) = 101894103778367561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_11
      · exact prime_seventyNineBY_7559
      · exact prime_seventyNineBY_65809
      · exact prime_seventyNineBY_465529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 101894103778367561) ^ 50947051889183780 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 101894103778367561) ^ 20378820755673512 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 101894103778367561) ^ 9263100343487960 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 101894103778367561) ^ 13479839102840 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 101894103778367561) ^ 1548330832840 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 101894103778367561) ^ 218878101640 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_103508258019066227 : Nat.Prime 103508258019066227 := by
  apply lucas_primality 103508258019066227 (2 : ZMod 103508258019066227)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (739, 1), (70032650892467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (739, 1), (70032650892467, 1)] : List FactorBlock).map factorBlockValue).prod) = 103508258019066227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_739
      · exact prime_seventyNineBY_70032650892467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 103508258019066227) ^ 51754129009533113 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 103508258019066227) ^ 140065301784934 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 103508258019066227) ^ 1478 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_123835942213311001 : Nat.Prime 123835942213311001 := by
  apply lucas_primality 123835942213311001 (13 : ZMod 123835942213311001)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 3), (41, 1), (1006796278157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 3), (41, 1), (1006796278157, 1)] : List FactorBlock).map factorBlockValue).prod) = 123835942213311001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_41
      · exact prime_seventyNineBY_1006796278157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 123835942213311001) ^ 61917971106655500 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (13 : ZMod 123835942213311001) ^ 41278647404437000 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (13 : ZMod 123835942213311001) ^ 24767188442662200 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (13 : ZMod 123835942213311001) ^ 3020388834471000 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (13 : ZMod 123835942213311001) ^ 123000 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_135655986992320213 : Nat.Prime 135655986992320213 := by
  apply lucas_primality 135655986992320213 (17 : ZMod 135655986992320213)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (23, 1), (3701, 1), (83089, 1), (145303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (23, 1), (3701, 1), (83089, 1), (145303, 1)] : List FactorBlock).map factorBlockValue).prod) = 135655986992320213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_11
      · exact prime_seventyNineBY_23
      · exact prime_seventyNineBY_3701
      · exact prime_seventyNineBY_83089
      · exact prime_seventyNineBY_145303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 135655986992320213) ^ 67827993496160106 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (17 : ZMod 135655986992320213) ^ 45218662330773404 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (17 : ZMod 135655986992320213) ^ 12332362453847292 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (17 : ZMod 135655986992320213) ^ 5898086390970444 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (17 : ZMod 135655986992320213) ^ 36653873815812 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (17 : ZMod 135655986992320213) ^ 1632658799508 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (17 : ZMod 135655986992320213) ^ 933607613004 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_138791132155861099 : Nat.Prime 138791132155861099 := by
  apply lucas_primality 138791132155861099 (2 : ZMod 138791132155861099)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (5149853, 1), (144895181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (5149853, 1), (144895181, 1)] : List FactorBlock).map factorBlockValue).prod) = 138791132155861099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_31
      · exact prime_seventyNineBY_5149853
      · exact prime_seventyNineBY_144895181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 138791132155861099) ^ 69395566077930549 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 138791132155861099) ^ 46263710718620366 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 138791132155861099) ^ 4477133295350358 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 138791132155861099) ^ 26950503666 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 138791132155861099) ^ 957872658 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_160661307025109687 : Nat.Prime 160661307025109687 := by
  apply lucas_primality 160661307025109687 (5 : ZMod 160661307025109687)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3593, 1), (22357543421251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3593, 1), (22357543421251, 1)] : List FactorBlock).map factorBlockValue).prod) = 160661307025109687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3593
      · exact prime_seventyNineBY_22357543421251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 160661307025109687) ^ 80330653512554843 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 160661307025109687) ^ 44715086842502 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 160661307025109687) ^ 7186 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_230448003133509923 : Nat.Prime 230448003133509923 := by
  apply lucas_primality 230448003133509923 (2 : ZMod 230448003133509923)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (71, 1), (131, 1), (211, 1), (2129, 1), (1622207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (71, 1), (131, 1), (211, 1), (2129, 1), (1622207, 1)] : List FactorBlock).map factorBlockValue).prod) = 230448003133509923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_17
      · exact prime_seventyNineBY_71
      · exact prime_seventyNineBY_131
      · exact prime_seventyNineBY_211
      · exact prime_seventyNineBY_2129
      · exact prime_seventyNineBY_1622207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 230448003133509923) ^ 115224001566754961 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 230448003133509923) ^ 13555764890206466 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 230448003133509923) ^ 3245746523007182 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 230448003133509923) ^ 1759145062087862 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 230448003133509923) ^ 1092170630964502 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 230448003133509923) ^ 108242368780418 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 230448003133509923) ^ 142058321246 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_545400436298251879 : Nat.Prime 545400436298251879 := by
  apply lucas_primality 545400436298251879 (7 : ZMod 545400436298251879)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7741, 1), (1304742033277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7741, 1), (1304742033277, 1)] : List FactorBlock).map factorBlockValue).prod) = 545400436298251879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_7741
      · exact prime_seventyNineBY_1304742033277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 545400436298251879) ^ 272700218149125939 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 545400436298251879) ^ 181800145432750626 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 545400436298251879) ^ 70456069796958 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 545400436298251879) ^ 418014 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_624734757346673453 : Nat.Prime 624734757346673453 := by
  apply lucas_primality 624734757346673453 (2 : ZMod 624734757346673453)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4861, 1), (14621, 1), (2197520723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4861, 1), (14621, 1), (2197520723, 1)] : List FactorBlock).map factorBlockValue).prod) = 624734757346673453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_4861
      · exact prime_seventyNineBY_14621
      · exact prime_seventyNineBY_2197520723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 624734757346673453) ^ 312367378673336726 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 624734757346673453) ^ 128519801963932 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 624734757346673453) ^ 42728592938012 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 624734757346673453) ^ 284290724 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_652893148010813533 : Nat.Prime 652893148010813533 := by
  apply lucas_primality 652893148010813533 (5 : ZMod 652893148010813533)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (509, 1), (306827, 1), (18335633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (509, 1), (306827, 1), (18335633, 1)] : List FactorBlock).map factorBlockValue).prod) = 652893148010813533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_19
      · exact prime_seventyNineBY_509
      · exact prime_seventyNineBY_306827
      · exact prime_seventyNineBY_18335633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 652893148010813533) ^ 326446574005406766 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 652893148010813533) ^ 217631049336937844 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 652893148010813533) ^ 34362797263727028 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 652893148010813533) ^ 1282697736759948 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 652893148010813533) ^ 2127886880916 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 652893148010813533) ^ 35607887004 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_1341617639466577619 : Nat.Prime 1341617639466577619 := by
  apply lucas_primality 1341617639466577619 (2 : ZMod 1341617639466577619)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (107, 1), (331, 1), (266764874087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (107, 1), (331, 1), (266764874087, 1)] : List FactorBlock).map factorBlockValue).prod) = 1341617639466577619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_71
      · exact prime_seventyNineBY_107
      · exact prime_seventyNineBY_331
      · exact prime_seventyNineBY_266764874087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1341617639466577619) ^ 670808819733288809 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1341617639466577619) ^ 18896023091078558 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1341617639466577619) ^ 12538482611837174 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1341617639466577619) ^ 4053225496877878 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1341617639466577619) ^ 5029214 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_1878222622321873621 : Nat.Prime 1878222622321873621 := by
  apply lucas_primality 1878222622321873621 (6 : ZMod 1878222622321873621)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (5, 1), (13, 1), (367261, 1), (242836457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (5, 1), (13, 1), (367261, 1), (242836457, 1)] : List FactorBlock).map factorBlockValue).prod) = 1878222622321873621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_13
      · exact prime_seventyNineBY_367261
      · exact prime_seventyNineBY_242836457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1878222622321873621) ^ 939111311160936810 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1878222622321873621) ^ 626074207440624540 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1878222622321873621) ^ 375644524464374724 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1878222622321873621) ^ 144478663255528740 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1878222622321873621) ^ 5114135784420 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1878222622321873621) ^ 7734516660 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_2683235278933155239 : Nat.Prime 2683235278933155239 := by
  apply lucas_primality 2683235278933155239 (13 : ZMod 2683235278933155239)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1341617639466577619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1341617639466577619, 1)] : List FactorBlock).map factorBlockValue).prod) = 2683235278933155239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_1341617639466577619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (13 : ZMod 2683235278933155239) ^ 1341617639466577619 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (13 : ZMod 2683235278933155239) ^ 2 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_2726413969369998521 : Nat.Prime 2726413969369998521 := by
  apply lucas_primality 2726413969369998521 (3 : ZMod 2726413969369998521)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (71, 1), (960004918792253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (71, 1), (960004918792253, 1)] : List FactorBlock).map factorBlockValue).prod) = 2726413969369998521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_71
      · exact prime_seventyNineBY_960004918792253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2726413969369998521) ^ 1363206984684999260 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2726413969369998521) ^ 545282793873999704 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2726413969369998521) ^ 38400196751690120 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2726413969369998521) ^ 2840 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_3270074974395325843 : Nat.Prime 3270074974395325843 := by
  apply lucas_primality 3270074974395325843 (2 : ZMod 3270074974395325843)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47328773, 1), (11515457959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47328773, 1), (11515457959, 1)] : List FactorBlock).map factorBlockValue).prod) = 3270074974395325843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_47328773
      · exact prime_seventyNineBY_11515457959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3270074974395325843) ^ 1635037487197662921 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3270074974395325843) ^ 1090024991465108614 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3270074974395325843) ^ 69092747754 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3270074974395325843) ^ 283972638 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_3742539667222142687 : Nat.Prime 3742539667222142687 := by
  apply lucas_primality 3742539667222142687 (5 : ZMod 3742539667222142687)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (421, 1), (10307849, 1), (14869223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (421, 1), (10307849, 1), (14869223, 1)] : List FactorBlock).map factorBlockValue).prod) = 3742539667222142687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_29
      · exact prime_seventyNineBY_421
      · exact prime_seventyNineBY_10307849
      · exact prime_seventyNineBY_14869223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3742539667222142687) ^ 1871269833611071343 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 3742539667222142687) ^ 129053091973177334 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 3742539667222142687) ^ 8889642915016966 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 3742539667222142687) ^ 363076687214 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 3742539667222142687) ^ 251697056882 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_3772499810716720327 : Nat.Prime 3772499810716720327 := by
  apply lucas_primality 3772499810716720327 (3 : ZMod 3772499810716720327)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (25261, 1), (421866874879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (25261, 1), (421866874879, 1)] : List FactorBlock).map factorBlockValue).prod) = 3772499810716720327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_59
      · exact prime_seventyNineBY_25261
      · exact prime_seventyNineBY_421866874879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3772499810716720327) ^ 1886249905358360163 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3772499810716720327) ^ 1257499936905573442 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3772499810716720327) ^ 63940674757910514 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3772499810716720327) ^ 149340873707166 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3772499810716720327) ^ 8942394 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_3933862087086176899 : Nat.Prime 3933862087086176899 := by
  apply lucas_primality 3933862087086176899 (2 : ZMod 3933862087086176899)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (449, 1), (7451, 1), (8419, 1), (23278043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (449, 1), (7451, 1), (8419, 1), (23278043, 1)] : List FactorBlock).map factorBlockValue).prod) = 3933862087086176899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_449
      · exact prime_seventyNineBY_7451
      · exact prime_seventyNineBY_8419
      · exact prime_seventyNineBY_23278043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3933862087086176899) ^ 1966931043543088449 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3933862087086176899) ^ 1311287362362058966 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3933862087086176899) ^ 8761385494624002 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3933862087086176899) ^ 527964311781798 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3933862087086176899) ^ 467260017470742 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3933862087086176899) ^ 168994536486 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_4108667690368227179 : Nat.Prime 4108667690368227179 := by
  apply lucas_primality 4108667690368227179 (2 : ZMod 4108667690368227179)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (562417, 1), (3652688032517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (562417, 1), (3652688032517, 1)] : List FactorBlock).map factorBlockValue).prod) = 4108667690368227179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_562417
      · exact prime_seventyNineBY_3652688032517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4108667690368227179) ^ 2054333845184113589 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4108667690368227179) ^ 7305376065034 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4108667690368227179) ^ 1124834 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_5303099380192293347 : Nat.Prime 5303099380192293347 := by
  apply lucas_primality 5303099380192293347 (2 : ZMod 5303099380192293347)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (331, 1), (8010724139263283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (331, 1), (8010724139263283, 1)] : List FactorBlock).map factorBlockValue).prod) = 5303099380192293347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_331
      · exact prime_seventyNineBY_8010724139263283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5303099380192293347) ^ 2651549690096146673 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 5303099380192293347) ^ 16021448278526566 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 5303099380192293347) ^ 662 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_5452827938739997043 : Nat.Prime 5452827938739997043 := by
  apply lucas_primality 5452827938739997043 (2 : ZMod 5452827938739997043)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2726413969369998521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2726413969369998521, 1)] : List FactorBlock).map factorBlockValue).prod) = 5452827938739997043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_2726413969369998521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 5452827938739997043) ^ 2726413969369998521 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 5452827938739997043) ^ 2 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_10841172117106136809 : Nat.Prime 10841172117106136809 := by
  apply lucas_primality 10841172117106136809 (14 : ZMod 10841172117106136809)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (67, 1), (6742022460886901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (67, 1), (6742022460886901, 1)] : List FactorBlock).map factorBlockValue).prod) = 10841172117106136809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_67
      · exact prime_seventyNineBY_6742022460886901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 10841172117106136809) ^ 5420586058553068404 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (14 : ZMod 10841172117106136809) ^ 3613724039035378936 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (14 : ZMod 10841172117106136809) ^ 161808539061285624 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (14 : ZMod 10841172117106136809) ^ 1608 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_12710995133056068689 : Nat.Prime 12710995133056068689 := by
  apply lucas_primality 12710995133056068689 (3 : ZMod 12710995133056068689)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (107, 1), (1060663812838457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (107, 1), (1060663812838457, 1)] : List FactorBlock).map factorBlockValue).prod) = 12710995133056068689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_107
      · exact prime_seventyNineBY_1060663812838457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 12710995133056068689) ^ 6355497566528034344 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 12710995133056068689) ^ 1815856447579438384 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 12710995133056068689) ^ 118794347037907184 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 12710995133056068689) ^ 11984 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_27900130712833844203 : Nat.Prime 27900130712833844203 := by
  apply lucas_primality 27900130712833844203 (3 : ZMod 27900130712833844203)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (472111, 1), (9849424786697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (472111, 1), (9849424786697, 1)] : List FactorBlock).map factorBlockValue).prod) = 27900130712833844203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_472111
      · exact prime_seventyNineBY_9849424786697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 27900130712833844203) ^ 13950065356416922101 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 27900130712833844203) ^ 9300043570944614734 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 27900130712833844203) ^ 59096548720182 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 27900130712833844203) ^ 2832666 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_68226787924528252777 : Nat.Prime 68226787924528252777 := by
  apply lucas_primality 68226787924528252777 (5 : ZMod 68226787924528252777)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19013, 1), (149517847272323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19013, 1), (149517847272323, 1)] : List FactorBlock).map factorBlockValue).prod) = 68226787924528252777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_19013
      · exact prime_seventyNineBY_149517847272323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 68226787924528252777) ^ 34113393962264126388 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 68226787924528252777) ^ 22742262641509417592 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 68226787924528252777) ^ 3588428334535752 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 68226787924528252777) ^ 456312 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_81882273105130179379 : Nat.Prime 81882273105130179379 := by
  apply lucas_primality 81882273105130179379 (2 : ZMod 81882273105130179379)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (977, 1), (1291, 1), (470424571583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (977, 1), (1291, 1), (470424571583, 1)] : List FactorBlock).map factorBlockValue).prod) = 81882273105130179379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_23
      · exact prime_seventyNineBY_977
      · exact prime_seventyNineBY_1291
      · exact prime_seventyNineBY_470424571583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 81882273105130179379) ^ 40941136552565089689 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 81882273105130179379) ^ 27294091035043393126 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 81882273105130179379) ^ 3560098830657833886 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 81882273105130179379) ^ 83809900824084114 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 81882273105130179379) ^ 63425463288249558 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 81882273105130179379) ^ 174060366 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_83742414943250482883 : Nat.Prime 83742414943250482883 := by
  apply lucas_primality 83742414943250482883 (2 : ZMod 83742414943250482883)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (277, 1), (284129, 1), (532010438077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (277, 1), (284129, 1), (532010438077, 1)] : List FactorBlock).map factorBlockValue).prod) = 83742414943250482883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_277
      · exact prime_seventyNineBY_284129
      · exact prime_seventyNineBY_532010438077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 83742414943250482883) ^ 41871207471625241441 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 83742414943250482883) ^ 302319187520759866 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 83742414943250482883) ^ 294733782694658 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 83742414943250482883) ^ 157407466 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_90468014356185501281 : Nat.Prime 90468014356185501281 := by
  apply lucas_primality 90468014356185501281 (6 : ZMod 90468014356185501281)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (7, 1), (227, 1), (62581, 1), (5686023887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (7, 1), (227, 1), (62581, 1), (5686023887, 1)] : List FactorBlock).map factorBlockValue).prod) = 90468014356185501281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_227
      · exact prime_seventyNineBY_62581
      · exact prime_seventyNineBY_5686023887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 90468014356185501281) ^ 45234007178092750640 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 90468014356185501281) ^ 18093602871237100256 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 90468014356185501281) ^ 12924002050883643040 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 90468014356185501281) ^ 398537508177028640 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 90468014356185501281) ^ 1445614713030880 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 90468014356185501281) ^ 15910593440 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_105868052876033123339 : Nat.Prime 105868052876033123339 := by
  apply lucas_primality 105868052876033123339 (2 : ZMod 105868052876033123339)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (1693, 1), (2405108202917741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (1693, 1), (2405108202917741, 1)] : List FactorBlock).map factorBlockValue).prod) = 105868052876033123339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_13
      · exact prime_seventyNineBY_1693
      · exact prime_seventyNineBY_2405108202917741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 105868052876033123339) ^ 52934026438016561669 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 105868052876033123339) ^ 8143696375079471026 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 105868052876033123339) ^ 62532813275861266 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 105868052876033123339) ^ 44018 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_226293884242693283999 : Nat.Prime 226293884242693283999 := by
  apply lucas_primality 226293884242693283999 (11 : ZMod 226293884242693283999)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (89, 1), (653, 1), (13033, 1), (2046314483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (89, 1), (653, 1), (13033, 1), (2046314483, 1)] : List FactorBlock).map factorBlockValue).prod) = 226293884242693283999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_73
      · exact prime_seventyNineBY_89
      · exact prime_seventyNineBY_653
      · exact prime_seventyNineBY_13033
      · exact prime_seventyNineBY_2046314483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 226293884242693283999) ^ 113146942121346641999 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (11 : ZMod 226293884242693283999) ^ 3099916222502647726 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (11 : ZMod 226293884242693283999) ^ 2542627912839250382 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (11 : ZMod 226293884242693283999) ^ 346544998840265366 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (11 : ZMod 226293884242693283999) ^ 17363146186042606 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (11 : ZMod 226293884242693283999) ^ 110586073706 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_240733444377293502737 : Nat.Prime 240733444377293502737 := by
  apply lucas_primality 240733444377293502737 (3 : ZMod 240733444377293502737)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (41, 1), (67, 1), (2029669, 1), (2698563047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (41, 1), (67, 1), (2029669, 1), (2698563047, 1)] : List FactorBlock).map factorBlockValue).prod) = 240733444377293502737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_41
      · exact prime_seventyNineBY_67
      · exact prime_seventyNineBY_2029669
      · exact prime_seventyNineBY_2698563047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 240733444377293502737) ^ 120366722188646751368 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 240733444377293502737) ^ 5871547423836426896 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 240733444377293502737) ^ 3593036483243186608 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 240733444377293502737) ^ 118607243041744 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 240733444377293502737) ^ 89208011888 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_249325482782017807597 : Nat.Prime 249325482782017807597 := by
  apply lucas_primality 249325482782017807597 (2 : ZMod 249325482782017807597)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (61, 1), (1249, 1), (90901676817599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (61, 1), (1249, 1), (90901676817599, 1)] : List FactorBlock).map factorBlockValue).prod) = 249325482782017807597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_61
      · exact prime_seventyNineBY_1249
      · exact prime_seventyNineBY_90901676817599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 249325482782017807597) ^ 124662741391008903798 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 249325482782017807597) ^ 83108494260672602532 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 249325482782017807597) ^ 4087302996426521436 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 249325482782017807597) ^ 199620082291447404 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 249325482782017807597) ^ 2742804 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_305358364569439834409 : Nat.Prime 305358364569439834409 := by
  apply lucas_primality 305358364569439834409 (3 : ZMod 305358364569439834409)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (5452827938739997043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (5452827938739997043, 1)] : List FactorBlock).map factorBlockValue).prod) = 305358364569439834409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_5452827938739997043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 305358364569439834409) ^ 152679182284719917204 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 305358364569439834409) ^ 43622623509919976344 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 305358364569439834409) ^ 56 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_490639452174366055741 : Nat.Prime 490639452174366055741 := by
  apply lucas_primality 490639452174366055741 (6 : ZMod 490639452174366055741)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 5), (5, 1), (7549, 1), (2802853, 1), (4771297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 5), (5, 1), (7549, 1), (2802853, 1), (4771297, 1)] : List FactorBlock).map factorBlockValue).prod) = 490639452174366055741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_7549
      · exact prime_seventyNineBY_2802853
      · exact prime_seventyNineBY_4771297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 490639452174366055741) ^ 245319726087183027870 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 490639452174366055741) ^ 163546484058122018580 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 490639452174366055741) ^ 98127890434873211148 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 490639452174366055741) ^ 64993966376257260 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 490639452174366055741) ^ 175050012317580 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 490639452174366055741) ^ 102831463263420 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_1348327632105326364077 : Nat.Prime 1348327632105326364077 := by
  apply lucas_primality 1348327632105326364077 (2 : ZMod 1348327632105326364077)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (4241, 1), (6113977255479143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (4241, 1), (6113977255479143, 1)] : List FactorBlock).map factorBlockValue).prod) = 1348327632105326364077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_13
      · exact prime_seventyNineBY_4241
      · exact prime_seventyNineBY_6113977255479143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1348327632105326364077) ^ 674163816052663182038 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348327632105326364077) ^ 103717510161948181852 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348327632105326364077) ^ 317926817284915436 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348327632105326364077) ^ 220532 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_2535182003400352098797 : Nat.Prime 2535182003400352098797 := by
  apply lucas_primality 2535182003400352098797 (2 : ZMod 2535182003400352098797)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (53, 2), (331, 1), (18423311487013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (53, 2), (331, 1), (18423311487013, 1)] : List FactorBlock).map factorBlockValue).prod) = 2535182003400352098797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_37
      · exact prime_seventyNineBY_53
      · exact prime_seventyNineBY_331
      · exact prime_seventyNineBY_18423311487013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2535182003400352098797) ^ 1267591001700176049398 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2535182003400352098797) ^ 68518432524333840508 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2535182003400352098797) ^ 47833622705667020732 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2535182003400352098797) ^ 7659160131118888516 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2535182003400352098797) ^ 137607292 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_2693915004824663545273 : Nat.Prime 2693915004824663545273 := by
  apply lucas_primality 2693915004824663545273 (7 : ZMod 2693915004824663545273)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (43, 1), (227, 1), (19441, 1), (29131, 1), (20305063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (43, 1), (227, 1), (19441, 1), (29131, 1), (20305063, 1)] : List FactorBlock).map factorBlockValue).prod) = 2693915004824663545273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_43
      · exact prime_seventyNineBY_227
      · exact prime_seventyNineBY_19441
      · exact prime_seventyNineBY_29131
      · exact prime_seventyNineBY_20305063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2693915004824663545273) ^ 1346957502412331772636 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2693915004824663545273) ^ 897971668274887848424 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2693915004824663545273) ^ 62649186158713105704 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2693915004824663545273) ^ 11867466981606447336 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2693915004824663545273) ^ 138568746711828792 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2693915004824663545273) ^ 92475884961884712 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2693915004824663545273) ^ 132672083057544 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_7881788539169832498823 : Nat.Prime 7881788539169832498823 := by
  apply lucas_primality 7881788539169832498823 (3 : ZMod 7881788539169832498823)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (13, 1), (3742539667222142687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (13, 1), (3742539667222142687, 1)] : List FactorBlock).map factorBlockValue).prod) = 7881788539169832498823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_13
      · exact prime_seventyNineBY_3742539667222142687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7881788539169832498823) ^ 3940894269584916249411 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 7881788539169832498823) ^ 2627262846389944166274 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 7881788539169832498823) ^ 606291426089987115294 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 7881788539169832498823) ^ 2106 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_9616260478029920529517 : Nat.Prime 9616260478029920529517 := by
  apply lucas_primality 9616260478029920529517 (2 : ZMod 9616260478029920529517)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (151, 1), (11497, 1), (11835834585121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (151, 1), (11497, 1), (11835834585121, 1)] : List FactorBlock).map factorBlockValue).prod) = 9616260478029920529517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_13
      · exact prime_seventyNineBY_151
      · exact prime_seventyNineBY_11497
      · exact prime_seventyNineBY_11835834585121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9616260478029920529517) ^ 4808130239014960264758 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 9616260478029920529517) ^ 3205420159343306843172 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 9616260478029920529517) ^ 739712344463840040732 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 9616260478029920529517) ^ 63683844225363712116 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 9616260478029920529517) ^ 836414758461330828 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 9616260478029920529517) ^ 812469996 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_10647897133022493017909 : Nat.Prime 10647897133022493017909 := by
  apply lucas_primality 10647897133022493017909 (2 : ZMod 10647897133022493017909)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (417733, 1), (490186919774413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (417733, 1), (490186919774413, 1)] : List FactorBlock).map factorBlockValue).prod) = 10647897133022493017909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_13
      · exact prime_seventyNineBY_417733
      · exact prime_seventyNineBY_490186919774413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10647897133022493017909) ^ 5323948566511246508954 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 10647897133022493017909) ^ 819069010232499462916 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 10647897133022493017909) ^ 25489719828269476 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 10647897133022493017909) ^ 21722116 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_13352874448026638349917 : Nat.Prime 13352874448026638349917 := by
  apply lucas_primality 13352874448026638349917 (2 : ZMod 13352874448026638349917)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (13, 1), (1621, 1), (22630302906269089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (13, 1), (1621, 1), (22630302906269089, 1)] : List FactorBlock).map factorBlockValue).prod) = 13352874448026638349917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_13
      · exact prime_seventyNineBY_1621
      · exact prime_seventyNineBY_22630302906269089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13352874448026638349917) ^ 6676437224013319174958 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 13352874448026638349917) ^ 1907553492575234049988 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 13352874448026638349917) ^ 1027144188309741411532 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 13352874448026638349917) ^ 8237430257881948396 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 13352874448026638349917) ^ 590044 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_17338232857373066133829 : Nat.Prime 17338232857373066133829 := by
  apply lucas_primality 17338232857373066133829 (2 : ZMod 17338232857373066133829)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (57663869, 1), (8352155131517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (57663869, 1), (8352155131517, 1)] : List FactorBlock).map factorBlockValue).prod) = 17338232857373066133829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_57663869
      · exact prime_seventyNineBY_8352155131517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17338232857373066133829) ^ 8669116428686533066914 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 17338232857373066133829) ^ 5779410952457688711276 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 17338232857373066133829) ^ 300677584734612 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 17338232857373066133829) ^ 2075899284 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_35148193554842996948549 : Nat.Prime 35148193554842996948549 := by
  apply lucas_primality 35148193554842996948549 (2 : ZMod 35148193554842996948549)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (83, 1), (105868052876033123339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (83, 1), (105868052876033123339, 1)] : List FactorBlock).map factorBlockValue).prod) = 35148193554842996948549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_83
      · exact prime_seventyNineBY_105868052876033123339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 35148193554842996948549) ^ 17574096777421498474274 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 35148193554842996948549) ^ 423472211504132493356 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 35148193554842996948549) ^ 332 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_49226511025804625088689 : Nat.Prime 49226511025804625088689 := by
  apply lucas_primality 49226511025804625088689 (3 : ZMod 49226511025804625088689)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 2), (181277, 1), (346370014534391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 2), (181277, 1), (346370014534391, 1)] : List FactorBlock).map factorBlockValue).prod) = 49226511025804625088689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_181277
      · exact prime_seventyNineBY_346370014534391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 49226511025804625088689) ^ 24613255512902312544344 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 49226511025804625088689) ^ 7032358717972089298384 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 49226511025804625088689) ^ 271554091394962544 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 49226511025804625088689) ^ 142121168 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_96416535746856590592583 : Nat.Prime 96416535746856590592583 := by
  apply lucas_primality 96416535746856590592583 (6 : ZMod 96416535746856590592583)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (347, 1), (36259649, 1), (1277165570099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (347, 1), (36259649, 1), (1277165570099, 1)] : List FactorBlock).map factorBlockValue).prod) = 96416535746856590592583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_347
      · exact prime_seventyNineBY_36259649
      · exact prime_seventyNineBY_1277165570099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 96416535746856590592583) ^ 48208267873428295296291 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 96416535746856590592583) ^ 32138845248952196864194 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 96416535746856590592583) ^ 277857451720047811506 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 96416535746856590592583) ^ 2659058716946118 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 96416535746856590592583) ^ 75492589218 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_106985982687485571909143 : Nat.Prime 106985982687485571909143 := by
  apply lucas_primality 106985982687485571909143 (5 : ZMod 106985982687485571909143)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (19, 1), (1877, 1), (88232805698677301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (19, 1), (1877, 1), (88232805698677301, 1)] : List FactorBlock).map factorBlockValue).prod) = 106985982687485571909143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_17
      · exact prime_seventyNineBY_19
      · exact prime_seventyNineBY_1877
      · exact prime_seventyNineBY_88232805698677301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 106985982687485571909143) ^ 53492991343742785954571 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 106985982687485571909143) ^ 6293293099263857171126 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 106985982687485571909143) ^ 5630841194078187995218 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 106985982687485571909143) ^ 56998392481345536446 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 106985982687485571909143) ^ 1212542 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_338332604658179168553587 : Nat.Prime 338332604658179168553587 := by
  apply lucas_primality 338332604658179168553587 (2 : ZMod 338332604658179168553587)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (101, 1), (383, 1), (624734757346673453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (101, 1), (383, 1), (624734757346673453, 1)] : List FactorBlock).map factorBlockValue).prod) = 338332604658179168553587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_101
      · exact prime_seventyNineBY_383
      · exact prime_seventyNineBY_624734757346673453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 338332604658179168553587) ^ 169166302329089584276793 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 338332604658179168553587) ^ 48333229236882738364798 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 338332604658179168553587) ^ 3349827768892863054986 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 338332604658179168553587) ^ 883374946888196262542 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 338332604658179168553587) ^ 541562 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_397018860043625603008691 : Nat.Prime 397018860043625603008691 := by
  apply lucas_primality 397018860043625603008691 (2 : ZMod 397018860043625603008691)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1423, 1), (27900130712833844203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1423, 1), (27900130712833844203, 1)] : List FactorBlock).map factorBlockValue).prod) = 397018860043625603008691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_1423
      · exact prime_seventyNineBY_27900130712833844203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 397018860043625603008691) ^ 198509430021812801504345 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 397018860043625603008691) ^ 79403772008725120601738 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 397018860043625603008691) ^ 279001307128338442030 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 397018860043625603008691) ^ 14230 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_576975628681795231771021 : Nat.Prime 576975628681795231771021 := by
  apply lucas_primality 576975628681795231771021 (7 : ZMod 576975628681795231771021)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (9616260478029920529517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (9616260478029920529517, 1)] : List FactorBlock).map factorBlockValue).prod) = 576975628681795231771021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_9616260478029920529517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 576975628681795231771021) ^ 288487814340897615885510 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 576975628681795231771021) ^ 192325209560598410590340 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 576975628681795231771021) ^ 115395125736359046354204 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (7 : ZMod 576975628681795231771021) ^ 60 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_747760969089491747595353 : Nat.Prime 747760969089491747595353 := by
  apply lucas_primality 747760969089491747595353 (3 : ZMod 747760969089491747595353)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (13352874448026638349917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (13352874448026638349917, 1)] : List FactorBlock).map factorBlockValue).prod) = 747760969089491747595353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_13352874448026638349917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 747760969089491747595353) ^ 373880484544745873797676 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 747760969089491747595353) ^ 106822995584213106799336 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 747760969089491747595353) ^ 56 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_2121163786430844993036827 : Nat.Prime 2121163786430844993036827 := by
  apply lucas_primality 2121163786430844993036827 (2 : ZMod 2121163786430844993036827)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (96416535746856590592583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (96416535746856590592583, 1)] : List FactorBlock).map factorBlockValue).prod) = 2121163786430844993036827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_11
      · exact prime_seventyNineBY_96416535746856590592583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2121163786430844993036827) ^ 1060581893215422496518413 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2121163786430844993036827) ^ 192833071493713181185166 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2121163786430844993036827) ^ 22 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_4857451832958340271135717 : Nat.Prime 4857451832958340271135717 := by
  apply lucas_primality 4857451832958340271135717 (2 : ZMod 4857451832958340271135717)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (646549, 1), (1878222622321873621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (646549, 1), (1878222622321873621, 1)] : List FactorBlock).map factorBlockValue).prod) = 4857451832958340271135717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_646549
      · exact prime_seventyNineBY_1878222622321873621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4857451832958340271135717) ^ 2428725916479170135567858 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4857451832958340271135717) ^ 7512890489287494484 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4857451832958340271135717) ^ 2586196 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_6764128320113192839904227 : Nat.Prime 6764128320113192839904227 := by
  apply lucas_primality 6764128320113192839904227 (2 : ZMod 6764128320113192839904227)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (223, 1), (240733444377293502737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (223, 1), (240733444377293502737, 1)] : List FactorBlock).map factorBlockValue).prod) = 6764128320113192839904227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_223
      · exact prime_seventyNineBY_240733444377293502737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6764128320113192839904227) ^ 3382064160056596419952113 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 6764128320113192839904227) ^ 2254709440037730946634742 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 6764128320113192839904227) ^ 966304045730456119986318 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 6764128320113192839904227) ^ 30332413991538981344862 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 6764128320113192839904227) ^ 28098 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_7877790472682436465367541 : Nat.Prime 7877790472682436465367541 := by
  apply lucas_primality 7877790472682436465367541 (10 : ZMod 7877790472682436465367541)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (23, 1), (131, 1), (11399, 1), (603607939583809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (23, 1), (131, 1), (11399, 1), (603607939583809, 1)] : List FactorBlock).map factorBlockValue).prod) = 7877790472682436465367541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_19
      · exact prime_seventyNineBY_23
      · exact prime_seventyNineBY_131
      · exact prime_seventyNineBY_11399
      · exact prime_seventyNineBY_603607939583809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 7877790472682436465367541) ^ 3938895236341218232683770 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (10 : ZMod 7877790472682436465367541) ^ 1575558094536487293073508 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (10 : ZMod 7877790472682436465367541) ^ 414620551193812445545660 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (10 : ZMod 7877790472682436465367541) ^ 342512629247062455015980 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (10 : ZMod 7877790472682436465367541) ^ 60135805134980431033340 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (10 : ZMod 7877790472682436465367541) ^ 691094874347086276460 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (10 : ZMod 7877790472682436465367541) ^ 13051171060 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_8761640135471197629774631 : Nat.Prime 8761640135471197629774631 := by
  apply lucas_primality 8761640135471197629774631 (6 : ZMod 8761640135471197629774631)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 2), (43, 1), (130183, 1), (1064744353947041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 2), (43, 1), (130183, 1), (1064744353947041, 1)] : List FactorBlock).map factorBlockValue).prod) = 8761640135471197629774631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_3
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_7
      · exact prime_seventyNineBY_43
      · exact prime_seventyNineBY_130183
      · exact prime_seventyNineBY_1064744353947041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 8761640135471197629774631) ^ 4380820067735598814887315 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 8761640135471197629774631) ^ 2920546711823732543258210 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 8761640135471197629774631) ^ 1752328027094239525954926 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 8761640135471197629774631) ^ 1251662876495885375682090 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 8761640135471197629774631) ^ 203759072917934828599410 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 8761640135471197629774631) ^ 67302490612992461610 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (6 : ZMod 8761640135471197629774631) ^ 8228867430 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_14327210284418310589568579 : Nat.Prime 14327210284418310589568579 := by
  apply lucas_primality 14327210284418310589568579 (2 : ZMod 14327210284418310589568579)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (442061, 1), (24879053, 1), (651351762233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (442061, 1), (24879053, 1), (651351762233, 1)] : List FactorBlock).map factorBlockValue).prod) = 14327210284418310589568579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_442061
      · exact prime_seventyNineBY_24879053
      · exact prime_seventyNineBY_651351762233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14327210284418310589568579) ^ 7163605142209155294784289 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 14327210284418310589568579) ^ 32410030028476410698 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 14327210284418310589568579) ^ 575874422728964426 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (2 : ZMod 14327210284418310589568579) ^ 21996118096466 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_79218900631147554481253237 : Nat.Prime 79218900631147554481253237 := by
  apply lucas_primality 79218900631147554481253237 (5 : ZMod 79218900631147554481253237)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (103, 1), (778303343, 1), (22458979260511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (103, 1), (778303343, 1), (22458979260511, 1)] : List FactorBlock).map factorBlockValue).prod) = 79218900631147554481253237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_11
      · exact prime_seventyNineBY_103
      · exact prime_seventyNineBY_778303343
      · exact prime_seventyNineBY_22458979260511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 79218900631147554481253237) ^ 39609450315573777240626618 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 79218900631147554481253237) ^ 7201718239195232225568476 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 79218900631147554481253237) ^ 769115540108228684284012 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 79218900631147554481253237) ^ 101784094008635852 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (5 : ZMod 79218900631147554481253237) ^ 3527270750476 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_299356037961932585683966559 : Nat.Prime 299356037961932585683966559 := by
  apply lucas_primality 299356037961932585683966559 (11 : ZMod 299356037961932585683966559)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (7877790472682436465367541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (7877790472682436465367541, 1)] : List FactorBlock).map factorBlockValue).prod) = 299356037961932585683966559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_19
      · exact prime_seventyNineBY_7877790472682436465367541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 299356037961932585683966559) ^ 149678018980966292841983279 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (11 : ZMod 299356037961932585683966559) ^ 15755580945364872930735082 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (11 : ZMod 299356037961932585683966559) ^ 38 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_93399083844122966733397566431 : Nat.Prime 93399083844122966733397566431 := by
  apply lucas_primality 93399083844122966733397566431 (23 : ZMod 93399083844122966733397566431)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (1762145767, 1), (230448003133509923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (1762145767, 1), (230448003133509923, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_5
      · exact prime_seventyNineBY_23
      · exact prime_seventyNineBY_1762145767
      · exact prime_seventyNineBY_230448003133509923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 93399083844122966733397566431) ^ 46699541922061483366698783215 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (23 : ZMod 93399083844122966733397566431) ^ 18679816768824593346679513286 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (23 : ZMod 93399083844122966733397566431) ^ 4060829732353172466669459410 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (23 : ZMod 93399083844122966733397566431) ^ 53003040720707282290 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (23 : ZMod 93399083844122966733397566431) ^ 405293526410 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem prime_seventyNineBY_93399083844122966733397566449 : Nat.Prime 93399083844122966733397566449 := by
  apply lucas_primality 93399083844122966733397566449 (3 : ZMod 93399083844122966733397566449)
  · rw [← seventyNineBYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (53, 1), (75269, 1), (95419, 1), (52954849, 1), (289594309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (53, 1), (75269, 1), (95419, 1), (52954849, 1), (289594309, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyNineBY_2
      · exact prime_seventyNineBY_53
      · exact prime_seventyNineBY_75269
      · exact prime_seventyNineBY_95419
      · exact prime_seventyNineBY_52954849
      · exact prime_seventyNineBY_289594309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 93399083844122966733397566449) ^ 46699541922061483366698783224 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 93399083844122966733397566449) ^ 1762246864983452202516935216 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 93399083844122966733397566449) ^ 1240870528957777660569392 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 93399083844122966733397566449) ^ 978831090706494165034192 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 93399083844122966733397566449) ^ 1763749413091952480752 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide
    · change (3 : ZMod 93399083844122966733397566449) ^ 322516986492724781872 ≠ 1
      rw [← seventyNineBYFastPow_eq_pow]
      decide

private theorem phi_seventyNineBY_93399083844122966733397566400 : Nat.totient 93399083844122966733397566400 = 35358786747036819403580620800 := by
  rw [← show ((([(2, 6), (5, 2), (19, 1), (1361, 1), (4139, 1), (545400436298251879, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566400 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_5, prime_seventyNineBY_19, prime_seventyNineBY_1361, prime_seventyNineBY_4139, prime_seventyNineBY_545400436298251879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566401 : Nat.totient 93399083844122966733397566401 = 93379869879082384217240316240 := by
  rw [← show ((([(4861, 1), (3166905163979, 1), (6067110949279, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566401 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_4861, prime_seventyNineBY_3166905163979, prime_seventyNineBY_6067110949279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566402 : Nat.totient 93399083844122966733397566402 = 31126895777323935208251474624 := by
  rw [← show ((([(2, 1), (3, 1), (5077, 1), (56855790253, 1), (53927402483707, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566402 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_3, prime_seventyNineBY_5077, prime_seventyNineBY_56855790253, prime_seventyNineBY_53927402483707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566403 : Nat.totient 93399083844122966733397566403 = 93133580189003652601601353440 := by
  rw [← show ((([(463, 1), (1531, 1), (32069, 1), (4108667690368227179, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566403 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_463, prime_seventyNineBY_1531, prime_seventyNineBY_32069, prime_seventyNineBY_4108667690368227179]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566404 : Nat.totient 93399083844122966733397566404 = 46699541921971516816132637664 := by
  rw [← show ((([(2, 2), (519082709317, 1), (44982756200363453, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566404 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_519082709317, prime_seventyNineBY_44982756200363453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566405 : Nat.totient 93399083844122966733397566405 = 42696707035674795080580513792 := by
  rw [← show ((([(3, 2), (5, 1), (7, 1), (2515673, 1), (1233327703, 1), (95565115073, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566405 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_3, prime_seventyNineBY_5, prime_seventyNineBY_7, prime_seventyNineBY_2515673, prime_seventyNineBY_1233327703, prime_seventyNineBY_95565115073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566406 : Nat.totient 93399083844122966733397566406 = 46699506773867928523700506008 := by
  rw [← show ((([(2, 1), (1328647, 1), (35148193554842996948549, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566406 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_1328647, prime_seventyNineBY_35148193554842996948549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566407 : Nat.totient 93399083844122966733397566407 = 89070834459249583291206535680 := by
  rw [← show ((([(23, 1), (337, 1), (43291, 1), (338119, 1), (823223359986133, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566407 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_23, prime_seventyNineBY_337, prime_seventyNineBY_43291, prime_seventyNineBY_338119, prime_seventyNineBY_823223359986133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566408 : Nat.totient 93399083844122966733397566408 = 28738179644345528225660789568 := by
  rw [← show ((([(2, 3), (3, 1), (13, 1), (299356037961932585683966559, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566408 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_3, prime_seventyNineBY_13, prime_seventyNineBY_299356037961932585683966559]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566409 : Nat.totient 93399083844122966733397566409 = 93321383962256721883330992000 := by
  rw [← show ((([(2393, 1), (2711, 1), (22051, 1), (652893148010813533, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566409 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2393, prime_seventyNineBY_2711, prime_seventyNineBY_22051, prime_seventyNineBY_652893148010813533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566410 : Nat.totient 93399083844122966733397566410 = 31631729152726437608306442240 := by
  rw [← show ((([(2, 1), (5, 1), (11, 1), (17, 1), (97, 1), (7547, 1), (68226787924528252777, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566410 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_5, prime_seventyNineBY_11, prime_seventyNineBY_17, prime_seventyNineBY_97, prime_seventyNineBY_7547, prime_seventyNineBY_68226787924528252777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566411 : Nat.totient 93399083844122966733397566411 = 62264188791264540450137671008 := by
  rw [← show ((([(3, 1), (33349, 1), (92471716307, 1), (10095541709959, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566411 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_3, prime_seventyNineBY_33349, prime_seventyNineBY_92471716307, prime_seventyNineBY_10095541709959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566412 : Nat.totient 93399083844122966733397566412 = 40028178790330710580902142080 := by
  rw [← show ((([(2, 2), (7, 1), (5238694497481, 1), (636739089760909, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566412 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_7, prime_seventyNineBY_5238694497481, prime_seventyNineBY_636739089760909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566413 : Nat.totient 93399083844122966733397566413 = 90339402170151937044009331200 := by
  rw [← show ((([(31, 1), (1931, 1), (4267390129, 1), (365625350975977, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566413 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_31, prime_seventyNineBY_1931, prime_seventyNineBY_4267390129, prime_seventyNineBY_365625350975977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566414 : Nat.totient 93399083844122966733397566414 = 30926786423518928957902524000 := by
  rw [← show ((([(2, 1), (3, 3), (151, 1), (541507, 1), (5707183, 1), (3706346648111, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566414 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_3, prime_seventyNineBY_151, prime_seventyNineBY_541507, prime_seventyNineBY_5707183, prime_seventyNineBY_3706346648111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566415 : Nat.totient 93399083844122966733397566415 = 73645168350879860060451456000 := by
  rw [← show ((([(5, 1), (109, 1), (191, 1), (74441, 1), (411018967, 1), (29325044831, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566415 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_5, prime_seventyNineBY_109, prime_seventyNineBY_191, prime_seventyNineBY_74441, prime_seventyNineBY_411018967, prime_seventyNineBY_29325044831]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566416 : Nat.totient 93399083844122966733397566416 = 46645428895500577823979542496 := by
  rw [← show ((([(2, 4), (863, 1), (6764128320113192839904227, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566416 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_863, prime_seventyNineBY_6764128320113192839904227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566417 : Nat.totient 93399083844122966733397566417 = 62264901944824614231801394320 := by
  rw [← show ((([(3, 1), (53959, 1), (576975628681795231771021, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566417 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_3, prime_seventyNineBY_53959, prime_seventyNineBY_576975628681795231771021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566418 : Nat.totient 93399083844122966733397566418 = 46699295587772704477989212880 := by
  rw [← show ((([(2, 1), (190543, 1), (37429571, 1), (6547941224199853, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566418 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_190543, prime_seventyNineBY_37429571, prime_seventyNineBY_6547941224199853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566419 : Nat.totient 93399083844122966733397566419 = 73991837823867238884335308800 := by
  rw [← show ((([(7, 1), (19, 1), (41, 1), (62639, 1), (3697081, 1), (73961095804697, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566419 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_7, prime_seventyNineBY_19, prime_seventyNineBY_41, prime_seventyNineBY_62639, prime_seventyNineBY_3697081, prime_seventyNineBY_73961095804697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566420 : Nat.totient 93399083844122966733397566420 = 24238520270311382936747212800 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (47, 1), (211, 1), (1091, 1), (114113, 1), (1260814454270237, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566420 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_3, prime_seventyNineBY_5, prime_seventyNineBY_47, prime_seventyNineBY_211, prime_seventyNineBY_1091, prime_seventyNineBY_114113, prime_seventyNineBY_1260814454270237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566421 : Nat.totient 93399083844122966733397566421 = 75946152673119220900020264960 := by
  rw [← show ((([(11, 2), (13, 1), (43, 1), (149, 1), (809, 1), (371897, 1), (30802642328807, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566421 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_11, prime_seventyNineBY_13, prime_seventyNineBY_43, prime_seventyNineBY_149, prime_seventyNineBY_809, prime_seventyNineBY_371897, prime_seventyNineBY_30802642328807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566422 : Nat.totient 93399083844122966733397566422 = 43870584355930204456205647872 := by
  rw [← show ((([(2, 1), (29, 1), (37, 1), (41703989, 1), (513895169, 1), (2030770127, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566422 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_29, prime_seventyNineBY_37, prime_seventyNineBY_41703989, prime_seventyNineBY_513895169, prime_seventyNineBY_2030770127]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566423 : Nat.totient 93399083844122966733397566423 = 61790742492295092495377524080 := by
  rw [← show ((([(3, 2), (131, 1), (79218900631147554481253237, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566423 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_3, prime_seventyNineBY_131, prime_seventyNineBY_79218900631147554481253237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566424 : Nat.totient 93399083844122966733397566424 = 46386347187139454185315762176 := by
  rw [← show ((([(2, 3), (389, 1), (433, 1), (599, 1), (9029, 1), (18787, 1), (124679, 1), (5471393, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566424 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_389, prime_seventyNineBY_433, prime_seventyNineBY_599, prime_seventyNineBY_9029, prime_seventyNineBY_18787, prime_seventyNineBY_124679, prime_seventyNineBY_5471393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566425 : Nat.totient 93399083844122966733397566425 = 74719262549420688532522186320 := by
  rw [← show ((([(5, 2), (16509343, 1), (226293884242693283999, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566425 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_5, prime_seventyNineBY_16509343, prime_seventyNineBY_226293884242693283999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566426 : Nat.totient 93399083844122966733397566426 = 26641489663430910120802743360 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (607, 1), (2890770011, 1), (1267334022826789, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566426 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_3, prime_seventyNineBY_7, prime_seventyNineBY_607, prime_seventyNineBY_2890770011, prime_seventyNineBY_1267334022826789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566427 : Nat.totient 93399083844122966733397566427 = 87899884006932143010408595072 := by
  rw [← show ((([(17, 1), (17123, 1), (37528223, 1), (8549797674932039, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566427 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_17, prime_seventyNineBY_17123, prime_seventyNineBY_37528223, prime_seventyNineBY_8549797674932039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566428 : Nat.totient 93399083844122966733397566428 = 46699541900379139128178899552 := by
  rw [← show ((([(2, 2), (2153805023, 1), (10841172117106136809, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566428 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_2153805023, prime_seventyNineBY_10841172117106136809]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566429 : Nat.totient 93399083844122966733397566429 = 62024481547173635400893619648 := by
  rw [← show ((([(3, 1), (397, 1), (733, 1), (106985982687485571909143, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566429 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_3, prime_seventyNineBY_397, prime_seventyNineBY_733, prime_seventyNineBY_106985982687485571909143]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566430 : Nat.totient 93399083844122966733397566430 = 35735301624428493275873542176 := by
  rw [← show ((([(2, 1), (5, 1), (23, 1), (1762145767, 1), (230448003133509923, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566430 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_5, prime_seventyNineBY_23, prime_seventyNineBY_1762145767, prime_seventyNineBY_230448003133509923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566431 : Nat.totient 93399083844122966733397566431 = 93399083844122966733397566430 := by
  rw [← show ((([(93399083844122966733397566431, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566431 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_93399083844122966733397566431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566432 : Nat.totient 93399083844122966733397566432 = 28302281666163175255012915200 := by
  rw [← show ((([(2, 5), (3, 2), (11, 1), (60089, 1), (490639452174366055741, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566432 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_3, prime_seventyNineBY_11, prime_seventyNineBY_60089, prime_seventyNineBY_490639452174366055741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566433 : Nat.totient 93399083844122966733397566433 = 80055570563467083666778173120 := by
  rw [← show ((([(7, 2), (101723, 1), (5852300539, 1), (3201848328761, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566433 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_7, prime_seventyNineBY_101723, prime_seventyNineBY_5852300539, prime_seventyNineBY_3201848328761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566434 : Nat.totient 93399083844122966733397566434 = 41875087121612538550734422016 := by
  rw [← show ((([(2, 1), (13, 1), (79, 1), (89, 1), (223, 1), (2287, 1), (33863, 1), (1479617, 1), (19994309, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566434 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_13, prime_seventyNineBY_79, prime_seventyNineBY_89, prime_seventyNineBY_223, prime_seventyNineBY_2287, prime_seventyNineBY_33863, prime_seventyNineBY_1479617, prime_seventyNineBY_19994309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566435 : Nat.totient 93399083844122966733397566435 = 48266177954555570581440000000 := by
  rw [← show ((([(3, 1), (5, 1), (61, 1), (101, 1), (199, 1), (41011, 1), (123835942213311001, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566435 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_3, prime_seventyNineBY_5, prime_seventyNineBY_61, prime_seventyNineBY_101, prime_seventyNineBY_199, prime_seventyNineBY_41011, prime_seventyNineBY_123835942213311001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566436 : Nat.totient 93399083844122966733397566436 = 46644794502335271430242727680 := by
  rw [← show ((([(2, 2), (853, 1), (5600482861, 1), (4887740285640073, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566436 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_853, prime_seventyNineBY_5600482861, prime_seventyNineBY_4887740285640073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566437 : Nat.totient 93399083844122966733397566437 = 92080157934208583413394451520 := by
  rw [← show ((([(71, 1), (26723, 1), (49226511025804625088689, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566437 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_71, prime_seventyNineBY_26723, prime_seventyNineBY_49226511025804625088689]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566438 : Nat.totient 93399083844122966733397566438 = 29326012511027569980663398400 := by
  rw [← show ((([(2, 1), (3, 1), (19, 1), (181, 1), (8537, 1), (22921, 1), (38239, 1), (604942115969, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566438 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_3, prime_seventyNineBY_19, prime_seventyNineBY_181, prime_seventyNineBY_8537, prime_seventyNineBY_22921, prime_seventyNineBY_38239, prime_seventyNineBY_604942115969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566439 : Nat.totient 93399083844122966733397566439 = 93384132813882287471147043960 := by
  rw [← show ((([(6247, 1), (283417790611, 1), (52752616119067, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566439 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_6247, prime_seventyNineBY_283417790611, prime_seventyNineBY_52752616119067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566440 : Nat.totient 93399083844122966733397566440 = 31539671703605664634907418624 := by
  rw [← show ((([(2, 3), (5, 1), (7, 1), (83, 1), (353, 1), (4243, 1), (2683235278933155239, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566440 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_5, prime_seventyNineBY_7, prime_seventyNineBY_83, prime_seventyNineBY_353, prime_seventyNineBY_4243, prime_seventyNineBY_2683235278933155239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566441 : Nat.totient 93399083844122966733397566441 = 62258909556601192561410731040 := by
  rw [← show ((([(3, 3), (8713, 1), (397018860043625603008691, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566441 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_3, prime_seventyNineBY_8713, prime_seventyNineBY_397018860043625603008691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566442 : Nat.totient 93399083844122966733397566442 = 46699541922060266642557991532 := by
  rw [← show ((([(2, 1), (39675103098143, 1), (1177049037693547, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566442 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_39675103098143, prime_seventyNineBY_1177049037693547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566443 : Nat.totient 93399083844122966733397566443 = 84239689059555241239238226400 := by
  rw [← show ((([(11, 1), (127, 1), (4295580931, 1), (15564110458748149, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566443 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_11, prime_seventyNineBY_127, prime_seventyNineBY_4295580931, prime_seventyNineBY_15564110458748149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566444 : Nat.totient 93399083844122966733397566444 = 28356447911141551842040919040 := by
  rw [← show ((([(2, 2), (3, 1), (17, 1), (31, 1), (2784973, 1), (5303099380192293347, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566444 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_3, prime_seventyNineBY_17, prime_seventyNineBY_31, prime_seventyNineBY_2784973, prime_seventyNineBY_5303099380192293347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566445 : Nat.totient 93399083844122966733397566445 = 74692761481409958708920074944 := by
  rw [← show ((([(5, 1), (2819, 1), (100604082277, 1), (65866097440903, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566445 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_5, prime_seventyNineBY_2819, prime_seventyNineBY_100604082277, prime_seventyNineBY_65866097440903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566446 : Nat.totient 93399083844122966733397566446 = 46699541922048351377346554040 := by
  rw [← show ((([(2, 1), (3557130138013, 1), (13128432222091171, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566446 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_3557130138013, prime_seventyNineBY_13128432222091171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566447 : Nat.totient 93399083844122966733397566447 = 49265414916008527776085179264 := by
  rw [← show ((([(3, 1), (7, 1), (13, 1), (1372187, 1), (249325482782017807597, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566447 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_3, prime_seventyNineBY_7, prime_seventyNineBY_13, prime_seventyNineBY_1372187, prime_seventyNineBY_249325482782017807597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566448 : Nat.totient 93399083844122966733397566448 = 45817328562293663301460525056 := by
  rw [← show ((([(2, 4), (53, 1), (75269, 1), (95419, 1), (52954849, 1), (289594309, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566448 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_53, prime_seventyNineBY_75269, prime_seventyNineBY_95419, prime_seventyNineBY_52954849, prime_seventyNineBY_289594309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566449 : Nat.totient 93399083844122966733397566449 = 93399083844122966733397566448 := by
  rw [← show ((([(93399083844122966733397566449, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566449 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_93399083844122966733397566449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566450 : Nat.totient 93399083844122966733397566450 = 24906421905732813836297478240 := by
  rw [← show ((([(2, 1), (3, 2), (5, 2), (55017503, 1), (3772499810716720327, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566450 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_3, prime_seventyNineBY_5, prime_seventyNineBY_55017503, prime_seventyNineBY_3772499810716720327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566451 : Nat.totient 93399083844122966733397566451 = 90113751079387095988716923904 := by
  rw [← show ((([(29, 1), (1433, 1), (51647, 1), (1939676933, 1), (22434889093, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566451 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_29, prime_seventyNineBY_1433, prime_seventyNineBY_51647, prime_seventyNineBY_1939676933, prime_seventyNineBY_22434889093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566452 : Nat.totient 93399083844122966733397566452 = 46483053538870392447492034560 := by
  rw [← show ((([(2, 2), (317, 1), (673, 1), (8286733333, 1), (13207631245021, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566452 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_317, prime_seventyNineBY_673, prime_seventyNineBY_8286733333, prime_seventyNineBY_13207631245021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566453 : Nat.totient 93399083844122966733397566453 = 58574912478271507369071820800 := by
  rw [← show ((([(3, 1), (23, 2), (107, 1), (139, 1), (26561, 1), (94903, 1), (1569794302441, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566453 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_3, prime_seventyNineBY_23, prime_seventyNineBY_107, prime_seventyNineBY_139, prime_seventyNineBY_26561, prime_seventyNineBY_94903, prime_seventyNineBY_1569794302441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566454 : Nat.totient 93399083844122966733397566454 = 36235405756719148224514314240 := by
  rw [← show ((([(2, 1), (7, 1), (11, 1), (277, 1), (1613, 1), (11427322337, 1), (118785459223, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566454 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_7, prime_seventyNineBY_11, prime_seventyNineBY_277, prime_seventyNineBY_1613, prime_seventyNineBY_11427322337, prime_seventyNineBY_118785459223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566455 : Nat.totient 93399083844122966733397566455 = 73695476580664731462472937472 := by
  rw [← show ((([(5, 1), (73, 1), (375149, 1), (1736177, 1), (392872798156879, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566455 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_5, prime_seventyNineBY_73, prime_seventyNineBY_375149, prime_seventyNineBY_1736177, prime_seventyNineBY_392872798156879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566456 : Nat.totient 93399083844122966733397566456 = 31133027947974077372225269760 := by
  rw [← show ((([(2, 3), (3, 1), (465312270209, 1), (8363477051136341, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566456 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_3, prime_seventyNineBY_465312270209, prime_seventyNineBY_8363477051136341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566457 : Nat.totient 93399083844122966733397566457 = 86946143070284042524765816320 := by
  rw [← show ((([(19, 1), (59, 1), (3331, 1), (7649, 1), (3270074974395325843, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566457 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_19, prime_seventyNineBY_59, prime_seventyNineBY_3331, prime_seventyNineBY_7649, prime_seventyNineBY_3270074974395325843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566458 : Nat.totient 93399083844122966733397566458 = 46697839221591990143893732656 := by
  rw [← show ((([(2, 1), (27427, 1), (3021762923, 1), (563474057680349, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566458 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_27427, prime_seventyNineBY_3021762923, prime_seventyNineBY_563474057680349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566459 : Nat.totient 93399083844122966733397566459 = 60510109677906027937471748928 := by
  rw [← show ((([(3, 2), (37, 1), (829, 1), (338332604658179168553587, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566459 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_3, prime_seventyNineBY_37, prime_seventyNineBY_829, prime_seventyNineBY_338332604658179168553587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566460 : Nat.totient 93399083844122966733397566460 = 33644698120209398898334579200 := by
  rw [← show ((([(2, 2), (5, 1), (13, 1), (41, 1), (8761640135471197629774631, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566460 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_5, prime_seventyNineBY_13, prime_seventyNineBY_41, prime_seventyNineBY_8761640135471197629774631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566461 : Nat.totient 93399083844122966733397566461 = 74222574717805278164165880576 := by
  rw [← show ((([(7, 1), (17, 1), (67, 1), (84403243, 1), (138791132155861099, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566461 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_7, prime_seventyNineBY_17, prime_seventyNineBY_67, prime_seventyNineBY_84403243, prime_seventyNineBY_138791132155861099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566462 : Nat.totient 93399083844122966733397566462 = 31133027948039428030212677592 := by
  rw [← show ((([(2, 1), (3, 1), (20483412891343, 1), (759957047030939, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566462 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_3, prime_seventyNineBY_20483412891343, prime_seventyNineBY_759957047030939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566463 : Nat.totient 93399083844122966733397566463 = 93399083843962304845030965328 := by
  rw [← show ((([(581341491449, 1), (160661307025109687, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566463 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_581341491449, prime_seventyNineBY_160661307025109687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566464 : Nat.totient 93399083844122966733397566464 = 45613506063408890730263906304 := by
  rw [← show ((([(2, 10), (43, 1), (2121163786430844993036827, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566464 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_43, prime_seventyNineBY_2121163786430844993036827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566465 : Nat.totient 93399083844122966733397566465 = 45224583410532460894566888960 := by
  rw [← show ((([(3, 1), (5, 1), (11, 1), (757, 1), (747760969089491747595353, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566465 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_3, prime_seventyNineBY_5, prime_seventyNineBY_11, prime_seventyNineBY_757, prime_seventyNineBY_747760969089491747595353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566466 : Nat.totient 93399083844122966733397566466 = 46695171043301280687451838448 := by
  rw [← show ((([(2, 1), (10789, 1), (1100303, 1), (3933862087086176899, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566466 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_10789, prime_seventyNineBY_1100303, prime_seventyNineBY_3933862087086176899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566467 : Nat.totient 93399083844122966733397566467 = 91411869289560880323458008000 := by
  rw [← show ((([(47, 1), (19502743301, 1), (101894103778367561, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566467 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_47, prime_seventyNineBY_19502743301, prime_seventyNineBY_101894103778367561]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566468 : Nat.totient 93399083844122966733397566468 = 26536371756061010139188005824 := by
  rw [← show ((([(2, 2), (3, 4), (7, 1), (179, 1), (871260007, 1), (264057651101467, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566468 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_3, prime_seventyNineBY_7, prime_seventyNineBY_179, prime_seventyNineBY_871260007, prime_seventyNineBY_264057651101467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566469 : Nat.totient 93399083844122966733397566469 = 93338553003909625129816383600 := by
  rw [← show ((([(1543, 1), (55287973151, 1), (1094828315729933, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566469 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_1543, prime_seventyNineBY_55287973151, prime_seventyNineBY_1094828315729933]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566470 : Nat.totient 93399083844122966733397566470 = 37359622761989167394690977344 := by
  rw [← show ((([(2, 1), (5, 1), (3467039, 1), (2693915004824663545273, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566470 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_5, prime_seventyNineBY_3467039, prime_seventyNineBY_2693915004824663545273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566471 : Nat.totient 93399083844122966733397566471 = 61955979881372002813380715904 := by
  rw [← show ((([(3, 1), (227, 1), (1733, 1), (12760679, 1), (6201877127138213, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566471 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_3, prime_seventyNineBY_227, prime_seventyNineBY_1733, prime_seventyNineBY_12760679, prime_seventyNineBY_6201877127138213]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566472 : Nat.totient 93399083844122966733397566472 = 46247963997958388555607244800 := by
  rw [← show ((([(2, 3), (113, 1), (1721, 1), (4229, 1), (97561, 1), (145505492449357, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566472 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_113, prime_seventyNineBY_1721, prime_seventyNineBY_4229, prime_seventyNineBY_97561, prime_seventyNineBY_145505492449357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566473 : Nat.totient 93399083844122966733397566473 = 86192805981912342146222345856 := by
  rw [← show ((([(13, 1), (3967, 1), (4373808169, 1), (414073399688027, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566473 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_13, prime_seventyNineBY_3967, prime_seventyNineBY_4373808169, prime_seventyNineBY_414073399688027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566474 : Nat.totient 93399083844122966733397566474 = 31126938898354439995651060992 := by
  rw [← show ((([(2, 1), (3, 1), (5227, 1), (234293, 1), (12710995133056068689, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566474 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_3, prime_seventyNineBY_5227, prime_seventyNineBY_234293, prime_seventyNineBY_12710995133056068689]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566475 : Nat.totient 93399083844122966733397566475 = 61969988891118206702969424000 := by
  rw [← show ((([(5, 2), (7, 1), (31, 1), (6791, 1), (2535182003400352098797, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566475 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_5, prime_seventyNineBY_7, prime_seventyNineBY_31, prime_seventyNineBY_6791, prime_seventyNineBY_2535182003400352098797]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566476 : Nat.totient 93399083844122966733397566476 = 38471018517030054947394870720 := by
  rw [← show ((([(2, 2), (11, 1), (19, 1), (23, 1), (4857451832958340271135717, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566476 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_11, prime_seventyNineBY_19, prime_seventyNineBY_23, prime_seventyNineBY_4857451832958340271135717]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566477 : Nat.totient 93399083844122966733397566477 = 62255024789097911582151396000 := by
  rw [← show ((([(3, 2), (5651, 1), (8620231, 1), (11766427, 1), (18105532019, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566477 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_3, prime_seventyNineBY_5651, prime_seventyNineBY_8620231, prime_seventyNineBY_11766427, prime_seventyNineBY_18105532019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566478 : Nat.totient 93399083844122966733397566478 = 43668387331033166693793389952 := by
  rw [← show ((([(2, 1), (17, 1), (167, 1), (2087, 1), (7881788539169832498823, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566478 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_17, prime_seventyNineBY_167, prime_seventyNineBY_2087, prime_seventyNineBY_7881788539169832498823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566479 : Nat.totient 93399083844122966733397566479 = 93399083753654952376179666240 := by
  rw [← show ((([(1032398959, 1), (90468014356185501281, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566479 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_1032398959, prime_seventyNineBY_90468014356185501281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566480 : Nat.totient 93399083844122966733397566480 = 23765208461545475851537121280 := by
  rw [← show ((([(2, 4), (3, 1), (5, 1), (29, 1), (103, 1), (487, 1), (48779611, 1), (5484396664753, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566480 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_3, prime_seventyNineBY_5, prime_seventyNineBY_29, prime_seventyNineBY_103, prime_seventyNineBY_487, prime_seventyNineBY_48779611, prime_seventyNineBY_5484396664753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566481 : Nat.totient 93399083844122966733397566481 = 93289002874280498258673269760 := by
  rw [← show ((([(1487, 1), (1999, 1), (161873, 1), (33987221, 1), (5711218589, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566481 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_1487, prime_seventyNineBY_1999, prime_seventyNineBY_161873, prime_seventyNineBY_33987221, prime_seventyNineBY_5711218589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566482 : Nat.totient 93399083844122966733397566482 = 40013042512744515779734143744 := by
  rw [← show ((([(2, 1), (7, 2), (2647, 1), (2889877, 1), (135305627, 1), (920804393, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566482 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_7, prime_seventyNineBY_2647, prime_seventyNineBY_2889877, prime_seventyNineBY_135305627, prime_seventyNineBY_920804393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566483 : Nat.totient 93399083844122966733397566483 = 62159980843042324886792096960 := by
  rw [← show ((([(3, 1), (587, 1), (153253320491, 1), (346077501923033, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566483 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_3, prime_seventyNineBY_587, prime_seventyNineBY_153253320491, prime_seventyNineBY_346077501923033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566484 : Nat.totient 93399083844122966733397566484 = 46450059649968595193063568000 := by
  rw [← show ((([(2, 2), (197, 1), (4591, 1), (37003, 1), (44111, 1), (15817041965731, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566484 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_197, prime_seventyNineBY_4591, prime_seventyNineBY_37003, prime_seventyNineBY_44111, prime_seventyNineBY_15817041965731]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566485 : Nat.totient 93399083844122966733397566485 = 74590440407958753418661595648 := by
  rw [← show ((([(5, 1), (983, 1), (1429, 1), (128473, 1), (103508258019066227, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566485 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_5, prime_seventyNineBY_983, prime_seventyNineBY_1429, prime_seventyNineBY_128473, prime_seventyNineBY_103508258019066227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566486 : Nat.totient 93399083844122966733397566486 = 28738082564756016642141262272 := by
  rw [← show ((([(2, 1), (3, 2), (13, 1), (296027, 1), (1348327632105326364077, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566486 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_3, prime_seventyNineBY_13, prime_seventyNineBY_296027, prime_seventyNineBY_1348327632105326364077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566487 : Nat.totient 93399083844122966733397566487 = 84852763060292458296961536000 := by
  rw [← show ((([(11, 1), (1553, 1), (103393, 1), (144184451, 1), (366748976423, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566487 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_11, prime_seventyNineBY_1553, prime_seventyNineBY_103393, prime_seventyNineBY_144184451, prime_seventyNineBY_366748976423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566488 : Nat.totient 93399083844122966733397566488 = 46699275826636577219699515392 := by
  rw [← show ((([(2, 3), (192629, 1), (1973527, 1), (30710570677609217, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566488 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_192629, prime_seventyNineBY_1973527, prime_seventyNineBY_30710570677609217]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566489 : Nat.totient 93399083844122966733397566489 = 53370901389484177585631529600 := by
  rw [← show ((([(3, 1), (7, 1), (14565101, 1), (305358364569439834409, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566489 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_3, prime_seventyNineBY_7, prime_seventyNineBY_14565101, prime_seventyNineBY_305358364569439834409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566490 : Nat.totient 93399083844122966733397566490 = 37349774090073795836477090880 := by
  rw [← show ((([(2, 1), (5, 1), (4027, 1), (64271, 1), (36535739, 1), (987706776223, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566490 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_5, prime_seventyNineBY_4027, prime_seventyNineBY_64271, prime_seventyNineBY_36535739, prime_seventyNineBY_987706776223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566491 : Nat.totient 93399083844122966733397566491 = 93399073196225833710895776984 := by
  rw [← show ((([(8771599, 1), (10647897133022493017909, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566491 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_8771599, prime_seventyNineBY_10647897133022493017909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566492 : Nat.totient 93399083844122966733397566492 = 30934728406961824815662423040 := by
  rw [← show ((([(2, 2), (3, 1), (157, 1), (6313983472681, 1), (7851602000873, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566492 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_3, prime_seventyNineBY_157, prime_seventyNineBY_6313983472681, prime_seventyNineBY_7851602000873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566493 : Nat.totient 93399083844122966733397566493 = 93374843107012077972549376944 := by
  rw [← show ((([(3853, 1), (755438767, 1), (32088124896863743, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566493 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_3853, prime_seventyNineBY_755438767, prime_seventyNineBY_32088124896863743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566494 : Nat.totient 93399083844122966733397566494 = 46699524583828625993629955976 := by
  rw [← show ((([(2, 1), (2693443, 1), (17338232857373066133829, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566494 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_2693443, prime_seventyNineBY_17338232857373066133829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566495 : Nat.totient 93399083844122966733397566495 = 44295046105145918961296056320 := by
  rw [← show ((([(3, 3), (5, 1), (17, 1), (19, 1), (373, 1), (42331, 1), (135655986992320213, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566495 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_3, prime_seventyNineBY_5, prime_seventyNineBY_17, prime_seventyNineBY_19, prime_seventyNineBY_373, prime_seventyNineBY_42331, prime_seventyNineBY_135655986992320213]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566496 : Nat.totient 93399083844122966733397566496 = 38307692602678498147151216640 := by
  rw [← show ((([(2, 5), (7, 1), (37, 1), (61, 1), (234809, 1), (2417477, 1), (325451253779, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566496 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_7, prime_seventyNineBY_37, prime_seventyNineBY_61, prime_seventyNineBY_234809, prime_seventyNineBY_2417477, prime_seventyNineBY_325451253779]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566497 : Nat.totient 93399083844122966733397566497 = 93204057055452533196665292144 := by
  rw [← show ((([(479, 1), (2381317, 1), (81882273105130179379, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566497 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_479, prime_seventyNineBY_2381317, prime_seventyNineBY_81882273105130179379]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566498 : Nat.totient 93399083844122966733397566498 = 28184037950347540684632534080 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (239, 1), (96443, 1), (30236483, 1), (2030480365583, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566498 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_3, prime_seventyNineBY_11, prime_seventyNineBY_239, prime_seventyNineBY_96443, prime_seventyNineBY_30236483, prime_seventyNineBY_2030480365583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566499 : Nat.totient 93399083844122966733397566499 = 82466058610559188150175243808 := by
  rw [← show ((([(13, 1), (23, 1), (3730147, 1), (83742414943250482883, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566499 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_13, prime_seventyNineBY_23, prime_seventyNineBY_3730147, prime_seventyNineBY_83742414943250482883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566500 : Nat.totient 93399083844122966733397566500 = 37359440968004848824536496000 := by
  rw [← show ((([(2, 2), (5, 3), (194027, 1), (1783904461, 1), (539683141139, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566500 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_2, prime_seventyNineBY_5, prime_seventyNineBY_194027, prime_seventyNineBY_1783904461, prime_seventyNineBY_539683141139]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyNineBY_93399083844122966733397566501 : Nat.totient 93399083844122966733397566501 = 59601194783180172052605284480 := by
  rw [← show ((([(3, 1), (41, 1), (53, 1), (14327210284418310589568579, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122966733397566501 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyNineBY_3, prime_seventyNineBY_41, prime_seventyNineBY_53, prime_seventyNineBY_14327210284418310589568579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64SeventyNineBY : certifiedKill 1 93399083844122966733397566399 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_seventyNineBY_93399083844122966733397566400, phi_seventyNineBY_93399083844122966733397566401, phi_seventyNineBY_93399083844122966733397566402,
    phi_seventyNineBY_93399083844122966733397566403, phi_seventyNineBY_93399083844122966733397566404, phi_seventyNineBY_93399083844122966733397566405,
    phi_seventyNineBY_93399083844122966733397566406, phi_seventyNineBY_93399083844122966733397566407, phi_seventyNineBY_93399083844122966733397566408,
    phi_seventyNineBY_93399083844122966733397566409, phi_seventyNineBY_93399083844122966733397566410, phi_seventyNineBY_93399083844122966733397566411,
    phi_seventyNineBY_93399083844122966733397566412, phi_seventyNineBY_93399083844122966733397566413, phi_seventyNineBY_93399083844122966733397566414,
    phi_seventyNineBY_93399083844122966733397566415, phi_seventyNineBY_93399083844122966733397566416, phi_seventyNineBY_93399083844122966733397566417,
    phi_seventyNineBY_93399083844122966733397566418, phi_seventyNineBY_93399083844122966733397566419, phi_seventyNineBY_93399083844122966733397566420,
    phi_seventyNineBY_93399083844122966733397566421, phi_seventyNineBY_93399083844122966733397566422, phi_seventyNineBY_93399083844122966733397566423,
    phi_seventyNineBY_93399083844122966733397566424, phi_seventyNineBY_93399083844122966733397566425, phi_seventyNineBY_93399083844122966733397566426,
    phi_seventyNineBY_93399083844122966733397566427, phi_seventyNineBY_93399083844122966733397566428, phi_seventyNineBY_93399083844122966733397566429,
    phi_seventyNineBY_93399083844122966733397566430, phi_seventyNineBY_93399083844122966733397566431, phi_seventyNineBY_93399083844122966733397566432,
    phi_seventyNineBY_93399083844122966733397566433, phi_seventyNineBY_93399083844122966733397566434, phi_seventyNineBY_93399083844122966733397566435,
    phi_seventyNineBY_93399083844122966733397566436, phi_seventyNineBY_93399083844122966733397566437, phi_seventyNineBY_93399083844122966733397566438,
    phi_seventyNineBY_93399083844122966733397566439, phi_seventyNineBY_93399083844122966733397566440, phi_seventyNineBY_93399083844122966733397566441,
    phi_seventyNineBY_93399083844122966733397566442, phi_seventyNineBY_93399083844122966733397566443, phi_seventyNineBY_93399083844122966733397566444,
    phi_seventyNineBY_93399083844122966733397566445, phi_seventyNineBY_93399083844122966733397566446, phi_seventyNineBY_93399083844122966733397566447,
    phi_seventyNineBY_93399083844122966733397566448, phi_seventyNineBY_93399083844122966733397566449, phi_seventyNineBY_93399083844122966733397566450,
    phi_seventyNineBY_93399083844122966733397566451, phi_seventyNineBY_93399083844122966733397566452, phi_seventyNineBY_93399083844122966733397566453,
    phi_seventyNineBY_93399083844122966733397566454, phi_seventyNineBY_93399083844122966733397566455, phi_seventyNineBY_93399083844122966733397566456,
    phi_seventyNineBY_93399083844122966733397566457, phi_seventyNineBY_93399083844122966733397566458, phi_seventyNineBY_93399083844122966733397566459,
    phi_seventyNineBY_93399083844122966733397566460, phi_seventyNineBY_93399083844122966733397566461, phi_seventyNineBY_93399083844122966733397566462,
    phi_seventyNineBY_93399083844122966733397566463, phi_seventyNineBY_93399083844122966733397566464, phi_seventyNineBY_93399083844122966733397566465,
    phi_seventyNineBY_93399083844122966733397566466, phi_seventyNineBY_93399083844122966733397566467, phi_seventyNineBY_93399083844122966733397566468,
    phi_seventyNineBY_93399083844122966733397566469, phi_seventyNineBY_93399083844122966733397566470, phi_seventyNineBY_93399083844122966733397566471,
    phi_seventyNineBY_93399083844122966733397566472, phi_seventyNineBY_93399083844122966733397566473, phi_seventyNineBY_93399083844122966733397566474,
    phi_seventyNineBY_93399083844122966733397566475, phi_seventyNineBY_93399083844122966733397566476, phi_seventyNineBY_93399083844122966733397566477,
    phi_seventyNineBY_93399083844122966733397566478, phi_seventyNineBY_93399083844122966733397566479, phi_seventyNineBY_93399083844122966733397566480,
    phi_seventyNineBY_93399083844122966733397566481, phi_seventyNineBY_93399083844122966733397566482, phi_seventyNineBY_93399083844122966733397566483,
    phi_seventyNineBY_93399083844122966733397566484, phi_seventyNineBY_93399083844122966733397566485, phi_seventyNineBY_93399083844122966733397566486,
    phi_seventyNineBY_93399083844122966733397566487, phi_seventyNineBY_93399083844122966733397566488, phi_seventyNineBY_93399083844122966733397566489,
    phi_seventyNineBY_93399083844122966733397566490, phi_seventyNineBY_93399083844122966733397566491, phi_seventyNineBY_93399083844122966733397566492,
    phi_seventyNineBY_93399083844122966733397566493, phi_seventyNineBY_93399083844122966733397566494, phi_seventyNineBY_93399083844122966733397566495,
    phi_seventyNineBY_93399083844122966733397566496, phi_seventyNineBY_93399083844122966733397566497, phi_seventyNineBY_93399083844122966733397566498,
    phi_seventyNineBY_93399083844122966733397566499, phi_seventyNineBY_93399083844122966733397566500, phi_seventyNineBY_93399083844122966733397566501]

end TotientTailPeriodKiller
end Erdos249257
