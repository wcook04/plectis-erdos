import Erdos249257.DiagonalPincerCertificatesT64
/- Kernel-checked off-diagonal certificate at a freely chosen position. -/
namespace Erdos249257
namespace TotientTailPeriodKiller
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
private def oneHundredSixtyFourFFFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredSixtyFourFFFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredSixtyFourFFFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredSixtyFourFFFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredSixtyFourFFFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredSixtyFourFFFastPow a n * oneHundredSixtyFourFFFastPow a n * a else oneHundredSixtyFourFFFastPow a n * oneHundredSixtyFourFFFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredSixtyFourFF_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredSixtyFourFF_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredSixtyFourFF_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredSixtyFourFF_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredSixtyFourFF_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredSixtyFourFF_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredSixtyFourFF_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredSixtyFourFF_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredSixtyFourFF_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredSixtyFourFF_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredSixtyFourFF_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredSixtyFourFF_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredSixtyFourFF_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredSixtyFourFF_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredSixtyFourFF_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredSixtyFourFF_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredSixtyFourFF_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredSixtyFourFF_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredSixtyFourFF_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredSixtyFourFF_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredSixtyFourFF_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredSixtyFourFF_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredSixtyFourFF_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredSixtyFourFF_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredSixtyFourFF_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredSixtyFourFF_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredSixtyFourFF_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredSixtyFourFF_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredSixtyFourFF_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredSixtyFourFF_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredSixtyFourFF_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredSixtyFourFF_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredSixtyFourFF_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredSixtyFourFF_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredSixtyFourFF_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredSixtyFourFF_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredSixtyFourFF_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredSixtyFourFF_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredSixtyFourFF_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredSixtyFourFF_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredSixtyFourFF_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredSixtyFourFF_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredSixtyFourFF_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredSixtyFourFF_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredSixtyFourFF_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredSixtyFourFF_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredSixtyFourFF_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredSixtyFourFF_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredSixtyFourFF_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredSixtyFourFF_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredSixtyFourFF_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredSixtyFourFF_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredSixtyFourFF_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredSixtyFourFF_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredSixtyFourFF_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredSixtyFourFF_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredSixtyFourFF_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredSixtyFourFF_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredSixtyFourFF_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredSixtyFourFF_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredSixtyFourFF_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredSixtyFourFF_337 : Nat.Prime 337 := by norm_num

private theorem prime_oneHundredSixtyFourFF_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredSixtyFourFF_359 : Nat.Prime 359 := by norm_num

private theorem prime_oneHundredSixtyFourFF_367 : Nat.Prime 367 := by norm_num

private theorem prime_oneHundredSixtyFourFF_379 : Nat.Prime 379 := by norm_num

private theorem prime_oneHundredSixtyFourFF_389 : Nat.Prime 389 := by norm_num

private theorem prime_oneHundredSixtyFourFF_397 : Nat.Prime 397 := by norm_num

private theorem prime_oneHundredSixtyFourFF_401 : Nat.Prime 401 := by norm_num

private theorem prime_oneHundredSixtyFourFF_439 : Nat.Prime 439 := by norm_num

private theorem prime_oneHundredSixtyFourFF_443 : Nat.Prime 443 := by norm_num

private theorem prime_oneHundredSixtyFourFF_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredSixtyFourFF_491 : Nat.Prime 491 := by norm_num

private theorem prime_oneHundredSixtyFourFF_499 : Nat.Prime 499 := by norm_num

private theorem prime_oneHundredSixtyFourFF_503 : Nat.Prime 503 := by norm_num

private theorem prime_oneHundredSixtyFourFF_523 : Nat.Prime 523 := by norm_num

private theorem prime_oneHundredSixtyFourFF_557 : Nat.Prime 557 := by norm_num

private theorem prime_oneHundredSixtyFourFF_593 : Nat.Prime 593 := by norm_num

private theorem prime_oneHundredSixtyFourFF_601 : Nat.Prime 601 := by norm_num

private theorem prime_oneHundredSixtyFourFF_617 : Nat.Prime 617 := by norm_num

private theorem prime_oneHundredSixtyFourFF_619 : Nat.Prime 619 := by norm_num

private theorem prime_oneHundredSixtyFourFF_643 : Nat.Prime 643 := by norm_num

private theorem prime_oneHundredSixtyFourFF_653 : Nat.Prime 653 := by norm_num

private theorem prime_oneHundredSixtyFourFF_659 : Nat.Prime 659 := by norm_num

private theorem prime_oneHundredSixtyFourFF_661 : Nat.Prime 661 := by norm_num

private theorem prime_oneHundredSixtyFourFF_673 : Nat.Prime 673 := by norm_num

private theorem prime_oneHundredSixtyFourFF_677 : Nat.Prime 677 := by norm_num

private theorem prime_oneHundredSixtyFourFF_683 : Nat.Prime 683 := by norm_num

private theorem prime_oneHundredSixtyFourFF_733 : Nat.Prime 733 := by norm_num

private theorem prime_oneHundredSixtyFourFF_739 : Nat.Prime 739 := by norm_num

private theorem prime_oneHundredSixtyFourFF_743 : Nat.Prime 743 := by norm_num

private theorem prime_oneHundredSixtyFourFF_757 : Nat.Prime 757 := by norm_num

private theorem prime_oneHundredSixtyFourFF_769 : Nat.Prime 769 := by norm_num

private theorem prime_oneHundredSixtyFourFF_773 : Nat.Prime 773 := by norm_num

private theorem prime_oneHundredSixtyFourFF_811 : Nat.Prime 811 := by norm_num

private theorem prime_oneHundredSixtyFourFF_853 : Nat.Prime 853 := by norm_num

private theorem prime_oneHundredSixtyFourFF_859 : Nat.Prime 859 := by norm_num

private theorem prime_oneHundredSixtyFourFF_877 : Nat.Prime 877 := by norm_num

private theorem prime_oneHundredSixtyFourFF_887 : Nat.Prime 887 := by norm_num

private theorem prime_oneHundredSixtyFourFF_907 : Nat.Prime 907 := by norm_num

private theorem prime_oneHundredSixtyFourFF_911 : Nat.Prime 911 := by norm_num

private theorem prime_oneHundredSixtyFourFF_929 : Nat.Prime 929 := by norm_num

private theorem prime_oneHundredSixtyFourFF_947 : Nat.Prime 947 := by norm_num

private theorem prime_oneHundredSixtyFourFF_953 : Nat.Prime 953 := by norm_num

private theorem prime_oneHundredSixtyFourFF_967 : Nat.Prime 967 := by norm_num

private theorem prime_oneHundredSixtyFourFF_977 : Nat.Prime 977 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1031 : Nat.Prime 1031 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1063 : Nat.Prime 1063 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1103 : Nat.Prime 1103 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1123 : Nat.Prime 1123 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1129 : Nat.Prime 1129 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1151 : Nat.Prime 1151 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1201 : Nat.Prime 1201 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1223 : Nat.Prime 1223 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1229 : Nat.Prime 1229 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1231 : Nat.Prime 1231 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1237 : Nat.Prime 1237 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1283 : Nat.Prime 1283 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1289 : Nat.Prime 1289 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1321 : Nat.Prime 1321 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1327 : Nat.Prime 1327 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1367 : Nat.Prime 1367 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1381 : Nat.Prime 1381 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1399 : Nat.Prime 1399 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1427 : Nat.Prime 1427 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1439 : Nat.Prime 1439 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1489 : Nat.Prime 1489 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1511 : Nat.Prime 1511 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1559 : Nat.Prime 1559 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1583 : Nat.Prime 1583 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1637 : Nat.Prime 1637 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1669 : Nat.Prime 1669 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1693 : Nat.Prime 1693 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1733 : Nat.Prime 1733 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1741 : Nat.Prime 1741 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1759 : Nat.Prime 1759 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1783 : Nat.Prime 1783 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1871 : Nat.Prime 1871 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1889 : Nat.Prime 1889 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1987 : Nat.Prime 1987 := by norm_num

private theorem prime_oneHundredSixtyFourFF_2003 : Nat.Prime 2003 := by norm_num

private theorem prime_oneHundredSixtyFourFF_2029 : Nat.Prime 2029 := by norm_num

private theorem prime_oneHundredSixtyFourFF_2131 : Nat.Prime 2131 := by norm_num

private theorem prime_oneHundredSixtyFourFF_2143 : Nat.Prime 2143 := by norm_num

private theorem prime_oneHundredSixtyFourFF_2221 : Nat.Prime 2221 := by norm_num

private theorem prime_oneHundredSixtyFourFF_2239 : Nat.Prime 2239 := by norm_num

private theorem prime_oneHundredSixtyFourFF_2281 : Nat.Prime 2281 := by norm_num

private theorem prime_oneHundredSixtyFourFF_2287 : Nat.Prime 2287 := by norm_num

private theorem prime_oneHundredSixtyFourFF_2297 : Nat.Prime 2297 := by norm_num

private theorem prime_oneHundredSixtyFourFF_2339 : Nat.Prime 2339 := by norm_num

private theorem prime_oneHundredSixtyFourFF_2437 : Nat.Prime 2437 := by norm_num

private theorem prime_oneHundredSixtyFourFF_2683 : Nat.Prime 2683 := by norm_num

private theorem prime_oneHundredSixtyFourFF_2693 : Nat.Prime 2693 := by norm_num

private theorem prime_oneHundredSixtyFourFF_2797 : Nat.Prime 2797 := by norm_num

private theorem prime_oneHundredSixtyFourFF_2803 : Nat.Prime 2803 := by norm_num

private theorem prime_oneHundredSixtyFourFF_2857 : Nat.Prime 2857 := by norm_num

private theorem prime_oneHundredSixtyFourFF_2897 : Nat.Prime 2897 := by norm_num

private theorem prime_oneHundredSixtyFourFF_2909 : Nat.Prime 2909 := by norm_num

private theorem prime_oneHundredSixtyFourFF_3119 : Nat.Prime 3119 := by norm_num

private theorem prime_oneHundredSixtyFourFF_3137 : Nat.Prime 3137 := by norm_num

private theorem prime_oneHundredSixtyFourFF_3163 : Nat.Prime 3163 := by norm_num

private theorem prime_oneHundredSixtyFourFF_3299 : Nat.Prime 3299 := by norm_num

private theorem prime_oneHundredSixtyFourFF_3323 : Nat.Prime 3323 := by norm_num

private theorem prime_oneHundredSixtyFourFF_3457 : Nat.Prime 3457 := by norm_num

private theorem prime_oneHundredSixtyFourFF_3461 : Nat.Prime 3461 := by norm_num

private theorem prime_oneHundredSixtyFourFF_3541 : Nat.Prime 3541 := by norm_num

private theorem prime_oneHundredSixtyFourFF_3593 : Nat.Prime 3593 := by norm_num

private theorem prime_oneHundredSixtyFourFF_3691 : Nat.Prime 3691 := by norm_num

private theorem prime_oneHundredSixtyFourFF_3709 : Nat.Prime 3709 := by norm_num

private theorem prime_oneHundredSixtyFourFF_3769 : Nat.Prime 3769 := by norm_num

private theorem prime_oneHundredSixtyFourFF_3803 : Nat.Prime 3803 := by norm_num

private theorem prime_oneHundredSixtyFourFF_3931 : Nat.Prime 3931 := by norm_num

private theorem prime_oneHundredSixtyFourFF_4241 : Nat.Prime 4241 := by norm_num

private theorem prime_oneHundredSixtyFourFF_4253 : Nat.Prime 4253 := by norm_num

private theorem prime_oneHundredSixtyFourFF_4517 : Nat.Prime 4517 := by norm_num

private theorem prime_oneHundredSixtyFourFF_4603 : Nat.Prime 4603 := by norm_num

private theorem prime_oneHundredSixtyFourFF_4621 : Nat.Prime 4621 := by norm_num

private theorem prime_oneHundredSixtyFourFF_4723 : Nat.Prime 4723 := by norm_num

private theorem prime_oneHundredSixtyFourFF_4933 : Nat.Prime 4933 := by norm_num

private theorem prime_oneHundredSixtyFourFF_4951 : Nat.Prime 4951 := by norm_num

private theorem prime_oneHundredSixtyFourFF_5167 : Nat.Prime 5167 := by norm_num

private theorem prime_oneHundredSixtyFourFF_5399 : Nat.Prime 5399 := by norm_num

private theorem prime_oneHundredSixtyFourFF_5569 : Nat.Prime 5569 := by norm_num

private theorem prime_oneHundredSixtyFourFF_5779 : Nat.Prime 5779 := by norm_num

private theorem prime_oneHundredSixtyFourFF_5791 : Nat.Prime 5791 := by norm_num

private theorem prime_oneHundredSixtyFourFF_6199 : Nat.Prime 6199 := by norm_num

private theorem prime_oneHundredSixtyFourFF_7229 : Nat.Prime 7229 := by norm_num

private theorem prime_oneHundredSixtyFourFF_7561 : Nat.Prime 7561 := by norm_num

private theorem prime_oneHundredSixtyFourFF_7703 : Nat.Prime 7703 := by norm_num

private theorem prime_oneHundredSixtyFourFF_8009 : Nat.Prime 8009 := by norm_num

private theorem prime_oneHundredSixtyFourFF_8081 : Nat.Prime 8081 := by norm_num

private theorem prime_oneHundredSixtyFourFF_8273 : Nat.Prime 8273 := by norm_num

private theorem prime_oneHundredSixtyFourFF_8537 : Nat.Prime 8537 := by norm_num

private theorem prime_oneHundredSixtyFourFF_8837 : Nat.Prime 8837 := by norm_num

private theorem prime_oneHundredSixtyFourFF_8861 : Nat.Prime 8861 := by norm_num

private theorem prime_oneHundredSixtyFourFF_9551 : Nat.Prime 9551 := by norm_num

private theorem prime_oneHundredSixtyFourFF_10139 : Nat.Prime 10139 := by norm_num

private theorem prime_oneHundredSixtyFourFF_10337 : Nat.Prime 10337 := by norm_num

private theorem prime_oneHundredSixtyFourFF_10499 : Nat.Prime 10499 := by norm_num

private theorem prime_oneHundredSixtyFourFF_10597 : Nat.Prime 10597 := by norm_num

private theorem prime_oneHundredSixtyFourFF_10789 : Nat.Prime 10789 := by norm_num

private theorem prime_oneHundredSixtyFourFF_11399 : Nat.Prime 11399 := by norm_num

private theorem prime_oneHundredSixtyFourFF_11549 : Nat.Prime 11549 := by norm_num

private theorem prime_oneHundredSixtyFourFF_11801 : Nat.Prime 11801 := by norm_num

private theorem prime_oneHundredSixtyFourFF_11939 : Nat.Prime 11939 := by norm_num

private theorem prime_oneHundredSixtyFourFF_12143 : Nat.Prime 12143 := by norm_num

private theorem prime_oneHundredSixtyFourFF_12241 : Nat.Prime 12241 := by norm_num

private theorem prime_oneHundredSixtyFourFF_12547 : Nat.Prime 12547 := by norm_num

private theorem prime_oneHundredSixtyFourFF_12923 : Nat.Prime 12923 := by norm_num

private theorem prime_oneHundredSixtyFourFF_13859 : Nat.Prime 13859 := by norm_num

private theorem prime_oneHundredSixtyFourFF_13963 : Nat.Prime 13963 := by norm_num

private theorem prime_oneHundredSixtyFourFF_14461 : Nat.Prime 14461 := by norm_num

private theorem prime_oneHundredSixtyFourFF_15173 : Nat.Prime 15173 := by norm_num

private theorem prime_oneHundredSixtyFourFF_15319 : Nat.Prime 15319 := by norm_num

private theorem prime_oneHundredSixtyFourFF_15823 : Nat.Prime 15823 := by norm_num

private theorem prime_oneHundredSixtyFourFF_16567 : Nat.Prime 16567 := by norm_num

private theorem prime_oneHundredSixtyFourFF_17191 : Nat.Prime 17191 := by norm_num

private theorem prime_oneHundredSixtyFourFF_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredSixtyFourFF_17509 : Nat.Prime 17509 := by norm_num

private theorem prime_oneHundredSixtyFourFF_17573 : Nat.Prime 17573 := by norm_num

private theorem prime_oneHundredSixtyFourFF_17737 : Nat.Prime 17737 := by norm_num

private theorem prime_oneHundredSixtyFourFF_17971 : Nat.Prime 17971 := by norm_num

private theorem prime_oneHundredSixtyFourFF_18797 : Nat.Prime 18797 := by norm_num

private theorem prime_oneHundredSixtyFourFF_19207 : Nat.Prime 19207 := by norm_num

private theorem prime_oneHundredSixtyFourFF_19429 : Nat.Prime 19429 := by norm_num

private theorem prime_oneHundredSixtyFourFF_19979 : Nat.Prime 19979 := by norm_num

private theorem prime_oneHundredSixtyFourFF_20173 : Nat.Prime 20173 := by norm_num

private theorem prime_oneHundredSixtyFourFF_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredSixtyFourFF_21347 : Nat.Prime 21347 := by norm_num

private theorem prime_oneHundredSixtyFourFF_21817 : Nat.Prime 21817 := by norm_num

private theorem prime_oneHundredSixtyFourFF_22091 : Nat.Prime 22091 := by norm_num

private theorem prime_oneHundredSixtyFourFF_22369 : Nat.Prime 22369 := by norm_num

private theorem prime_oneHundredSixtyFourFF_22397 : Nat.Prime 22397 := by norm_num

private theorem prime_oneHundredSixtyFourFF_22811 : Nat.Prime 22811 := by norm_num

private theorem prime_oneHundredSixtyFourFF_23027 : Nat.Prime 23027 := by norm_num

private theorem prime_oneHundredSixtyFourFF_23143 : Nat.Prime 23143 := by norm_num

private theorem prime_oneHundredSixtyFourFF_23497 : Nat.Prime 23497 := by norm_num

private theorem prime_oneHundredSixtyFourFF_23539 : Nat.Prime 23539 := by norm_num

private theorem prime_oneHundredSixtyFourFF_23819 : Nat.Prime 23819 := by norm_num

private theorem prime_oneHundredSixtyFourFF_24181 : Nat.Prime 24181 := by norm_num

private theorem prime_oneHundredSixtyFourFF_26399 : Nat.Prime 26399 := by norm_num

private theorem prime_oneHundredSixtyFourFF_26479 : Nat.Prime 26479 := by norm_num

private theorem prime_oneHundredSixtyFourFF_26953 : Nat.Prime 26953 := by norm_num

private theorem prime_oneHundredSixtyFourFF_28219 : Nat.Prime 28219 := by norm_num

private theorem prime_oneHundredSixtyFourFF_28277 : Nat.Prime 28277 := by norm_num

private theorem prime_oneHundredSixtyFourFF_28687 : Nat.Prime 28687 := by norm_num

private theorem prime_oneHundredSixtyFourFF_28933 : Nat.Prime 28933 := by norm_num

private theorem prime_oneHundredSixtyFourFF_29129 : Nat.Prime 29129 := by norm_num

private theorem prime_oneHundredSixtyFourFF_30427 : Nat.Prime 30427 := by norm_num

private theorem prime_oneHundredSixtyFourFF_30949 : Nat.Prime 30949 := by norm_num

private theorem prime_oneHundredSixtyFourFF_31513 : Nat.Prime 31513 := by norm_num

private theorem prime_oneHundredSixtyFourFF_32203 : Nat.Prime 32203 := by norm_num

private theorem prime_oneHundredSixtyFourFF_33301 : Nat.Prime 33301 := by norm_num

private theorem prime_oneHundredSixtyFourFF_34267 : Nat.Prime 34267 := by norm_num

private theorem prime_oneHundredSixtyFourFF_36263 : Nat.Prime 36263 := by norm_num

private theorem prime_oneHundredSixtyFourFF_36343 : Nat.Prime 36343 := by norm_num

private theorem prime_oneHundredSixtyFourFF_36713 : Nat.Prime 36713 := by norm_num

private theorem prime_oneHundredSixtyFourFF_36901 : Nat.Prime 36901 := by norm_num

private theorem prime_oneHundredSixtyFourFF_39293 : Nat.Prime 39293 := by norm_num

private theorem prime_oneHundredSixtyFourFF_39827 : Nat.Prime 39827 := by norm_num

private theorem prime_oneHundredSixtyFourFF_40189 : Nat.Prime 40189 := by norm_num

private theorem prime_oneHundredSixtyFourFF_40343 : Nat.Prime 40343 := by norm_num

private theorem prime_oneHundredSixtyFourFF_40597 : Nat.Prime 40597 := by norm_num

private theorem prime_oneHundredSixtyFourFF_41887 : Nat.Prime 41887 := by norm_num

private theorem prime_oneHundredSixtyFourFF_43291 : Nat.Prime 43291 := by norm_num

private theorem prime_oneHundredSixtyFourFF_43319 : Nat.Prime 43319 := by norm_num

private theorem prime_oneHundredSixtyFourFF_45119 : Nat.Prime 45119 := by norm_num

private theorem prime_oneHundredSixtyFourFF_45767 : Nat.Prime 45767 := by norm_num

private theorem prime_oneHundredSixtyFourFF_46687 : Nat.Prime 46687 := by norm_num

private theorem prime_oneHundredSixtyFourFF_47381 : Nat.Prime 47381 := by norm_num

private theorem prime_oneHundredSixtyFourFF_48017 : Nat.Prime 48017 := by norm_num

private theorem prime_oneHundredSixtyFourFF_49393 : Nat.Prime 49393 := by norm_num

private theorem prime_oneHundredSixtyFourFF_56099 : Nat.Prime 56099 := by norm_num

private theorem prime_oneHundredSixtyFourFF_61031 : Nat.Prime 61031 := by norm_num

private theorem prime_oneHundredSixtyFourFF_61261 : Nat.Prime 61261 := by norm_num

private theorem prime_oneHundredSixtyFourFF_63601 : Nat.Prime 63601 := by norm_num

private theorem prime_oneHundredSixtyFourFF_63689 : Nat.Prime 63689 := by norm_num

private theorem prime_oneHundredSixtyFourFF_64937 : Nat.Prime 64937 := by norm_num

private theorem prime_oneHundredSixtyFourFF_65867 : Nat.Prime 65867 := by norm_num

private theorem prime_oneHundredSixtyFourFF_65899 : Nat.Prime 65899 := by norm_num

private theorem prime_oneHundredSixtyFourFF_67559 : Nat.Prime 67559 := by norm_num

private theorem prime_oneHundredSixtyFourFF_69997 : Nat.Prime 69997 := by norm_num

private theorem prime_oneHundredSixtyFourFF_72221 : Nat.Prime 72221 := by norm_num

private theorem prime_oneHundredSixtyFourFF_74573 : Nat.Prime 74573 := by norm_num

private theorem prime_oneHundredSixtyFourFF_77347 : Nat.Prime 77347 := by norm_num

private theorem prime_oneHundredSixtyFourFF_77527 : Nat.Prime 77527 := by norm_num

private theorem prime_oneHundredSixtyFourFF_83423 : Nat.Prime 83423 := by norm_num

private theorem prime_oneHundredSixtyFourFF_85297 : Nat.Prime 85297 := by norm_num

private theorem prime_oneHundredSixtyFourFF_85639 : Nat.Prime 85639 := by norm_num

private theorem prime_oneHundredSixtyFourFF_91253 : Nat.Prime 91253 := by norm_num

private theorem prime_oneHundredSixtyFourFF_94439 : Nat.Prime 94439 := by norm_num

private theorem prime_oneHundredSixtyFourFF_96457 : Nat.Prime 96457 := by norm_num

private theorem prime_oneHundredSixtyFourFF_97003 : Nat.Prime 97003 := by norm_num

private theorem prime_oneHundredSixtyFourFF_104123 : Nat.Prime 104123 := by norm_num

private theorem prime_oneHundredSixtyFourFF_105619 : Nat.Prime 105619 := by norm_num

private theorem prime_oneHundredSixtyFourFF_108739 : Nat.Prime 108739 := by norm_num

private theorem prime_oneHundredSixtyFourFF_115319 : Nat.Prime 115319 := by norm_num

private theorem prime_oneHundredSixtyFourFF_121553 : Nat.Prime 121553 := by norm_num

private theorem prime_oneHundredSixtyFourFF_123737 : Nat.Prime 123737 := by norm_num

private theorem prime_oneHundredSixtyFourFF_125711 : Nat.Prime 125711 := by norm_num

private theorem prime_oneHundredSixtyFourFF_143257 : Nat.Prime 143257 := by norm_num

private theorem prime_oneHundredSixtyFourFF_147557 : Nat.Prime 147557 := by norm_num

private theorem prime_oneHundredSixtyFourFF_151717 : Nat.Prime 151717 := by norm_num

private theorem prime_oneHundredSixtyFourFF_159869 : Nat.Prime 159869 := by norm_num

private theorem prime_oneHundredSixtyFourFF_160343 : Nat.Prime 160343 := by norm_num

private theorem prime_oneHundredSixtyFourFF_163883 : Nat.Prime 163883 := by norm_num

private theorem prime_oneHundredSixtyFourFF_164627 : Nat.Prime 164627 := by norm_num

private theorem prime_oneHundredSixtyFourFF_166189 : Nat.Prime 166189 := by norm_num

private theorem prime_oneHundredSixtyFourFF_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredSixtyFourFF_174299 : Nat.Prime 174299 := by norm_num

private theorem prime_oneHundredSixtyFourFF_187513 : Nat.Prime 187513 := by norm_num

private theorem prime_oneHundredSixtyFourFF_190147 : Nat.Prime 190147 := by norm_num

private theorem prime_oneHundredSixtyFourFF_203221 : Nat.Prime 203221 := by norm_num

private theorem prime_oneHundredSixtyFourFF_208889 : Nat.Prime 208889 := by norm_num

private theorem prime_oneHundredSixtyFourFF_224993 : Nat.Prime 224993 := by norm_num

private theorem prime_oneHundredSixtyFourFF_226649 : Nat.Prime 226649 := by norm_num

private theorem prime_oneHundredSixtyFourFF_232681 : Nat.Prime 232681 := by norm_num

private theorem prime_oneHundredSixtyFourFF_236399 : Nat.Prime 236399 := by norm_num

private theorem prime_oneHundredSixtyFourFF_245299 : Nat.Prime 245299 := by norm_num

private theorem prime_oneHundredSixtyFourFF_246929 : Nat.Prime 246929 := by norm_num

private theorem prime_oneHundredSixtyFourFF_247943 : Nat.Prime 247943 := by norm_num

private theorem prime_oneHundredSixtyFourFF_257893 : Nat.Prime 257893 := by norm_num

private theorem prime_oneHundredSixtyFourFF_273913 : Nat.Prime 273913 := by norm_num

private theorem prime_oneHundredSixtyFourFF_284831 : Nat.Prime 284831 := by norm_num

private theorem prime_oneHundredSixtyFourFF_301759 : Nat.Prime 301759 := by norm_num

private theorem prime_oneHundredSixtyFourFF_306517 : Nat.Prime 306517 := by norm_num

private theorem prime_oneHundredSixtyFourFF_325249 : Nat.Prime 325249 := by norm_num

private theorem prime_oneHundredSixtyFourFF_327251 : Nat.Prime 327251 := by norm_num

private theorem prime_oneHundredSixtyFourFF_347969 : Nat.Prime 347969 := by norm_num

private theorem prime_oneHundredSixtyFourFF_348911 : Nat.Prime 348911 := by norm_num

private theorem prime_oneHundredSixtyFourFF_362027 : Nat.Prime 362027 := by norm_num

private theorem prime_oneHundredSixtyFourFF_419929 : Nat.Prime 419929 := by norm_num

private theorem prime_oneHundredSixtyFourFF_419953 : Nat.Prime 419953 := by norm_num

private theorem prime_oneHundredSixtyFourFF_436463 : Nat.Prime 436463 := by norm_num

private theorem prime_oneHundredSixtyFourFF_437509 : Nat.Prime 437509 := by norm_num

private theorem prime_oneHundredSixtyFourFF_450529 : Nat.Prime 450529 := by norm_num

private theorem prime_oneHundredSixtyFourFF_487079 : Nat.Prime 487079 := by norm_num

private theorem prime_oneHundredSixtyFourFF_498521 : Nat.Prime 498521 := by norm_num

private theorem prime_oneHundredSixtyFourFF_518953 : Nat.Prime 518953 := by norm_num

private theorem prime_oneHundredSixtyFourFF_531133 : Nat.Prime 531133 := by norm_num

private theorem prime_oneHundredSixtyFourFF_539111 : Nat.Prime 539111 := by norm_num

private theorem prime_oneHundredSixtyFourFF_543281 : Nat.Prime 543281 := by norm_num

private theorem prime_oneHundredSixtyFourFF_566701 : Nat.Prime 566701 := by norm_num

private theorem prime_oneHundredSixtyFourFF_567467 : Nat.Prime 567467 := by norm_num

private theorem prime_oneHundredSixtyFourFF_603667 : Nat.Prime 603667 := by norm_num

private theorem prime_oneHundredSixtyFourFF_635287 : Nat.Prime 635287 := by norm_num

private theorem prime_oneHundredSixtyFourFF_636931 : Nat.Prime 636931 := by norm_num

private theorem prime_oneHundredSixtyFourFF_659783 : Nat.Prime 659783 := by norm_num

private theorem prime_oneHundredSixtyFourFF_665479 : Nat.Prime 665479 := by norm_num

private theorem prime_oneHundredSixtyFourFF_722147 : Nat.Prime 722147 := by norm_num

private theorem prime_oneHundredSixtyFourFF_736277 : Nat.Prime 736277 := by norm_num

private theorem prime_oneHundredSixtyFourFF_739117 : Nat.Prime 739117 := by norm_num

private theorem prime_oneHundredSixtyFourFF_800801 : Nat.Prime 800801 := by norm_num

private theorem prime_oneHundredSixtyFourFF_851293 : Nat.Prime 851293 := by norm_num

private theorem prime_oneHundredSixtyFourFF_856147 : Nat.Prime 856147 := by norm_num

private theorem prime_oneHundredSixtyFourFF_913259 : Nat.Prime 913259 := by norm_num

private theorem prime_oneHundredSixtyFourFF_944551 : Nat.Prime 944551 := by norm_num

private theorem prime_oneHundredSixtyFourFF_954067 : Nat.Prime 954067 := by norm_num

private theorem prime_oneHundredSixtyFourFF_959377 : Nat.Prime 959377 := by norm_num

private theorem prime_oneHundredSixtyFourFF_963239 : Nat.Prime 963239 := by norm_num

private theorem prime_oneHundredSixtyFourFF_974969 : Nat.Prime 974969 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1034959 : Nat.Prime 1034959 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1069727 : Nat.Prime 1069727 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1146703 : Nat.Prime 1146703 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1326653 : Nat.Prime 1326653 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1336729 : Nat.Prime 1336729 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1388603 : Nat.Prime 1388603 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1390913 : Nat.Prime 1390913 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1477139 : Nat.Prime 1477139 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1700723 : Nat.Prime 1700723 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1789559 : Nat.Prime 1789559 := by norm_num

private theorem prime_oneHundredSixtyFourFF_1809491 : Nat.Prime 1809491 := by norm_num

private theorem prime_oneHundredSixtyFourFF_2009593 : Nat.Prime 2009593 := by norm_num

private theorem prime_oneHundredSixtyFourFF_2022701 : Nat.Prime 2022701 := by norm_num

private theorem prime_oneHundredSixtyFourFF_2046719 : Nat.Prime 2046719 := by norm_num

private theorem prime_oneHundredSixtyFourFF_2070643 : Nat.Prime 2070643 := by norm_num

private theorem prime_oneHundredSixtyFourFF_2096209 : Nat.Prime 2096209 := by norm_num

private theorem prime_oneHundredSixtyFourFF_2439301 : Nat.Prime 2439301 := by norm_num

private theorem prime_oneHundredSixtyFourFF_2479049 : Nat.Prime 2479049 := by norm_num

private theorem prime_oneHundredSixtyFourFF_2608519 : Nat.Prime 2608519 := by norm_num

private theorem prime_oneHundredSixtyFourFF_2647343 : Nat.Prime 2647343 := by norm_num

private theorem prime_oneHundredSixtyFourFF_2663497 : Nat.Prime 2663497 := by norm_num

private theorem prime_oneHundredSixtyFourFF_2811989 : Nat.Prime 2811989 := by norm_num

private theorem prime_oneHundredSixtyFourFF_2889599 : Nat.Prime 2889599 := by norm_num

private theorem prime_oneHundredSixtyFourFF_2911193 : Nat.Prime 2911193 := by norm_num

private theorem prime_oneHundredSixtyFourFF_2921563 : Nat.Prime 2921563 := by norm_num

private theorem prime_oneHundredSixtyFourFF_2960861 : Nat.Prime 2960861 := by norm_num

private theorem prime_oneHundredSixtyFourFF_3248689 : Nat.Prime 3248689 := by norm_num

private theorem prime_oneHundredSixtyFourFF_3437261 : Nat.Prime 3437261 := by norm_num

private theorem prime_oneHundredSixtyFourFF_4097113 : Nat.Prime 4097113 := by norm_num

private theorem prime_oneHundredSixtyFourFF_4576063 : Nat.Prime 4576063 := by norm_num

private theorem prime_oneHundredSixtyFourFF_4637947 : Nat.Prime 4637947 := by norm_num

private theorem prime_oneHundredSixtyFourFF_4674443 : Nat.Prime 4674443 := by norm_num

private theorem prime_oneHundredSixtyFourFF_4690811 : Nat.Prime 4690811 := by norm_num

private theorem prime_oneHundredSixtyFourFF_4719287 : Nat.Prime 4719287 := by norm_num

private theorem prime_oneHundredSixtyFourFF_5262667 : Nat.Prime 5262667 := by norm_num

private theorem prime_oneHundredSixtyFourFF_5312953 : Nat.Prime 5312953 := by norm_num

private theorem prime_oneHundredSixtyFourFF_5488591 : Nat.Prime 5488591 := by norm_num

private theorem prime_oneHundredSixtyFourFF_5646349 : Nat.Prime 5646349 := by norm_num

private theorem prime_oneHundredSixtyFourFF_6004067 : Nat.Prime 6004067 := by norm_num

private theorem prime_oneHundredSixtyFourFF_6065483 : Nat.Prime 6065483 := by norm_num

private theorem prime_oneHundredSixtyFourFF_6098947 : Nat.Prime 6098947 := by norm_num

private theorem prime_oneHundredSixtyFourFF_6362311 : Nat.Prime 6362311 := by norm_num

private theorem prime_oneHundredSixtyFourFF_6498727 : Nat.Prime 6498727 := by norm_num

private theorem prime_oneHundredSixtyFourFF_6834551 : Nat.Prime 6834551 := by norm_num

private theorem prime_oneHundredSixtyFourFF_7149353 : Nat.Prime 7149353 := by norm_num

private theorem prime_oneHundredSixtyFourFF_8248369 : Nat.Prime 8248369 := by norm_num

private theorem prime_oneHundredSixtyFourFF_8409889 : Nat.Prime 8409889 := by norm_num

private theorem prime_oneHundredSixtyFourFF_9042907 : Nat.Prime 9042907 := by norm_num

private theorem prime_oneHundredSixtyFourFF_10040057 : Nat.Prime 10040057 := by norm_num

private theorem prime_oneHundredSixtyFourFF_10540379 : Nat.Prime 10540379 := by norm_num

private theorem prime_oneHundredSixtyFourFF_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredSixtyFourFF_11109611 : Nat.Prime 11109611 := by norm_num

private theorem prime_oneHundredSixtyFourFF_11231657 : Nat.Prime 11231657 := by norm_num

private theorem prime_oneHundredSixtyFourFF_12126643 : Nat.Prime 12126643 := by norm_num

private theorem prime_oneHundredSixtyFourFF_12312661 : Nat.Prime 12312661 := by norm_num

private theorem prime_oneHundredSixtyFourFF_13417171 : Nat.Prime 13417171 := by norm_num

private theorem prime_oneHundredSixtyFourFF_13439191 : Nat.Prime 13439191 := by norm_num

private theorem prime_oneHundredSixtyFourFF_13681211 : Nat.Prime 13681211 := by norm_num

private theorem prime_oneHundredSixtyFourFF_14356061 : Nat.Prime 14356061 := by norm_num

private theorem prime_oneHundredSixtyFourFF_14427541 : Nat.Prime 14427541 := by norm_num

private theorem prime_oneHundredSixtyFourFF_14996321 : Nat.Prime 14996321 := by norm_num

private theorem prime_oneHundredSixtyFourFF_15805613 : Nat.Prime 15805613 := by norm_num

private theorem prime_oneHundredSixtyFourFF_16050487 : Nat.Prime 16050487 := by norm_num

private theorem prime_oneHundredSixtyFourFF_17233577 : Nat.Prime 17233577 := by norm_num

private theorem prime_oneHundredSixtyFourFF_20295391 : Nat.Prime 20295391 := by norm_num

private theorem prime_oneHundredSixtyFourFF_20697107 : Nat.Prime 20697107 := by norm_num

private theorem prime_oneHundredSixtyFourFF_21723721 : Nat.Prime 21723721 := by norm_num

private theorem prime_oneHundredSixtyFourFF_21866027 : Nat.Prime 21866027 := by norm_num

private theorem prime_oneHundredSixtyFourFF_25064989 : Nat.Prime 25064989 := by norm_num

private theorem prime_oneHundredSixtyFourFF_25285133 : Nat.Prime 25285133 := by norm_num

private theorem prime_oneHundredSixtyFourFF_29850787 : Nat.Prime 29850787 := by norm_num

private theorem prime_oneHundredSixtyFourFF_32499919 : Nat.Prime 32499919 := by
  apply lucas_primality 32499919 (3 : ZMod 32499919)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (19, 1), (53, 1), (163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (19, 1), (53, 1), (163, 1)] : List FactorBlock).map factorBlockValue).prod) = 32499919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_11
      · exact prime_oneHundredSixtyFourFF_19
      · exact prime_oneHundredSixtyFourFF_53
      · exact prime_oneHundredSixtyFourFF_163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 32499919) ^ 16249959 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 32499919) ^ 10833306 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 32499919) ^ 2954538 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 32499919) ^ 1710522 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 32499919) ^ 613206 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 32499919) ^ 199386 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_33476693 : Nat.Prime 33476693 := by
  apply lucas_primality 33476693 (2 : ZMod 33476693)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (127, 1), (65899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (127, 1), (65899, 1)] : List FactorBlock).map factorBlockValue).prod) = 33476693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_127
      · exact prime_oneHundredSixtyFourFF_65899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 33476693) ^ 16738346 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 33476693) ^ 263596 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 33476693) ^ 508 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_34681573 : Nat.Prime 34681573 := by
  apply lucas_primality 34681573 (2 : ZMod 34681573)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (41, 1), (23497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (41, 1), (23497, 1)] : List FactorBlock).map factorBlockValue).prod) = 34681573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_41
      · exact prime_oneHundredSixtyFourFF_23497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 34681573) ^ 17340786 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 34681573) ^ 11560524 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 34681573) ^ 845892 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 34681573) ^ 1476 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_34954709 : Nat.Prime 34954709 := by
  apply lucas_primality 34954709 (2 : ZMod 34954709)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (61, 1), (143257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (61, 1), (143257, 1)] : List FactorBlock).map factorBlockValue).prod) = 34954709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_61
      · exact prime_oneHundredSixtyFourFF_143257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 34954709) ^ 17477354 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 34954709) ^ 573028 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 34954709) ^ 244 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_37742767 : Nat.Prime 37742767 := by
  apply lucas_primality 37742767 (3 : ZMod 37742767)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1669, 1), (3769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1669, 1), (3769, 1)] : List FactorBlock).map factorBlockValue).prod) = 37742767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_1669
      · exact prime_oneHundredSixtyFourFF_3769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 37742767) ^ 18871383 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 37742767) ^ 12580922 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 37742767) ^ 22614 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 37742767) ^ 10014 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_39231469 : Nat.Prime 39231469 := by
  apply lucas_primality 39231469 (2 : ZMod 39231469)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (23, 1), (47381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (23, 1), (47381, 1)] : List FactorBlock).map factorBlockValue).prod) = 39231469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_23
      · exact prime_oneHundredSixtyFourFF_47381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 39231469) ^ 19615734 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 39231469) ^ 13077156 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 39231469) ^ 1705716 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 39231469) ^ 828 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_39668467 : Nat.Prime 39668467 := by
  apply lucas_primality 39668467 (2 : ZMod 39668467)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (347969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (347969, 1)] : List FactorBlock).map factorBlockValue).prod) = 39668467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_19
      · exact prime_oneHundredSixtyFourFF_347969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 39668467) ^ 19834233 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 39668467) ^ 13222822 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 39668467) ^ 2087814 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 39668467) ^ 114 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_40934381 : Nat.Prime 40934381 := by
  apply lucas_primality 40934381 (2 : ZMod 40934381)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (2046719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (2046719, 1)] : List FactorBlock).map factorBlockValue).prod) = 40934381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_2046719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 40934381) ^ 20467190 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 40934381) ^ 8186876 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 40934381) ^ 20 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_43071731 : Nat.Prime 43071731 := by
  apply lucas_primality 43071731 (2 : ZMod 43071731)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (41, 1), (8081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (41, 1), (8081, 1)] : List FactorBlock).map factorBlockValue).prod) = 43071731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_13
      · exact prime_oneHundredSixtyFourFF_41
      · exact prime_oneHundredSixtyFourFF_8081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 43071731) ^ 21535865 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 43071731) ^ 8614346 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 43071731) ^ 3313210 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 43071731) ^ 1050530 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 43071731) ^ 5330 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_47733743 : Nat.Prime 47733743 := by
  apply lucas_primality 47733743 (5 : ZMod 47733743)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (487079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (487079, 1)] : List FactorBlock).map factorBlockValue).prod) = 47733743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_487079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 47733743) ^ 23866871 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 47733743) ^ 6819106 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 47733743) ^ 98 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_48547621 : Nat.Prime 48547621 := by
  apply lucas_primality 48547621 (2 : ZMod 48547621)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (11, 2), (743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (11, 2), (743, 1)] : List FactorBlock).map factorBlockValue).prod) = 48547621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_11
      · exact prime_oneHundredSixtyFourFF_743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 48547621) ^ 24273810 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 48547621) ^ 16182540 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 48547621) ^ 9709524 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 48547621) ^ 4413420 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 48547621) ^ 65340 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_51047459 : Nat.Prime 51047459 := by
  apply lucas_primality 51047459 (2 : ZMod 51047459)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (503, 1), (659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (503, 1), (659, 1)] : List FactorBlock).map factorBlockValue).prod) = 51047459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_11
      · exact prime_oneHundredSixtyFourFF_503
      · exact prime_oneHundredSixtyFourFF_659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 51047459) ^ 25523729 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 51047459) ^ 7292494 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 51047459) ^ 4640678 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 51047459) ^ 101486 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 51047459) ^ 77462 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_51131497 : Nat.Prime 51131497 := by
  apply lucas_primality 51131497 (5 : ZMod 51131497)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (163883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (163883, 1)] : List FactorBlock).map factorBlockValue).prod) = 51131497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_13
      · exact prime_oneHundredSixtyFourFF_163883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 51131497) ^ 25565748 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 51131497) ^ 17043832 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 51131497) ^ 3933192 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 51131497) ^ 312 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_54284731 : Nat.Prime 54284731 := by
  apply lucas_primality 54284731 (3 : ZMod 54284731)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1809491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1809491, 1)] : List FactorBlock).map factorBlockValue).prod) = 54284731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_1809491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 54284731) ^ 27142365 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 54284731) ^ 18094910 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 54284731) ^ 10856946 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 54284731) ^ 30 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_59929613 : Nat.Prime 59929613 := by
  apply lucas_primality 59929613 (2 : ZMod 59929613)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) = 59929613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_1811
      · exact prime_oneHundredSixtyFourFF_8273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59929613) ^ 29964806 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 33092 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 7244 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_62383637 : Nat.Prime 62383637 := by
  apply lucas_primality 62383637 (3 : ZMod 62383637)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (23, 1), (157, 1), (617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (23, 1), (157, 1), (617, 1)] : List FactorBlock).map factorBlockValue).prod) = 62383637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_23
      · exact prime_oneHundredSixtyFourFF_157
      · exact prime_oneHundredSixtyFourFF_617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 62383637) ^ 31191818 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 62383637) ^ 8911948 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 62383637) ^ 2712332 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 62383637) ^ 397348 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 62383637) ^ 101108 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_69909419 : Nat.Prime 69909419 := by
  apply lucas_primality 69909419 (2 : ZMod 69909419)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (34954709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (34954709, 1)] : List FactorBlock).map factorBlockValue).prod) = 69909419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_34954709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 69909419) ^ 34954709 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 69909419) ^ 2 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_72759859 : Nat.Prime 72759859 := by
  apply lucas_primality 72759859 (3 : ZMod 72759859)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (12126643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (12126643, 1)] : List FactorBlock).map factorBlockValue).prod) = 72759859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_12126643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 72759859) ^ 36379929 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 72759859) ^ 24253286 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 72759859) ^ 6 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_82087267 : Nat.Prime 82087267 := by
  apply lucas_primality 82087267 (3 : ZMod 82087267)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13681211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13681211, 1)] : List FactorBlock).map factorBlockValue).prod) = 82087267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_13681211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 82087267) ^ 41043633 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 82087267) ^ 27362422 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 82087267) ^ 6 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_82758073 : Nat.Prime 82758073 := by
  apply lucas_primality 82758073 (10 : ZMod 82758073)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (97, 1), (1871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (97, 1), (1871, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_19
      · exact prime_oneHundredSixtyFourFF_97
      · exact prime_oneHundredSixtyFourFF_1871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 82758073) ^ 41379036 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (10 : ZMod 82758073) ^ 27586024 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (10 : ZMod 82758073) ^ 4355688 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (10 : ZMod 82758073) ^ 853176 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (10 : ZMod 82758073) ^ 44232 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_93130421 : Nat.Prime 93130421 := by
  apply lucas_primality 93130421 (2 : ZMod 93130421)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 1), (273913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 1), (273913, 1)] : List FactorBlock).map factorBlockValue).prod) = 93130421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_17
      · exact prime_oneHundredSixtyFourFF_273913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 93130421) ^ 46565210 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 93130421) ^ 18626084 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 93130421) ^ 5478260 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 93130421) ^ 340 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_96302923 : Nat.Prime 96302923 := by
  apply lucas_primality 96302923 (2 : ZMod 96302923)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (16050487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (16050487, 1)] : List FactorBlock).map factorBlockValue).prod) = 96302923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_16050487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 96302923) ^ 48151461 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 96302923) ^ 32100974 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 96302923) ^ 6 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_102534983 : Nat.Prime 102534983 := by
  apply lucas_primality 102534983 (5 : ZMod 102534983)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (245299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (245299, 1)] : List FactorBlock).map factorBlockValue).prod) = 102534983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_11
      · exact prime_oneHundredSixtyFourFF_19
      · exact prime_oneHundredSixtyFourFF_245299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 102534983) ^ 51267491 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 9321362 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 5396578 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 418 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_126406999 : Nat.Prime 126406999 := by
  apply lucas_primality 126406999 (11 : ZMod 126406999)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (29, 1), (113, 1), (2143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (29, 1), (113, 1), (2143, 1)] : List FactorBlock).map factorBlockValue).prod) = 126406999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_29
      · exact prime_oneHundredSixtyFourFF_113
      · exact prime_oneHundredSixtyFourFF_2143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 126406999) ^ 63203499 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 126406999) ^ 42135666 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 126406999) ^ 4358862 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 126406999) ^ 1118646 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 126406999) ^ 58986 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_127847857 : Nat.Prime 127847857 := by
  apply lucas_primality 127847857 (5 : ZMod 127847857)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (2663497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (2663497, 1)] : List FactorBlock).map factorBlockValue).prod) = 127847857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_2663497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 127847857) ^ 63923928 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 127847857) ^ 42615952 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 127847857) ^ 48 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_129862517 : Nat.Prime 129862517 := by
  apply lucas_primality 129862517 (2 : ZMod 129862517)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (4637947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (4637947, 1)] : List FactorBlock).map factorBlockValue).prod) = 129862517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_4637947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 129862517) ^ 64931258 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 129862517) ^ 18551788 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 129862517) ^ 28 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_140866157 : Nat.Prime 140866157 := by
  apply lucas_primality 140866157 (2 : ZMod 140866157)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (53, 1), (503, 1), (1321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (53, 1), (503, 1), (1321, 1)] : List FactorBlock).map factorBlockValue).prod) = 140866157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_53
      · exact prime_oneHundredSixtyFourFF_503
      · exact prime_oneHundredSixtyFourFF_1321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 140866157) ^ 70433078 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 140866157) ^ 2657852 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 140866157) ^ 280052 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 140866157) ^ 106636 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_142724963 : Nat.Prime 142724963 := by
  apply lucas_primality 142724963 (2 : ZMod 142724963)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 2), (246929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 2), (246929, 1)] : List FactorBlock).map factorBlockValue).prod) = 142724963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_17
      · exact prime_oneHundredSixtyFourFF_246929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 142724963) ^ 71362481 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 142724963) ^ 8395586 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 142724963) ^ 578 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_143590061 : Nat.Prime 143590061 := by
  apply lucas_primality 143590061 (2 : ZMod 143590061)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (109, 1), (65867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (109, 1), (65867, 1)] : List FactorBlock).map factorBlockValue).prod) = 143590061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_109
      · exact prime_oneHundredSixtyFourFF_65867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 143590061) ^ 71795030 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 143590061) ^ 28718012 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 143590061) ^ 1317340 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 143590061) ^ 2180 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_145006877 : Nat.Prime 145006877 := by
  apply lucas_primality 145006877 (2 : ZMod 145006877)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (601, 1), (1231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (601, 1), (1231, 1)] : List FactorBlock).map factorBlockValue).prod) = 145006877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_601
      · exact prime_oneHundredSixtyFourFF_1231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 145006877) ^ 72503438 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 145006877) ^ 20715268 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 145006877) ^ 241276 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 145006877) ^ 117796 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_147009893 : Nat.Prime 147009893 := by
  apply lucas_primality 147009893 (2 : ZMod 147009893)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (911, 1), (40343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (911, 1), (40343, 1)] : List FactorBlock).map factorBlockValue).prod) = 147009893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_911
      · exact prime_oneHundredSixtyFourFF_40343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 147009893) ^ 73504946 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 147009893) ^ 161372 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 147009893) ^ 3644 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_161173237 : Nat.Prime 161173237 := by
  apply lucas_primality 161173237 (5 : ZMod 161173237)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (23, 1), (83423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (23, 1), (83423, 1)] : List FactorBlock).map factorBlockValue).prod) = 161173237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_23
      · exact prime_oneHundredSixtyFourFF_83423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 161173237) ^ 80586618 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 161173237) ^ 53724412 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 161173237) ^ 23024748 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 161173237) ^ 7007532 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 161173237) ^ 1932 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_194763479 : Nat.Prime 194763479 := by
  apply lucas_primality 194763479 (7 : ZMod 194763479)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (29, 1), (36901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (29, 1), (36901, 1)] : List FactorBlock).map factorBlockValue).prod) = 194763479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_13
      · exact prime_oneHundredSixtyFourFF_29
      · exact prime_oneHundredSixtyFourFF_36901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 194763479) ^ 97381739 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 194763479) ^ 27823354 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 194763479) ^ 14981806 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 194763479) ^ 6715982 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 194763479) ^ 5278 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_197014063 : Nat.Prime 197014063 := by
  apply lucas_primality 197014063 (3 : ZMod 197014063)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (4690811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (4690811, 1)] : List FactorBlock).map factorBlockValue).prod) = 197014063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_4690811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 197014063) ^ 98507031 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 197014063) ^ 65671354 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 197014063) ^ 28144866 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 197014063) ^ 42 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_220348273 : Nat.Prime 220348273 := by
  apply lucas_primality 220348273 (5 : ZMod 220348273)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (389, 1), (11801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (389, 1), (11801, 1)] : List FactorBlock).map factorBlockValue).prod) = 220348273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_389
      · exact prime_oneHundredSixtyFourFF_11801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 220348273) ^ 110174136 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 220348273) ^ 73449424 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 220348273) ^ 566448 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 220348273) ^ 18672 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_229043197 : Nat.Prime 229043197 := by
  apply lucas_primality 229043197 (2 : ZMod 229043197)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (6362311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (6362311, 1)] : List FactorBlock).map factorBlockValue).prod) = 229043197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_6362311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 229043197) ^ 114521598 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 229043197) ^ 76347732 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 229043197) ^ 36 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_230268887 : Nat.Prime 230268887 := by
  apply lucas_primality 230268887 (5 : ZMod 230268887)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (1223, 1), (2003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (1223, 1), (2003, 1)] : List FactorBlock).map factorBlockValue).prod) = 230268887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_47
      · exact prime_oneHundredSixtyFourFF_1223
      · exact prime_oneHundredSixtyFourFF_2003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 230268887) ^ 115134443 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 230268887) ^ 4899338 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 230268887) ^ 188282 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 230268887) ^ 114962 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_237754967 : Nat.Prime 237754967 := by
  apply lucas_primality 237754967 (5 : ZMod 237754967)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (197, 1), (491, 1), (1229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (197, 1), (491, 1), (1229, 1)] : List FactorBlock).map factorBlockValue).prod) = 237754967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_197
      · exact prime_oneHundredSixtyFourFF_491
      · exact prime_oneHundredSixtyFourFF_1229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 237754967) ^ 118877483 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 237754967) ^ 1206878 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 237754967) ^ 484226 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 237754967) ^ 193454 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_261919789 : Nat.Prime 261919789 := by
  apply lucas_primality 261919789 (10 : ZMod 261919789)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (19, 1), (97, 1), (911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (19, 1), (97, 1), (911, 1)] : List FactorBlock).map factorBlockValue).prod) = 261919789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_13
      · exact prime_oneHundredSixtyFourFF_19
      · exact prime_oneHundredSixtyFourFF_97
      · exact prime_oneHundredSixtyFourFF_911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 261919789) ^ 130959894 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (10 : ZMod 261919789) ^ 87306596 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (10 : ZMod 261919789) ^ 20147676 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (10 : ZMod 261919789) ^ 13785252 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (10 : ZMod 261919789) ^ 2700204 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (10 : ZMod 261919789) ^ 287508 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_269549981 : Nat.Prime 269549981 := by
  apply lucas_primality 269549981 (2 : ZMod 269549981)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 3), (39293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 3), (39293, 1)] : List FactorBlock).map factorBlockValue).prod) = 269549981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_39293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 269549981) ^ 134774990 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 269549981) ^ 53909996 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 269549981) ^ 38507140 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 269549981) ^ 6860 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_287180123 : Nat.Prime 287180123 := by
  apply lucas_primality 287180123 (2 : ZMod 287180123)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (143590061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (143590061, 1)] : List FactorBlock).map factorBlockValue).prod) = 287180123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_143590061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 287180123) ^ 143590061 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 287180123) ^ 2 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_291155483 : Nat.Prime 291155483 := by
  apply lucas_primality 291155483 (2 : ZMod 291155483)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (151, 1), (167, 1), (251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (151, 1), (167, 1), (251, 1)] : List FactorBlock).map factorBlockValue).prod) = 291155483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_23
      · exact prime_oneHundredSixtyFourFF_151
      · exact prime_oneHundredSixtyFourFF_167
      · exact prime_oneHundredSixtyFourFF_251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 291155483) ^ 145577741 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 291155483) ^ 12658934 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 291155483) ^ 1928182 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 291155483) ^ 1743446 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 291155483) ^ 1159982 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_300416419 : Nat.Prime 300416419 := by
  apply lucas_primality 300416419 (7 : ZMod 300416419)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (17, 1), (327251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (17, 1), (327251, 1)] : List FactorBlock).map factorBlockValue).prod) = 300416419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_17
      · exact prime_oneHundredSixtyFourFF_327251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 300416419) ^ 150208209 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 300416419) ^ 100138806 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 300416419) ^ 17671554 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 300416419) ^ 918 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_309250261 : Nat.Prime 309250261 := by
  apply lucas_primality 309250261 (17 : ZMod 309250261)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (11, 1), (313, 1), (499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (11, 1), (313, 1), (499, 1)] : List FactorBlock).map factorBlockValue).prod) = 309250261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_11
      · exact prime_oneHundredSixtyFourFF_313
      · exact prime_oneHundredSixtyFourFF_499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 309250261) ^ 154625130 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (17 : ZMod 309250261) ^ 103083420 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (17 : ZMod 309250261) ^ 61850052 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (17 : ZMod 309250261) ^ 28113660 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (17 : ZMod 309250261) ^ 988020 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (17 : ZMod 309250261) ^ 619740 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_325921333 : Nat.Prime 325921333 := by
  apply lucas_primality 325921333 (5 : ZMod 325921333)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (233, 1), (10597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (233, 1), (10597, 1)] : List FactorBlock).map factorBlockValue).prod) = 325921333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_11
      · exact prime_oneHundredSixtyFourFF_233
      · exact prime_oneHundredSixtyFourFF_10597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 325921333) ^ 162960666 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 325921333) ^ 108640444 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 325921333) ^ 29629212 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 325921333) ^ 1398804 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 325921333) ^ 30756 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_362257453 : Nat.Prime 362257453 := by
  apply lucas_primality 362257453 (5 : ZMod 362257453)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (23, 1), (437509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (23, 1), (437509, 1)] : List FactorBlock).map factorBlockValue).prod) = 362257453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_23
      · exact prime_oneHundredSixtyFourFF_437509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 362257453) ^ 181128726 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 362257453) ^ 120752484 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 362257453) ^ 15750324 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 362257453) ^ 828 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_362420183 : Nat.Prime 362420183 := by
  apply lucas_primality 362420183 (5 : ZMod 362420183)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (953, 1), (190147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (953, 1), (190147, 1)] : List FactorBlock).map factorBlockValue).prod) = 362420183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_953
      · exact prime_oneHundredSixtyFourFF_190147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 362420183) ^ 181210091 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 362420183) ^ 380294 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 362420183) ^ 1906 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_368081293 : Nat.Prime 368081293 := by
  apply lucas_primality 368081293 (7 : ZMod 368081293)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3593, 1), (8537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3593, 1), (8537, 1)] : List FactorBlock).map factorBlockValue).prod) = 368081293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_3593
      · exact prime_oneHundredSixtyFourFF_8537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 368081293) ^ 184040646 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 368081293) ^ 122693764 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 368081293) ^ 102444 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 368081293) ^ 43116 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_370122169 : Nat.Prime 370122169 := by
  apply lucas_primality 370122169 (11 : ZMod 370122169)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 2), (91253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 2), (91253, 1)] : List FactorBlock).map factorBlockValue).prod) = 370122169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_13
      · exact prime_oneHundredSixtyFourFF_91253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 370122169) ^ 185061084 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 370122169) ^ 123374056 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 370122169) ^ 28470936 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 370122169) ^ 4056 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_371838361 : Nat.Prime 371838361 := by
  apply lucas_primality 371838361 (21 : ZMod 371838361)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (19, 1), (71, 1), (2297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (19, 1), (71, 1), (2297, 1)] : List FactorBlock).map factorBlockValue).prod) = 371838361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_19
      · exact prime_oneHundredSixtyFourFF_71
      · exact prime_oneHundredSixtyFourFF_2297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (21 : ZMod 371838361) ^ 185919180 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (21 : ZMod 371838361) ^ 123946120 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (21 : ZMod 371838361) ^ 74367672 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (21 : ZMod 371838361) ^ 19570440 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (21 : ZMod 371838361) ^ 5237160 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (21 : ZMod 371838361) ^ 161880 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_385344647 : Nat.Prime 385344647 := by
  apply lucas_primality 385344647 (5 : ZMod 385344647)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (9551, 1), (20173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (9551, 1), (20173, 1)] : List FactorBlock).map factorBlockValue).prod) = 385344647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_9551
      · exact prime_oneHundredSixtyFourFF_20173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 385344647) ^ 192672323 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 385344647) ^ 40346 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 385344647) ^ 19102 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_435456781 : Nat.Prime 435456781 := by
  apply lucas_primality 435456781 (10 : ZMod 435456781)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (659783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (659783, 1)] : List FactorBlock).map factorBlockValue).prod) = 435456781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_11
      · exact prime_oneHundredSixtyFourFF_659783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 435456781) ^ 217728390 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (10 : ZMod 435456781) ^ 145152260 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (10 : ZMod 435456781) ^ 87091356 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (10 : ZMod 435456781) ^ 39586980 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (10 : ZMod 435456781) ^ 660 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_475876553 : Nat.Prime 475876553 := by
  apply lucas_primality 475876553 (3 : ZMod 475876553)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (4603, 1), (12923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (4603, 1), (12923, 1)] : List FactorBlock).map factorBlockValue).prod) = 475876553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_4603
      · exact prime_oneHundredSixtyFourFF_12923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 475876553) ^ 237938276 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 475876553) ^ 103384 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 475876553) ^ 36824 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_506900707 : Nat.Prime 506900707 := by
  apply lucas_primality 506900707 (3 : ZMod 506900707)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (6498727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (6498727, 1)] : List FactorBlock).map factorBlockValue).prod) = 506900707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_13
      · exact prime_oneHundredSixtyFourFF_6498727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 506900707) ^ 253450353 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 506900707) ^ 168966902 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 506900707) ^ 38992362 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 506900707) ^ 78 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_542515333 : Nat.Prime 542515333 := by
  apply lucas_primality 542515333 (2 : ZMod 542515333)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (139, 1), (325249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (139, 1), (325249, 1)] : List FactorBlock).map factorBlockValue).prod) = 542515333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_139
      · exact prime_oneHundredSixtyFourFF_325249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 542515333) ^ 271257666 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 542515333) ^ 180838444 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 542515333) ^ 3902988 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 542515333) ^ 1668 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_632230331 : Nat.Prime 632230331 := by
  apply lucas_primality 632230331 (2 : ZMod 632230331)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (281, 1), (224993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (281, 1), (224993, 1)] : List FactorBlock).map factorBlockValue).prod) = 632230331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_281
      · exact prime_oneHundredSixtyFourFF_224993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 632230331) ^ 316115165 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 632230331) ^ 126446066 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 632230331) ^ 2249930 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 632230331) ^ 2810 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_636055141 : Nat.Prime 636055141 := by
  apply lucas_primality 636055141 (14 : ZMod 636055141)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (41, 1), (43, 1), (859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (41, 1), (43, 1), (859, 1)] : List FactorBlock).map factorBlockValue).prod) = 636055141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_41
      · exact prime_oneHundredSixtyFourFF_43
      · exact prime_oneHundredSixtyFourFF_859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 636055141) ^ 318027570 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (14 : ZMod 636055141) ^ 212018380 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (14 : ZMod 636055141) ^ 127211028 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (14 : ZMod 636055141) ^ 90865020 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (14 : ZMod 636055141) ^ 15513540 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (14 : ZMod 636055141) ^ 14791980 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (14 : ZMod 636055141) ^ 740460 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_658269071 : Nat.Prime 658269071 := by
  apply lucas_primality 658269071 (11 : ZMod 658269071)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (113, 1), (34267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (113, 1), (34267, 1)] : List FactorBlock).map factorBlockValue).prod) = 658269071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_17
      · exact prime_oneHundredSixtyFourFF_113
      · exact prime_oneHundredSixtyFourFF_34267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 658269071) ^ 329134535 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 658269071) ^ 131653814 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 658269071) ^ 38721710 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 658269071) ^ 5825390 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 658269071) ^ 19210 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_661483679 : Nat.Prime 661483679 := by
  apply lucas_primality 661483679 (17 : ZMod 661483679)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (643, 1), (17737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (643, 1), (17737, 1)] : List FactorBlock).map factorBlockValue).prod) = 661483679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_29
      · exact prime_oneHundredSixtyFourFF_643
      · exact prime_oneHundredSixtyFourFF_17737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 661483679) ^ 330741839 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (17 : ZMod 661483679) ^ 22809782 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (17 : ZMod 661483679) ^ 1028746 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (17 : ZMod 661483679) ^ 37294 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_17203
      · exact prime_oneHundredSixtyFourFF_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_821234273 : Nat.Prime 821234273 := by
  apply lucas_primality 821234273 (3 : ZMod 821234273)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (887, 1), (28933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (887, 1), (28933, 1)] : List FactorBlock).map factorBlockValue).prod) = 821234273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_887
      · exact prime_oneHundredSixtyFourFF_28933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 821234273) ^ 410617136 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 821234273) ^ 925856 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 821234273) ^ 28384 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_983925587 : Nat.Prime 983925587 := by
  apply lucas_primality 983925587 (2 : ZMod 983925587)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (10040057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (10040057, 1)] : List FactorBlock).map factorBlockValue).prod) = 983925587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_10040057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 983925587) ^ 491962793 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 983925587) ^ 140560798 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 983925587) ^ 98 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_1016457397 : Nat.Prime 1016457397 := by
  apply lucas_primality 1016457397 (2 : ZMod 1016457397)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (61, 1), (1388603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (61, 1), (1388603, 1)] : List FactorBlock).map factorBlockValue).prod) = 1016457397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_61
      · exact prime_oneHundredSixtyFourFF_1388603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1016457397) ^ 508228698 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1016457397) ^ 338819132 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1016457397) ^ 16663236 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1016457397) ^ 732 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_1064016167 : Nat.Prime 1064016167 := by
  apply lucas_primality 1064016167 (5 : ZMod 1064016167)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (337, 1), (36713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (337, 1), (36713, 1)] : List FactorBlock).map factorBlockValue).prod) = 1064016167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_43
      · exact prime_oneHundredSixtyFourFF_337
      · exact prime_oneHundredSixtyFourFF_36713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1064016167) ^ 532008083 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1064016167) ^ 24744562 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1064016167) ^ 3157318 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1064016167) ^ 28982 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_1106962873 : Nat.Prime 1106962873 := by
  apply lucas_primality 1106962873 (5 : ZMod 1106962873)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2683, 1), (17191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2683, 1), (17191, 1)] : List FactorBlock).map factorBlockValue).prod) = 1106962873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_2683
      · exact prime_oneHundredSixtyFourFF_17191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1106962873) ^ 553481436 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1106962873) ^ 368987624 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1106962873) ^ 412584 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1106962873) ^ 64392 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_1149081121 : Nat.Prime 1149081121 := by
  apply lucas_primality 1149081121 (7 : ZMod 1149081121)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 1), (11, 1), (24181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 1), (11, 1), (24181, 1)] : List FactorBlock).map factorBlockValue).prod) = 1149081121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_11
      · exact prime_oneHundredSixtyFourFF_24181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1149081121) ^ 574540560 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1149081121) ^ 383027040 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1149081121) ^ 229816224 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1149081121) ^ 104461920 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1149081121) ^ 47520 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_1176020819 : Nat.Prime 1176020819 := by
  apply lucas_primality 1176020819 (2 : ZMod 1176020819)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (29, 1), (683, 1), (4241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (29, 1), (683, 1), (4241, 1)] : List FactorBlock).map factorBlockValue).prod) = 1176020819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_29
      · exact prime_oneHundredSixtyFourFF_683
      · exact prime_oneHundredSixtyFourFF_4241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1176020819) ^ 588010409 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1176020819) ^ 168002974 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1176020819) ^ 40552442 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1176020819) ^ 1721846 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1176020819) ^ 277298 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_1206642293 : Nat.Prime 1206642293 := by
  apply lucas_primality 1206642293 (2 : ZMod 1206642293)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (181, 1), (1103, 1), (1511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (181, 1), (1103, 1), (1511, 1)] : List FactorBlock).map factorBlockValue).prod) = 1206642293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_181
      · exact prime_oneHundredSixtyFourFF_1103
      · exact prime_oneHundredSixtyFourFF_1511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1206642293) ^ 603321146 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1206642293) ^ 6666532 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1206642293) ^ 1093964 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1206642293) ^ 798572 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_1309677463 : Nat.Prime 1309677463 := by
  apply lucas_primality 1309677463 (3 : ZMod 1309677463)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (72759859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (72759859, 1)] : List FactorBlock).map factorBlockValue).prod) = 1309677463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_72759859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1309677463) ^ 654838731 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1309677463) ^ 436559154 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1309677463) ^ 18 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_1461468469 : Nat.Prime 1461468469 := by
  apply lucas_primality 1461468469 (2 : ZMod 1461468469)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (59, 1), (73, 1), (28277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (59, 1), (73, 1), (28277, 1)] : List FactorBlock).map factorBlockValue).prod) = 1461468469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_59
      · exact prime_oneHundredSixtyFourFF_73
      · exact prime_oneHundredSixtyFourFF_28277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1461468469) ^ 730734234 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1461468469) ^ 487156156 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1461468469) ^ 24770652 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1461468469) ^ 20020116 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1461468469) ^ 51684 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_1463747281 : Nat.Prime 1463747281 := by
  apply lucas_primality 1463747281 (7 : ZMod 1463747281)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (6098947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (6098947, 1)] : List FactorBlock).map factorBlockValue).prod) = 1463747281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_6098947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1463747281) ^ 731873640 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1463747281) ^ 487915760 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1463747281) ^ 292749456 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1463747281) ^ 240 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_1531429793 : Nat.Prime 1531429793 := by
  apply lucas_primality 1531429793 (3 : ZMod 1531429793)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (19, 1), (23, 1), (97, 1), (1129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (19, 1), (23, 1), (97, 1), (1129, 1)] : List FactorBlock).map factorBlockValue).prod) = 1531429793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_19
      · exact prime_oneHundredSixtyFourFF_23
      · exact prime_oneHundredSixtyFourFF_97
      · exact prime_oneHundredSixtyFourFF_1129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1531429793) ^ 765714896 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1531429793) ^ 80601568 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1531429793) ^ 66583904 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1531429793) ^ 15787936 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1531429793) ^ 1356448 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_1597025669 : Nat.Prime 1597025669 := by
  apply lucas_primality 1597025669 (2 : ZMod 1597025669)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (67, 1), (851293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (67, 1), (851293, 1)] : List FactorBlock).map factorBlockValue).prod) = 1597025669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_67
      · exact prime_oneHundredSixtyFourFF_851293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1597025669) ^ 798512834 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1597025669) ^ 228146524 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1597025669) ^ 23836204 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1597025669) ^ 1876 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_1651351319 : Nat.Prime 1651351319 := by
  apply lucas_primality 1651351319 (7 : ZMod 1651351319)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (197, 1), (907, 1), (4621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (197, 1), (907, 1), (4621, 1)] : List FactorBlock).map factorBlockValue).prod) = 1651351319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_197
      · exact prime_oneHundredSixtyFourFF_907
      · exact prime_oneHundredSixtyFourFF_4621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1651351319) ^ 825675659 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1651351319) ^ 8382494 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1651351319) ^ 1820674 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1651351319) ^ 357358 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_1694450239 : Nat.Prime 1694450239 := by
  apply lucas_primality 1694450239 (6 : ZMod 1694450239)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (21723721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (21723721, 1)] : List FactorBlock).map factorBlockValue).prod) = 1694450239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_13
      · exact prime_oneHundredSixtyFourFF_21723721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1694450239) ^ 847225119 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1694450239) ^ 564816746 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1694450239) ^ 130342326 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1694450239) ^ 78 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_1736680111 : Nat.Prime 1736680111 := by
  apply lucas_primality 1736680111 (6 : ZMod 1736680111)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (5262667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (5262667, 1)] : List FactorBlock).map factorBlockValue).prod) = 1736680111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_11
      · exact prime_oneHundredSixtyFourFF_5262667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1736680111) ^ 868340055 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1736680111) ^ 578893370 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1736680111) ^ 347336022 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1736680111) ^ 157880010 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1736680111) ^ 330 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_2128604351 : Nat.Prime 2128604351 := by
  apply lucas_primality 2128604351 (11 : ZMod 2128604351)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (29, 1), (1063, 1), (1381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (29, 1), (1063, 1), (1381, 1)] : List FactorBlock).map factorBlockValue).prod) = 2128604351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_29
      · exact prime_oneHundredSixtyFourFF_1063
      · exact prime_oneHundredSixtyFourFF_1381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2128604351) ^ 1064302175 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 2128604351) ^ 425720870 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 2128604351) ^ 73400150 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 2128604351) ^ 2002450 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 2128604351) ^ 1541350 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_2174521099 : Nat.Prime 2174521099 := by
  apply lucas_primality 2174521099 (3 : ZMod 2174521099)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (362420183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (362420183, 1)] : List FactorBlock).map factorBlockValue).prod) = 2174521099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_362420183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2174521099) ^ 1087260549 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2174521099) ^ 724840366 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2174521099) ^ 6 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_2208487759 : Nat.Prime 2208487759 := by
  apply lucas_primality 2208487759 (3 : ZMod 2208487759)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (368081293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (368081293, 1)] : List FactorBlock).map factorBlockValue).prod) = 2208487759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_368081293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2208487759) ^ 1104243879 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2208487759) ^ 736162586 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2208487759) ^ 6 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_2259666419 : Nat.Prime 2259666419 := by
  apply lucas_primality 2259666419 (2 : ZMod 2259666419)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (23, 1), (2889599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (23, 1), (2889599, 1)] : List FactorBlock).map factorBlockValue).prod) = 2259666419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_17
      · exact prime_oneHundredSixtyFourFF_23
      · exact prime_oneHundredSixtyFourFF_2889599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2259666419) ^ 1129833209 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2259666419) ^ 132921554 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2259666419) ^ 98246366 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2259666419) ^ 782 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_2352041639 : Nat.Prime 2352041639 := by
  apply lucas_primality 2352041639 (19 : ZMod 2352041639)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1176020819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1176020819, 1)] : List FactorBlock).map factorBlockValue).prod) = 2352041639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_1176020819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (19 : ZMod 2352041639) ^ 1176020819 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (19 : ZMod 2352041639) ^ 2 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_2385340501 : Nat.Prime 2385340501 := by
  apply lucas_primality 2385340501 (7 : ZMod 2385340501)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 3), (59, 1), (26953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 3), (59, 1), (26953, 1)] : List FactorBlock).map factorBlockValue).prod) = 2385340501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_59
      · exact prime_oneHundredSixtyFourFF_26953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2385340501) ^ 1192670250 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 2385340501) ^ 795113500 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 2385340501) ^ 477068100 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 2385340501) ^ 40429500 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 2385340501) ^ 88500 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_2416168199 : Nat.Prime 2416168199 := by
  apply lucas_primality 2416168199 (7 : ZMod 2416168199)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (71, 1), (362027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (71, 1), (362027, 1)] : List FactorBlock).map factorBlockValue).prod) = 2416168199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_47
      · exact prime_oneHundredSixtyFourFF_71
      · exact prime_oneHundredSixtyFourFF_362027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2416168199) ^ 1208084099 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 51407834 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 34030538 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 6674 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_2842734247 : Nat.Prime 2842734247 := by
  apply lucas_primality 2842734247 (3 : ZMod 2842734247)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (43071731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (43071731, 1)] : List FactorBlock).map factorBlockValue).prod) = 2842734247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_11
      · exact prime_oneHundredSixtyFourFF_43071731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2842734247) ^ 1421367123 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2842734247) ^ 947578082 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2842734247) ^ 258430386 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2842734247) ^ 66 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_3082757177 : Nat.Prime 3082757177 := by
  apply lucas_primality 3082757177 (3 : ZMod 3082757177)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (385344647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (385344647, 1)] : List FactorBlock).map factorBlockValue).prod) = 3082757177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_385344647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 3082757177) ^ 1541378588 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3082757177) ^ 8 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_3194051339 : Nat.Prime 3194051339 := by
  apply lucas_primality 3194051339 (2 : ZMod 3194051339)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1597025669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1597025669, 1)] : List FactorBlock).map factorBlockValue).prod) = 3194051339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_1597025669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 3194051339) ^ 1597025669 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3194051339) ^ 2 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_3503121703 : Nat.Prime 3503121703 := by
  apply lucas_primality 3503121703 (3 : ZMod 3503121703)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (89, 1), (349, 1), (18797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (89, 1), (349, 1), (18797, 1)] : List FactorBlock).map factorBlockValue).prod) = 3503121703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_89
      · exact prime_oneHundredSixtyFourFF_349
      · exact prime_oneHundredSixtyFourFF_18797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3503121703) ^ 1751560851 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3503121703) ^ 1167707234 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3503121703) ^ 39360918 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3503121703) ^ 10037598 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3503121703) ^ 186366 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_3579204791 : Nat.Prime 3579204791 := by
  apply lucas_primality 3579204791 (7 : ZMod 3579204791)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (51131497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (51131497, 1)] : List FactorBlock).map factorBlockValue).prod) = 3579204791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_51131497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 3579204791) ^ 1789602395 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 3579204791) ^ 715840958 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 3579204791) ^ 511314970 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 3579204791) ^ 70 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_4046689961 : Nat.Prime 4046689961 := by
  apply lucas_primality 4046689961 (7 : ZMod 4046689961)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (4517, 1), (22397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (4517, 1), (22397, 1)] : List FactorBlock).map factorBlockValue).prod) = 4046689961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_4517
      · exact prime_oneHundredSixtyFourFF_22397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 4046689961) ^ 2023344980 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 4046689961) ^ 809337992 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 4046689961) ^ 895880 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 4046689961) ^ 180680 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_4165516939 : Nat.Prime 4165516939 := by
  apply lucas_primality 4165516939 (2 : ZMod 4165516939)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (59, 1), (1069727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (59, 1), (1069727, 1)] : List FactorBlock).map factorBlockValue).prod) = 4165516939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_11
      · exact prime_oneHundredSixtyFourFF_59
      · exact prime_oneHundredSixtyFourFF_1069727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4165516939) ^ 2082758469 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4165516939) ^ 1388505646 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4165516939) ^ 378683358 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4165516939) ^ 70601982 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4165516939) ^ 3894 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_4557625129 : Nat.Prime 4557625129 := by
  apply lucas_primality 4557625129 (13 : ZMod 4557625129)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (9042907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (9042907, 1)] : List FactorBlock).map factorBlockValue).prod) = 4557625129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_9042907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 4557625129) ^ 2278812564 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (13 : ZMod 4557625129) ^ 1519208376 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (13 : ZMod 4557625129) ^ 651089304 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (13 : ZMod 4557625129) ^ 504 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_5858781301 : Nat.Prime 5858781301 := by
  apply lucas_primality 5858781301 (11 : ZMod 5858781301)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 2), (653, 1), (3323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 2), (653, 1), (3323, 1)] : List FactorBlock).map factorBlockValue).prod) = 5858781301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_653
      · exact prime_oneHundredSixtyFourFF_3323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 5858781301) ^ 2929390650 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 5858781301) ^ 1952927100 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 5858781301) ^ 1171756260 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 5858781301) ^ 8972100 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 5858781301) ^ 1763100 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_31
      · exact prime_oneHundredSixtyFourFF_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_7446463909 : Nat.Prime 7446463909 := by
  apply lucas_primality 7446463909 (7 : ZMod 7446463909)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (47733743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (47733743, 1)] : List FactorBlock).map factorBlockValue).prod) = 7446463909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_13
      · exact prime_oneHundredSixtyFourFF_47733743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 7446463909) ^ 3723231954 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 7446463909) ^ 2482154636 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 7446463909) ^ 572804916 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 7446463909) ^ 156 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_7466683199 : Nat.Prime 7466683199 := by
  apply lucas_primality 7466683199 (19 : ZMod 7466683199)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (287180123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (287180123, 1)] : List FactorBlock).map factorBlockValue).prod) = 7466683199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_13
      · exact prime_oneHundredSixtyFourFF_287180123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (19 : ZMod 7466683199) ^ 3733341599 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (19 : ZMod 7466683199) ^ 574360246 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (19 : ZMod 7466683199) ^ 26 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_8813930921 : Nat.Prime 8813930921 := by
  apply lucas_primality 8813930921 (6 : ZMod 8813930921)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (220348273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (220348273, 1)] : List FactorBlock).map factorBlockValue).prod) = 8813930921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_220348273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 8813930921) ^ 4406965460 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 8813930921) ^ 1762786184 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 8813930921) ^ 40 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_10360477973 : Nat.Prime 10360477973 := by
  apply lucas_primality 10360477973 (2 : ZMod 10360477973)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (23, 1), (269, 1), (32203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (23, 1), (269, 1), (32203, 1)] : List FactorBlock).map factorBlockValue).prod) = 10360477973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_13
      · exact prime_oneHundredSixtyFourFF_23
      · exact prime_oneHundredSixtyFourFF_269
      · exact prime_oneHundredSixtyFourFF_32203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10360477973) ^ 5180238986 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 10360477973) ^ 796959844 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 10360477973) ^ 450455564 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 10360477973) ^ 38514788 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 10360477973) ^ 321724 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_12420845651 : Nat.Prime 12420845651 := by
  apply lucas_primality 12420845651 (2 : ZMod 12420845651)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (263, 1), (944551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (263, 1), (944551, 1)] : List FactorBlock).map factorBlockValue).prod) = 12420845651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_263
      · exact prime_oneHundredSixtyFourFF_944551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 12420845651) ^ 6210422825 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 12420845651) ^ 2484169130 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 12420845651) ^ 47227550 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 12420845651) ^ 13150 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_13644685697 : Nat.Prime 13644685697 := by
  apply lucas_primality 13644685697 (3 : ZMod 13644685697)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (43, 1), (2479049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (43, 1), (2479049, 1)] : List FactorBlock).map factorBlockValue).prod) = 13644685697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_43
      · exact prime_oneHundredSixtyFourFF_2479049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 13644685697) ^ 6822342848 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 13644685697) ^ 317318272 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 13644685697) ^ 5504 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_14399904703 : Nat.Prime 14399904703 := by
  apply lucas_primality 14399904703 (3 : ZMod 14399904703)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (82758073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (82758073, 1)] : List FactorBlock).map factorBlockValue).prod) = 14399904703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_29
      · exact prime_oneHundredSixtyFourFF_82758073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 14399904703) ^ 7199952351 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 14399904703) ^ 4799968234 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 14399904703) ^ 496548438 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 14399904703) ^ 174 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_17867268467 : Nat.Prime 17867268467 := by
  apply lucas_primality 17867268467 (2 : ZMod 17867268467)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (137, 1), (263, 1), (247943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (137, 1), (263, 1), (247943, 1)] : List FactorBlock).map factorBlockValue).prod) = 17867268467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_137
      · exact prime_oneHundredSixtyFourFF_263
      · exact prime_oneHundredSixtyFourFF_247943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17867268467) ^ 8933634233 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 17867268467) ^ 130418018 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 17867268467) ^ 67936382 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 17867268467) ^ 72062 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_18230500517 : Nat.Prime 18230500517 := by
  apply lucas_primality 18230500517 (2 : ZMod 18230500517)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4557625129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4557625129, 1)] : List FactorBlock).map factorBlockValue).prod) = 18230500517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_4557625129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 18230500517) ^ 9115250258 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 18230500517) ^ 4 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_18435482759 : Nat.Prime 18435482759 := by
  apply lucas_primality 18435482759 (7 : ZMod 18435482759)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (11, 1), (29, 1), (47, 1), (12547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (11, 1), (29, 1), (47, 1), (12547, 1)] : List FactorBlock).map factorBlockValue).prod) = 18435482759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_11
      · exact prime_oneHundredSixtyFourFF_29
      · exact prime_oneHundredSixtyFourFF_47
      · exact prime_oneHundredSixtyFourFF_12547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 18435482759) ^ 9217741379 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 18435482759) ^ 2633640394 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 18435482759) ^ 1675952978 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 18435482759) ^ 635706302 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 18435482759) ^ 392244314 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 18435482759) ^ 1469314 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_19563937889 : Nat.Prime 19563937889 := by
  apply lucas_primality 19563937889 (3 : ZMod 19563937889)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 1), (1669, 1), (33301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 1), (1669, 1), (33301, 1)] : List FactorBlock).map factorBlockValue).prod) = 19563937889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_11
      · exact prime_oneHundredSixtyFourFF_1669
      · exact prime_oneHundredSixtyFourFF_33301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 19563937889) ^ 9781968944 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 19563937889) ^ 1778539808 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 19563937889) ^ 11721952 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 19563937889) ^ 587488 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_21458947231 : Nat.Prime 21458947231 := by
  apply lucas_primality 21458947231 (12 : ZMod 21458947231)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (59, 1), (167, 1), (3457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (59, 1), (167, 1), (3457, 1)] : List FactorBlock).map factorBlockValue).prod) = 21458947231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_59
      · exact prime_oneHundredSixtyFourFF_167
      · exact prime_oneHundredSixtyFourFF_3457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 21458947231) ^ 10729473615 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (12 : ZMod 21458947231) ^ 7152982410 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (12 : ZMod 21458947231) ^ 4291789446 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (12 : ZMod 21458947231) ^ 3065563890 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (12 : ZMod 21458947231) ^ 363710970 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (12 : ZMod 21458947231) ^ 128496690 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (12 : ZMod 21458947231) ^ 6207390 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_22020007241 : Nat.Prime 22020007241 := by
  apply lucas_primality 22020007241 (3 : ZMod 22020007241)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (11, 1), (7149353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (11, 1), (7149353, 1)] : List FactorBlock).map factorBlockValue).prod) = 22020007241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_11
      · exact prime_oneHundredSixtyFourFF_7149353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 22020007241) ^ 11010003620 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 22020007241) ^ 4404001448 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 22020007241) ^ 3145715320 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 22020007241) ^ 2001818840 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 22020007241) ^ 3080 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_22363884461 : Nat.Prime 22363884461 := by
  apply lucas_primality 22363884461 (2 : ZMod 22363884461)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (757, 1), (1477139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (757, 1), (1477139, 1)] : List FactorBlock).map factorBlockValue).prod) = 22363884461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_757
      · exact prime_oneHundredSixtyFourFF_1477139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 22363884461) ^ 11181942230 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 22363884461) ^ 4472776892 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 22363884461) ^ 29542780 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 22363884461) ^ 15140 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_22696936027 : Nat.Prime 22696936027 := by
  apply lucas_primality 22696936027 (2 : ZMod 22696936027)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (173, 1), (21866027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (173, 1), (21866027, 1)] : List FactorBlock).map factorBlockValue).prod) = 22696936027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_173
      · exact prime_oneHundredSixtyFourFF_21866027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 22696936027) ^ 11348468013 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 22696936027) ^ 7565645342 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 22696936027) ^ 131196162 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 22696936027) ^ 1038 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_22772312639 : Nat.Prime 22772312639 := by
  apply lucas_primality 22772312639 (13 : ZMod 22772312639)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (79, 1), (677, 1), (4951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (79, 1), (677, 1), (4951, 1)] : List FactorBlock).map factorBlockValue).prod) = 22772312639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_43
      · exact prime_oneHundredSixtyFourFF_79
      · exact prime_oneHundredSixtyFourFF_677
      · exact prime_oneHundredSixtyFourFF_4951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 22772312639) ^ 11386156319 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (13 : ZMod 22772312639) ^ 529588666 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (13 : ZMod 22772312639) ^ 288257122 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (13 : ZMod 22772312639) ^ 33637094 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (13 : ZMod 22772312639) ^ 4599538 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_27786881777 : Nat.Prime 27786881777 := by
  apply lucas_primality 27786881777 (3 : ZMod 27786881777)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (1736680111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (1736680111, 1)] : List FactorBlock).map factorBlockValue).prod) = 27786881777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_1736680111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 27786881777) ^ 13893440888 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 27786881777) ^ 16 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_31601290729 : Nat.Prime 31601290729 := by
  apply lucas_primality 31601290729 (11 : ZMod 31601290729)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (4723, 1), (39827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (4723, 1), (39827, 1)] : List FactorBlock).map factorBlockValue).prod) = 31601290729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_4723
      · exact prime_oneHundredSixtyFourFF_39827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 31601290729) ^ 15800645364 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 31601290729) ^ 10533763576 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 31601290729) ^ 4514470104 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 31601290729) ^ 6690936 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 31601290729) ^ 793464 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_31834365877 : Nat.Prime 31834365877 := by
  apply lucas_primality 31834365877 (2 : ZMod 31834365877)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (113, 1), (2608519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (113, 1), (2608519, 1)] : List FactorBlock).map factorBlockValue).prod) = 31834365877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_113
      · exact prime_oneHundredSixtyFourFF_2608519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 31834365877) ^ 15917182938 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 31834365877) ^ 10611455292 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 31834365877) ^ 281720052 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 31834365877) ^ 12204 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_44416591663 : Nat.Prime 44416591663 := by
  apply lucas_primality 44416591663 (11 : ZMod 44416591663)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (435456781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (435456781, 1)] : List FactorBlock).map factorBlockValue).prod) = 44416591663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_17
      · exact prime_oneHundredSixtyFourFF_435456781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 44416591663) ^ 22208295831 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 44416591663) ^ 14805530554 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 44416591663) ^ 2612740686 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 44416591663) ^ 102 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_45368450737 : Nat.Prime 45368450737 := by
  apply lucas_primality 45368450737 (5 : ZMod 45368450737)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (1583, 1), (85297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (1583, 1), (85297, 1)] : List FactorBlock).map factorBlockValue).prod) = 45368450737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_1583
      · exact prime_oneHundredSixtyFourFF_85297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 45368450737) ^ 22684225368 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 45368450737) ^ 15122816912 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 45368450737) ^ 6481207248 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 45368450737) ^ 28659792 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 45368450737) ^ 531888 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_47370820507 : Nat.Prime 47370820507 := by
  apply lucas_primality 47370820507 (2 : ZMod 47370820507)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (47, 1), (4097113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (47, 1), (4097113, 1)] : List FactorBlock).map factorBlockValue).prod) = 47370820507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_41
      · exact prime_oneHundredSixtyFourFF_47
      · exact prime_oneHundredSixtyFourFF_4097113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 47370820507) ^ 23685410253 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 47370820507) ^ 15790273502 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 47370820507) ^ 1155385866 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 47370820507) ^ 1007889798 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 47370820507) ^ 11562 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_48502013269 : Nat.Prime 48502013269 := by
  apply lucas_primality 48502013269 (2 : ZMod 48502013269)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (237754967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (237754967, 1)] : List FactorBlock).map factorBlockValue).prod) = 48502013269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_17
      · exact prime_oneHundredSixtyFourFF_237754967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 48502013269) ^ 24251006634 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 48502013269) ^ 16167337756 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 48502013269) ^ 2853059604 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 48502013269) ^ 204 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_49992525409 : Nat.Prime 49992525409 := by
  apply lucas_primality 49992525409 (11 : ZMod 49992525409)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (41, 1), (251, 1), (7229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (41, 1), (251, 1), (7229, 1)] : List FactorBlock).map factorBlockValue).prod) = 49992525409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_41
      · exact prime_oneHundredSixtyFourFF_251
      · exact prime_oneHundredSixtyFourFF_7229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 49992525409) ^ 24996262704 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 49992525409) ^ 16664175136 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 49992525409) ^ 7141789344 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 49992525409) ^ 1219329888 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 49992525409) ^ 199173408 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 49992525409) ^ 6915552 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_53131981699 : Nat.Prime 53131981699 := by
  apply lucas_primality 53131981699 (2 : ZMod 53131981699)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (983925587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (983925587, 1)] : List FactorBlock).map factorBlockValue).prod) = 53131981699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_983925587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 53131981699) ^ 26565990849 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 53131981699) ^ 17710660566 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 53131981699) ^ 54 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_60093023953 : Nat.Prime 60093023953 := by
  apply lucas_primality 60093023953 (5 : ZMod 60093023953)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (13, 1), (96302923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (13, 1), (96302923, 1)] : List FactorBlock).map factorBlockValue).prod) = 60093023953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_13
      · exact prime_oneHundredSixtyFourFF_96302923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 60093023953) ^ 30046511976 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 60093023953) ^ 20031007984 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 60093023953) ^ 4622540304 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 60093023953) ^ 624 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_60886590773 : Nat.Prime 60886590773 := by
  apply lucas_primality 60886590773 (2 : ZMod 60886590773)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (2174521099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (2174521099, 1)] : List FactorBlock).map factorBlockValue).prod) = 60886590773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_2174521099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 60886590773) ^ 30443295386 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 60886590773) ^ 8698084396 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 60886590773) ^ 28 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_85932246011 : Nat.Prime 85932246011 := by
  apply lucas_primality 85932246011 (2 : ZMod 85932246011)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (19, 1), (1987, 1), (17509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (19, 1), (1987, 1), (17509, 1)] : List FactorBlock).map factorBlockValue).prod) = 85932246011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_13
      · exact prime_oneHundredSixtyFourFF_19
      · exact prime_oneHundredSixtyFourFF_1987
      · exact prime_oneHundredSixtyFourFF_17509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 85932246011) ^ 42966123005 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 85932246011) ^ 17186449202 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 85932246011) ^ 6610172770 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 85932246011) ^ 4522749790 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 85932246011) ^ 43247230 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 85932246011) ^ 4907890 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_90457457939 : Nat.Prime 90457457939 := by
  apply lucas_primality 90457457939 (2 : ZMod 90457457939)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (147557, 1), (306517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (147557, 1), (306517, 1)] : List FactorBlock).map factorBlockValue).prod) = 90457457939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_147557
      · exact prime_oneHundredSixtyFourFF_306517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 90457457939) ^ 45228728969 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 90457457939) ^ 613034 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 90457457939) ^ 295114 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_92028367733 : Nat.Prime 92028367733 := by
  apply lucas_primality 92028367733 (2 : ZMod 92028367733)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (17, 1), (139, 1), (1390913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (17, 1), (139, 1), (1390913, 1)] : List FactorBlock).map factorBlockValue).prod) = 92028367733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_17
      · exact prime_oneHundredSixtyFourFF_139
      · exact prime_oneHundredSixtyFourFF_1390913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 92028367733) ^ 46014183866 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 92028367733) ^ 13146909676 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 92028367733) ^ 5413433396 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 92028367733) ^ 662074588 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 92028367733) ^ 66164 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_99983057029 : Nat.Prime 99983057029 := by
  apply lucas_primality 99983057029 (2 : ZMod 99983057029)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (362257453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (362257453, 1)] : List FactorBlock).map factorBlockValue).prod) = 99983057029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_23
      · exact prime_oneHundredSixtyFourFF_362257453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 99983057029) ^ 49991528514 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 99983057029) ^ 33327685676 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 99983057029) ^ 4347089436 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 99983057029) ^ 276 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_107203610803 : Nat.Prime 107203610803 := by
  apply lucas_primality 107203610803 (2 : ZMod 107203610803)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17867268467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17867268467, 1)] : List FactorBlock).map factorBlockValue).prod) = 107203610803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_17867268467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 107203610803) ^ 53601805401 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 107203610803) ^ 35734536934 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 107203610803) ^ 6 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_134060634143 : Nat.Prime 134060634143 := by
  apply lucas_primality 134060634143 (5 : ZMod 134060634143)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (1327, 1), (856147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (1327, 1), (856147, 1)] : List FactorBlock).map factorBlockValue).prod) = 134060634143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_59
      · exact prime_oneHundredSixtyFourFF_1327
      · exact prime_oneHundredSixtyFourFF_856147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 134060634143) ^ 67030317071 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 134060634143) ^ 2272214138 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 134060634143) ^ 101025346 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 134060634143) ^ 156586 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_149592190823 : Nat.Prime 149592190823 := by
  apply lucas_primality 149592190823 (10 : ZMod 149592190823)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (397, 1), (2811989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (397, 1), (2811989, 1)] : List FactorBlock).map factorBlockValue).prod) = 149592190823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_67
      · exact prime_oneHundredSixtyFourFF_397
      · exact prime_oneHundredSixtyFourFF_2811989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 149592190823) ^ 74796095411 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (10 : ZMod 149592190823) ^ 2232719266 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (10 : ZMod 149592190823) ^ 376806526 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (10 : ZMod 149592190823) ^ 53198 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_173054587543 : Nat.Prime 173054587543 := by
  apply lucas_primality 173054587543 (3 : ZMod 173054587543)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (193, 1), (211, 1), (263, 1), (2693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (193, 1), (211, 1), (263, 1), (2693, 1)] : List FactorBlock).map factorBlockValue).prod) = 173054587543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_193
      · exact prime_oneHundredSixtyFourFF_211
      · exact prime_oneHundredSixtyFourFF_263
      · exact prime_oneHundredSixtyFourFF_2693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 173054587543) ^ 86527293771 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 173054587543) ^ 57684862514 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 173054587543) ^ 896655894 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 173054587543) ^ 820163922 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 173054587543) ^ 658002234 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 173054587543) ^ 64260894 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_211247586061 : Nat.Prime 211247586061 := by
  apply lucas_primality 211247586061 (2 : ZMod 211247586061)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (31, 1), (557, 1), (29129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (31, 1), (557, 1), (29129, 1)] : List FactorBlock).map factorBlockValue).prod) = 211247586061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_31
      · exact prime_oneHundredSixtyFourFF_557
      · exact prime_oneHundredSixtyFourFF_29129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 211247586061) ^ 105623793030 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 211247586061) ^ 70415862020 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 211247586061) ^ 42249517212 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 211247586061) ^ 30178226580 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 211247586061) ^ 6814438260 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 211247586061) ^ 379259580 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 211247586061) ^ 7252140 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_249625314383 : Nat.Prime 249625314383 := by
  apply lucas_primality 249625314383 (5 : ZMod 249625314383)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (211, 1), (14427541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (211, 1), (14427541, 1)] : List FactorBlock).map factorBlockValue).prod) = 249625314383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_41
      · exact prime_oneHundredSixtyFourFF_211
      · exact prime_oneHundredSixtyFourFF_14427541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 249625314383) ^ 124812657191 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 249625314383) ^ 6088422302 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 249625314383) ^ 1183058362 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 249625314383) ^ 17302 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_303985441553 : Nat.Prime 303985441553 := by
  apply lucas_primality 303985441553 (3 : ZMod 303985441553)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (1461468469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (1461468469, 1)] : List FactorBlock).map factorBlockValue).prod) = 303985441553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_13
      · exact prime_oneHundredSixtyFourFF_1461468469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 303985441553) ^ 151992720776 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 303985441553) ^ 23383495504 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 303985441553) ^ 208 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_310945062751 : Nat.Prime 310945062751 := by
  apply lucas_primality 310945062751 (3 : ZMod 310945062751)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (7, 1), (89, 1), (665479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (7, 1), (89, 1), (665479, 1)] : List FactorBlock).map factorBlockValue).prod) = 310945062751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_89
      · exact prime_oneHundredSixtyFourFF_665479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 310945062751) ^ 155472531375 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 310945062751) ^ 103648354250 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 310945062751) ^ 62189012550 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 310945062751) ^ 44420723250 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 310945062751) ^ 3493764750 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 310945062751) ^ 467250 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_312751484179 : Nat.Prime 312751484179 := by
  apply lucas_primality 312751484179 (2 : ZMod 312751484179)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (7446463909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (7446463909, 1)] : List FactorBlock).map factorBlockValue).prod) = 312751484179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_7446463909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 312751484179) ^ 156375742089 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 312751484179) ^ 104250494726 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 312751484179) ^ 44678783454 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 312751484179) ^ 42 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_325925441143 : Nat.Prime 325925441143 := by
  apply lucas_primality 325925441143 (3 : ZMod 325925441143)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (23, 1), (967, 1), (348911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (23, 1), (967, 1), (348911, 1)] : List FactorBlock).map factorBlockValue).prod) = 325925441143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_23
      · exact prime_oneHundredSixtyFourFF_967
      · exact prime_oneHundredSixtyFourFF_348911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 325925441143) ^ 162962720571 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 325925441143) ^ 108641813714 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 325925441143) ^ 46560777306 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 325925441143) ^ 14170671354 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 325925441143) ^ 337048026 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 325925441143) ^ 934122 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_345118424881 : Nat.Prime 345118424881 := by
  apply lucas_primality 345118424881 (7 : ZMod 345118424881)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (107, 1), (13439191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (107, 1), (13439191, 1)] : List FactorBlock).map factorBlockValue).prod) = 345118424881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_107
      · exact prime_oneHundredSixtyFourFF_13439191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 345118424881) ^ 172559212440 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 345118424881) ^ 115039474960 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 345118424881) ^ 69023684976 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 345118424881) ^ 3225405840 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 345118424881) ^ 25680 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_355395970823 : Nat.Prime 355395970823 := by
  apply lucas_primality 355395970823 (5 : ZMod 355395970823)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1031, 1), (5569, 1), (30949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1031, 1), (5569, 1), (30949, 1)] : List FactorBlock).map factorBlockValue).prod) = 355395970823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_1031
      · exact prime_oneHundredSixtyFourFF_5569
      · exact prime_oneHundredSixtyFourFF_30949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 355395970823) ^ 177697985411 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 355395970823) ^ 344709962 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 355395970823) ^ 63816838 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 355395970823) ^ 11483278 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_373829227171 : Nat.Prime 373829227171 := by
  apply lucas_primality 373829227171 (7 : ZMod 373829227171)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (199, 1), (317, 1), (28219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (199, 1), (317, 1), (28219, 1)] : List FactorBlock).map factorBlockValue).prod) = 373829227171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_199
      · exact prime_oneHundredSixtyFourFF_317
      · exact prime_oneHundredSixtyFourFF_28219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 373829227171) ^ 186914613585 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 373829227171) ^ 124609742390 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 373829227171) ^ 74765845434 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 373829227171) ^ 53404175310 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 373829227171) ^ 1878538830 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 373829227171) ^ 1179272010 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 373829227171) ^ 13247430 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_399627019199 : Nat.Prime 399627019199 := by
  apply lucas_primality 399627019199 (7 : ZMod 399627019199)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 2), (1651351319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 2), (1651351319, 1)] : List FactorBlock).map factorBlockValue).prod) = 399627019199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_11
      · exact prime_oneHundredSixtyFourFF_1651351319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 399627019199) ^ 199813509599 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 399627019199) ^ 36329729018 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 399627019199) ^ 242 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_631765699379 : Nat.Prime 631765699379 := by
  apply lucas_primality 631765699379 (2 : ZMod 631765699379)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (23, 2), (54284731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (23, 2), (54284731, 1)] : List FactorBlock).map factorBlockValue).prod) = 631765699379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_11
      · exact prime_oneHundredSixtyFourFF_23
      · exact prime_oneHundredSixtyFourFF_54284731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 631765699379) ^ 315882849689 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 631765699379) ^ 57433245398 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 631765699379) ^ 27468073886 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 631765699379) ^ 11638 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_842955281741 : Nat.Prime 842955281741 := by
  apply lucas_primality 842955281741 (2 : ZMod 842955281741)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (13, 1), (19, 1), (89, 1), (174299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (13, 1), (19, 1), (89, 1), (174299, 1)] : List FactorBlock).map factorBlockValue).prod) = 842955281741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_11
      · exact prime_oneHundredSixtyFourFF_13
      · exact prime_oneHundredSixtyFourFF_19
      · exact prime_oneHundredSixtyFourFF_89
      · exact prime_oneHundredSixtyFourFF_174299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 842955281741) ^ 421477640870 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 842955281741) ^ 168591056348 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 842955281741) ^ 76632298340 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 842955281741) ^ 64842713980 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 842955281741) ^ 44366067460 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 842955281741) ^ 9471407660 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 842955281741) ^ 4836260 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_852412270823 : Nat.Prime 852412270823 := by
  apply lucas_primality 852412270823 (5 : ZMod 852412270823)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (60886590773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (60886590773, 1)] : List FactorBlock).map factorBlockValue).prod) = 852412270823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_60886590773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 852412270823) ^ 426206135411 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 852412270823) ^ 121773181546 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 852412270823) ^ 14 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_914480876299 : Nat.Prime 914480876299 := by
  apply lucas_primality 914480876299 (2 : ZMod 914480876299)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (173, 1), (5779, 1), (13859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (173, 1), (5779, 1), (13859, 1)] : List FactorBlock).map factorBlockValue).prod) = 914480876299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_11
      · exact prime_oneHundredSixtyFourFF_173
      · exact prime_oneHundredSixtyFourFF_5779
      · exact prime_oneHundredSixtyFourFF_13859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 914480876299) ^ 457240438149 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 914480876299) ^ 304826958766 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 914480876299) ^ 83134625118 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 914480876299) ^ 5286016626 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 914480876299) ^ 158242062 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 914480876299) ^ 65984622 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_1038269493017 : Nat.Prime 1038269493017 := by
  apply lucas_primality 1038269493017 (3 : ZMod 1038269493017)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (1759, 1), (10540379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (1759, 1), (10540379, 1)] : List FactorBlock).map factorBlockValue).prod) = 1038269493017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_1759
      · exact prime_oneHundredSixtyFourFF_10540379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1038269493017) ^ 519134746508 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1038269493017) ^ 148324213288 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1038269493017) ^ 590261224 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1038269493017) ^ 98504 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_1062117475429 : Nat.Prime 1062117475429 := by
  apply lucas_primality 1062117475429 (2 : ZMod 1062117475429)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (131, 1), (2909, 1), (8009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (131, 1), (2909, 1), (8009, 1)] : List FactorBlock).map factorBlockValue).prod) = 1062117475429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_29
      · exact prime_oneHundredSixtyFourFF_131
      · exact prime_oneHundredSixtyFourFF_2909
      · exact prime_oneHundredSixtyFourFF_8009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1062117475429) ^ 531058737714 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1062117475429) ^ 354039158476 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1062117475429) ^ 36624740532 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1062117475429) ^ 8107766988 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1062117475429) ^ 365114292 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1062117475429) ^ 132615492 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_1101000362051 : Nat.Prime 1101000362051 := by
  apply lucas_primality 1101000362051 (2 : ZMod 1101000362051)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (22020007241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (22020007241, 1)] : List FactorBlock).map factorBlockValue).prod) = 1101000362051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_22020007241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1101000362051) ^ 550500181025 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1101000362051) ^ 220200072410 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1101000362051) ^ 50 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_1210281000961 : Nat.Prime 1210281000961 := by
  apply lucas_primality 1210281000961 (29 : ZMod 1210281000961)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 15), (3, 1), (5, 1), (1381, 1), (1783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 15), (3, 1), (5, 1), (1381, 1), (1783, 1)] : List FactorBlock).map factorBlockValue).prod) = 1210281000961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_1381
      · exact prime_oneHundredSixtyFourFF_1783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 1210281000961) ^ 605140500480 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (29 : ZMod 1210281000961) ^ 403427000320 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (29 : ZMod 1210281000961) ^ 242056200192 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (29 : ZMod 1210281000961) ^ 876380160 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (29 : ZMod 1210281000961) ^ 678789120 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_1403736441413 : Nat.Prime 1403736441413 := by
  apply lucas_primality 1403736441413 (2 : ZMod 1403736441413)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (7466683199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (7466683199, 1)] : List FactorBlock).map factorBlockValue).prod) = 1403736441413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_47
      · exact prime_oneHundredSixtyFourFF_7466683199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1403736441413) ^ 701868220706 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1403736441413) ^ 29866732796 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1403736441413) ^ 188 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_1450741358743 : Nat.Prime 1450741358743 := by
  apply lucas_primality 1450741358743 (5 : ZMod 1450741358743)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (17971, 1), (1034959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (17971, 1), (1034959, 1)] : List FactorBlock).map factorBlockValue).prod) = 1450741358743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_13
      · exact prime_oneHundredSixtyFourFF_17971
      · exact prime_oneHundredSixtyFourFF_1034959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1450741358743) ^ 725370679371 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1450741358743) ^ 483580452914 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1450741358743) ^ 111595489134 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1450741358743) ^ 80726802 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1450741358743) ^ 1401738 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_1563173487481 : Nat.Prime 1563173487481 := by
  apply lucas_primality 1563173487481 (26 : ZMod 1563173487481)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (11, 1), (733, 1), (1223, 1), (1321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (11, 1), (733, 1), (1223, 1), (1321, 1)] : List FactorBlock).map factorBlockValue).prod) = 1563173487481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_11
      · exact prime_oneHundredSixtyFourFF_733
      · exact prime_oneHundredSixtyFourFF_1223
      · exact prime_oneHundredSixtyFourFF_1321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 1563173487481) ^ 781586743740 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (26 : ZMod 1563173487481) ^ 521057829160 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (26 : ZMod 1563173487481) ^ 312634697496 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (26 : ZMod 1563173487481) ^ 142106680680 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (26 : ZMod 1563173487481) ^ 2132569560 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (26 : ZMod 1563173487481) ^ 1278146760 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (26 : ZMod 1563173487481) ^ 1183325880 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_1673437451123 : Nat.Prime 1673437451123 := by
  apply lucas_primality 1673437451123 (2 : ZMod 1673437451123)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (137, 1), (197014063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (137, 1), (197014063, 1)] : List FactorBlock).map factorBlockValue).prod) = 1673437451123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_31
      · exact prime_oneHundredSixtyFourFF_137
      · exact prime_oneHundredSixtyFourFF_197014063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1673437451123) ^ 836718725561 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1673437451123) ^ 53981853262 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1673437451123) ^ 12214871906 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1673437451123) ^ 8494 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_1983975556951 : Nat.Prime 1983975556951 := by
  apply lucas_primality 1983975556951 (6 : ZMod 1983975556951)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (10499, 1), (419929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (10499, 1), (419929, 1)] : List FactorBlock).map factorBlockValue).prod) = 1983975556951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_10499
      · exact prime_oneHundredSixtyFourFF_419929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1983975556951) ^ 991987778475 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1983975556951) ^ 661325185650 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1983975556951) ^ 396795111390 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1983975556951) ^ 188968050 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1983975556951) ^ 4724550 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_2112475860611 : Nat.Prime 2112475860611 := by
  apply lucas_primality 2112475860611 (2 : ZMod 2112475860611)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (211247586061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (211247586061, 1)] : List FactorBlock).map factorBlockValue).prod) = 2112475860611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_211247586061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2112475860611) ^ 1056237930305 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2112475860611) ^ 422495172122 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2112475860611) ^ 10 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_2131567714711 : Nat.Prime 2131567714711 := by
  apply lucas_primality 2131567714711 (15 : ZMod 2131567714711)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (29, 1), (769, 1), (151717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (29, 1), (769, 1), (151717, 1)] : List FactorBlock).map factorBlockValue).prod) = 2131567714711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_29
      · exact prime_oneHundredSixtyFourFF_769
      · exact prime_oneHundredSixtyFourFF_151717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 2131567714711) ^ 1065783857355 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (15 : ZMod 2131567714711) ^ 710522571570 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (15 : ZMod 2131567714711) ^ 426313542942 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (15 : ZMod 2131567714711) ^ 304509673530 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (15 : ZMod 2131567714711) ^ 73502334990 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (15 : ZMod 2131567714711) ^ 2771869590 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (15 : ZMod 2131567714711) ^ 14049630 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_2426519858207 : Nat.Prime 2426519858207 := by
  apply lucas_primality 2426519858207 (5 : ZMod 2426519858207)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (239, 1), (21817, 1), (232681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (239, 1), (21817, 1), (232681, 1)] : List FactorBlock).map factorBlockValue).prod) = 2426519858207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_239
      · exact prime_oneHundredSixtyFourFF_21817
      · exact prime_oneHundredSixtyFourFF_232681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2426519858207) ^ 1213259929103 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 2426519858207) ^ 10152802754 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 2426519858207) ^ 111221518 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 2426519858207) ^ 10428526 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_3251947489543 : Nat.Prime 3251947489543 := by
  apply lucas_primality 3251947489543 (3 : ZMod 3251947489543)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (109, 1), (10337, 1), (160343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (109, 1), (10337, 1), (160343, 1)] : List FactorBlock).map factorBlockValue).prod) = 3251947489543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_109
      · exact prime_oneHundredSixtyFourFF_10337
      · exact prime_oneHundredSixtyFourFF_160343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3251947489543) ^ 1625973744771 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3251947489543) ^ 1083982496514 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3251947489543) ^ 29834380638 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3251947489543) ^ 314592966 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3251947489543) ^ 20281194 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_3945795860701 : Nat.Prime 3945795860701 := by
  apply lucas_primality 3945795860701 (11 : ZMod 3945795860701)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (929, 1), (4719287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (929, 1), (4719287, 1)] : List FactorBlock).map factorBlockValue).prod) = 3945795860701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_929
      · exact prime_oneHundredSixtyFourFF_4719287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 3945795860701) ^ 1972897930350 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 3945795860701) ^ 1315265286900 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 3945795860701) ^ 789159172140 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 3945795860701) ^ 4247358300 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 3945795860701) ^ 836100 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_4485950726053 : Nat.Prime 4485950726053 := by
  apply lucas_primality 4485950726053 (2 : ZMod 4485950726053)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (373829227171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (373829227171, 1)] : List FactorBlock).map factorBlockValue).prod) = 4485950726053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_373829227171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4485950726053) ^ 2242975363026 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4485950726053) ^ 1495316908684 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4485950726053) ^ 12 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_4944391472773 : Nat.Prime 4944391472773 := by
  apply lucas_primality 4944391472773 (2 : ZMod 4944391472773)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (43, 1), (3194051339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (43, 1), (3194051339, 1)] : List FactorBlock).map factorBlockValue).prod) = 4944391472773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_43
      · exact prime_oneHundredSixtyFourFF_3194051339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4944391472773) ^ 2472195736386 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4944391472773) ^ 1648130490924 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4944391472773) ^ 114985848204 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4944391472773) ^ 1548 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_5056381242277 : Nat.Prime 5056381242277 := by
  apply lucas_primality 5056381242277 (2 : ZMod 5056381242277)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (13, 1), (661483679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (13, 1), (661483679, 1)] : List FactorBlock).map factorBlockValue).prod) = 5056381242277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_13
      · exact prime_oneHundredSixtyFourFF_661483679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5056381242277) ^ 2528190621138 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5056381242277) ^ 1685460414092 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5056381242277) ^ 722340177468 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5056381242277) ^ 388952403252 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5056381242277) ^ 7644 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_7359814694369 : Nat.Prime 7359814694369 := by
  apply lucas_primality 7359814694369 (3 : ZMod 7359814694369)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (1427, 1), (161173237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (1427, 1), (161173237, 1)] : List FactorBlock).map factorBlockValue).prod) = 7359814694369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_1427
      · exact prime_oneHundredSixtyFourFF_161173237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 7359814694369) ^ 3679907347184 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 7359814694369) ^ 5157543584 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 7359814694369) ^ 45664 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_8380211051153 : Nat.Prime 8380211051153 := by
  apply lucas_primality 8380211051153 (3 : ZMod 8380211051153)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (23, 1), (22772312639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (23, 1), (22772312639, 1)] : List FactorBlock).map factorBlockValue).prod) = 8380211051153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_23
      · exact prime_oneHundredSixtyFourFF_22772312639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 8380211051153) ^ 4190105525576 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 8380211051153) ^ 364357002224 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 8380211051153) ^ 368 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_9255115388171 : Nat.Prime 9255115388171 := by
  apply lucas_primality 9255115388171 (2 : ZMod 9255115388171)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (337, 1), (3803, 1), (722147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (337, 1), (3803, 1), (722147, 1)] : List FactorBlock).map factorBlockValue).prod) = 9255115388171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_337
      · exact prime_oneHundredSixtyFourFF_3803
      · exact prime_oneHundredSixtyFourFF_722147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9255115388171) ^ 4627557694085 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 9255115388171) ^ 1851023077634 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 9255115388171) ^ 27463250410 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 9255115388171) ^ 2433635390 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 9255115388171) ^ 12816110 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_10156147401149 : Nat.Prime 10156147401149 := by
  apply lucas_primality 10156147401149 (2 : ZMod 10156147401149)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (8861, 1), (40934381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (8861, 1), (40934381, 1)] : List FactorBlock).map factorBlockValue).prod) = 10156147401149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_8861
      · exact prime_oneHundredSixtyFourFF_40934381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10156147401149) ^ 5078073700574 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 10156147401149) ^ 1450878200164 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 10156147401149) ^ 1146162668 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 10156147401149) ^ 248108 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_13282339919447 : Nat.Prime 13282339919447 := by
  apply lucas_primality 13282339919447 (5 : ZMod 13282339919447)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 2), (271, 1), (145006877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 2), (271, 1), (145006877, 1)] : List FactorBlock).map factorBlockValue).prod) = 13282339919447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_13
      · exact prime_oneHundredSixtyFourFF_271
      · exact prime_oneHundredSixtyFourFF_145006877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 13282339919447) ^ 6641169959723 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 13282339919447) ^ 1021718455342 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 13282339919447) ^ 49012324426 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 13282339919447) ^ 91598 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_15563811684527 : Nat.Prime 15563811684527 := by
  apply lucas_primality 15563811684527 (7 : ZMod 15563811684527)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (47, 1), (139, 1), (7703, 1), (22091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (47, 1), (139, 1), (7703, 1), (22091, 1)] : List FactorBlock).map factorBlockValue).prod) = 15563811684527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_47
      · exact prime_oneHundredSixtyFourFF_139
      · exact prime_oneHundredSixtyFourFF_7703
      · exact prime_oneHundredSixtyFourFF_22091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 15563811684527) ^ 7781905842263 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 15563811684527) ^ 2223401669218 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 15563811684527) ^ 331144929458 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 15563811684527) ^ 111969868234 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 15563811684527) ^ 2020487042 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 15563811684527) ^ 704531786 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_17797584535699 : Nat.Prime 17797584535699 := by
  apply lucas_primality 17797584535699 (3 : ZMod 17797584535699)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (17, 1), (36343, 1), (436463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (17, 1), (36343, 1), (436463, 1)] : List FactorBlock).map factorBlockValue).prod) = 17797584535699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_11
      · exact prime_oneHundredSixtyFourFF_17
      · exact prime_oneHundredSixtyFourFF_36343
      · exact prime_oneHundredSixtyFourFF_436463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 17797584535699) ^ 8898792267849 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 17797584535699) ^ 5932528178566 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 17797584535699) ^ 1617962230518 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 17797584535699) ^ 1046916737394 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 17797584535699) ^ 489711486 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 17797584535699) ^ 40776846 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_21606385793549 : Nat.Prime 21606385793549 := by
  apply lucas_primality 21606385793549 (2 : ZMod 21606385793549)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (293, 1), (18435482759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (293, 1), (18435482759, 1)] : List FactorBlock).map factorBlockValue).prod) = 21606385793549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_293
      · exact prime_oneHundredSixtyFourFF_18435482759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 21606385793549) ^ 10803192896774 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 21606385793549) ^ 73741931036 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 21606385793549) ^ 1172 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_26533200616991 : Nat.Prime 26533200616991 := by
  apply lucas_primality 26533200616991 (23 : ZMod 26533200616991)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (29, 1), (2339, 1), (1700723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (29, 1), (2339, 1), (1700723, 1)] : List FactorBlock).map factorBlockValue).prod) = 26533200616991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_23
      · exact prime_oneHundredSixtyFourFF_29
      · exact prime_oneHundredSixtyFourFF_2339
      · exact prime_oneHundredSixtyFourFF_1700723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 26533200616991) ^ 13266600308495 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (23 : ZMod 26533200616991) ^ 5306640123398 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (23 : ZMod 26533200616991) ^ 1153617418130 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (23 : ZMod 26533200616991) ^ 914937952310 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (23 : ZMod 26533200616991) ^ 11343822410 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (23 : ZMod 26533200616991) ^ 15601130 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_47202337644989 : Nat.Prime 47202337644989 := by
  apply lucas_primality 47202337644989 (2 : ZMod 47202337644989)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (67, 1), (10360477973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (67, 1), (10360477973, 1)] : List FactorBlock).map factorBlockValue).prod) = 47202337644989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_17
      · exact prime_oneHundredSixtyFourFF_67
      · exact prime_oneHundredSixtyFourFF_10360477973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 47202337644989) ^ 23601168822494 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 47202337644989) ^ 2776608096764 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 47202337644989) ^ 704512502164 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 47202337644989) ^ 4556 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_53066401233983 : Nat.Prime 53066401233983 := by
  apply lucas_primality 53066401233983 (5 : ZMod 53066401233983)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (26533200616991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (26533200616991, 1)] : List FactorBlock).map factorBlockValue).prod) = 53066401233983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_26533200616991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 53066401233983) ^ 26533200616991 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 53066401233983) ^ 2 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_57352123987729 : Nat.Prime 57352123987729 := by
  apply lucas_primality 57352123987729 (11 : ZMod 57352123987729)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (43, 1), (27786881777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (43, 1), (27786881777, 1)] : List FactorBlock).map factorBlockValue).prod) = 57352123987729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_43
      · exact prime_oneHundredSixtyFourFF_27786881777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 57352123987729) ^ 28676061993864 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 57352123987729) ^ 19117374662576 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 57352123987729) ^ 1333770325296 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 57352123987729) ^ 2064 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_108159489589871 : Nat.Prime 108159489589871 := by
  apply lucas_primality 108159489589871 (11 : ZMod 108159489589871)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (223, 1), (48502013269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (223, 1), (48502013269, 1)] : List FactorBlock).map factorBlockValue).prod) = 108159489589871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_223
      · exact prime_oneHundredSixtyFourFF_48502013269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 108159489589871) ^ 54079744794935 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 108159489589871) ^ 21631897917974 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 108159489589871) ^ 485020132690 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 108159489589871) ^ 2230 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_109593990089351 : Nat.Prime 109593990089351 := by
  apply lucas_primality 109593990089351 (11 : ZMod 109593990089351)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (13, 1), (61, 1), (45119, 1), (61261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (13, 1), (61, 1), (45119, 1), (61261, 1)] : List FactorBlock).map factorBlockValue).prod) = 109593990089351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_13
      · exact prime_oneHundredSixtyFourFF_61
      · exact prime_oneHundredSixtyFourFF_45119
      · exact prime_oneHundredSixtyFourFF_61261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 109593990089351) ^ 54796995044675 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 109593990089351) ^ 21918798017870 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 109593990089351) ^ 8430306929950 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 109593990089351) ^ 1796622788350 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 109593990089351) ^ 2428998650 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 109593990089351) ^ 1788968350 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_130816944578447 : Nat.Prime 130816944578447 := by
  apply lucas_primality 130816944578447 (5 : ZMod 130816944578447)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (173, 1), (2842734247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (173, 1), (2842734247, 1)] : List FactorBlock).map factorBlockValue).prod) = 130816944578447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_19
      · exact prime_oneHundredSixtyFourFF_173
      · exact prime_oneHundredSixtyFourFF_2842734247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 130816944578447) ^ 65408472289223 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 130816944578447) ^ 18688134939778 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 130816944578447) ^ 6885102346234 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 130816944578447) ^ 756167309702 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 130816944578447) ^ 46018 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_165384514896703 : Nat.Prime 165384514896703 := by
  apply lucas_primality 165384514896703 (3 : ZMod 165384514896703)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (1450741358743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (1450741358743, 1)] : List FactorBlock).map factorBlockValue).prod) = 165384514896703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_19
      · exact prime_oneHundredSixtyFourFF_1450741358743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 165384514896703) ^ 82692257448351 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 165384514896703) ^ 55128171632234 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 165384514896703) ^ 8704448152458 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 165384514896703) ^ 114 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_238162884405553 : Nat.Prime 238162884405553 := by
  apply lucas_primality 238162884405553 (5 : ZMod 238162884405553)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (379, 1), (2803, 1), (518953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (379, 1), (2803, 1), (518953, 1)] : List FactorBlock).map factorBlockValue).prod) = 238162884405553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_379
      · exact prime_oneHundredSixtyFourFF_2803
      · exact prime_oneHundredSixtyFourFF_518953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 238162884405553) ^ 119081442202776 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 238162884405553) ^ 79387628135184 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 238162884405553) ^ 628398111888 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 238162884405553) ^ 84967136784 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 238162884405553) ^ 458929584 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_248859330486707 : Nat.Prime 248859330486707 := by
  apply lucas_primality 248859330486707 (2 : ZMod 248859330486707)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1381, 1), (94439, 1), (954067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1381, 1), (94439, 1), (954067, 1)] : List FactorBlock).map factorBlockValue).prod) = 248859330486707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_1381
      · exact prime_oneHundredSixtyFourFF_94439
      · exact prime_oneHundredSixtyFourFF_954067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 248859330486707) ^ 124429665243353 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 248859330486707) ^ 180202266826 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 248859330486707) ^ 2635133054 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 248859330486707) ^ 260840518 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_258862483991359 : Nat.Prime 258862483991359 := by
  apply lucas_primality 258862483991359 (6 : ZMod 258862483991359)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (10789, 1), (102534983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (10789, 1), (102534983, 1)] : List FactorBlock).map factorBlockValue).prod) = 258862483991359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_13
      · exact prime_oneHundredSixtyFourFF_10789
      · exact prime_oneHundredSixtyFourFF_102534983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 258862483991359) ^ 129431241995679 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 86287494663786 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 19912498768566 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 23993186022 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 2524626 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_355705005018821 : Nat.Prime 355705005018821 := by
  apply lucas_primality 355705005018821 (2 : ZMod 355705005018821)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (4253, 1), (36263, 1), (115319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (4253, 1), (36263, 1), (115319, 1)] : List FactorBlock).map factorBlockValue).prod) = 355705005018821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_4253
      · exact prime_oneHundredSixtyFourFF_36263
      · exact prime_oneHundredSixtyFourFF_115319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 355705005018821) ^ 177852502509410 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 355705005018821) ^ 71141001003764 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 355705005018821) ^ 83636257940 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 355705005018821) ^ 9809034140 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 355705005018821) ^ 3084530780 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_385447666294679 : Nat.Prime 385447666294679 := by
  apply lucas_primality 385447666294679 (7 : ZMod 385447666294679)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 2), (567467, 1), (2009593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 2), (567467, 1), (2009593, 1)] : List FactorBlock).map factorBlockValue).prod) = 385447666294679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_13
      · exact prime_oneHundredSixtyFourFF_567467
      · exact prime_oneHundredSixtyFourFF_2009593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 385447666294679) ^ 192723833147339 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 385447666294679) ^ 29649820484206 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 385447666294679) ^ 679242434 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 385447666294679) ^ 191803846 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_401939904288361 : Nat.Prime 401939904288361 := by
  apply lucas_primality 401939904288361 (17 : ZMod 401939904288361)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (67, 1), (49992525409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (67, 1), (49992525409, 1)] : List FactorBlock).map factorBlockValue).prod) = 401939904288361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_67
      · exact prime_oneHundredSixtyFourFF_49992525409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 401939904288361) ^ 200969952144180 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (17 : ZMod 401939904288361) ^ 133979968096120 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (17 : ZMod 401939904288361) ^ 80387980857672 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (17 : ZMod 401939904288361) ^ 5999103049080 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (17 : ZMod 401939904288361) ^ 8040 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_516699234063517 : Nat.Prime 516699234063517 := by
  apply lucas_primality 516699234063517 (6 : ZMod 516699234063517)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (1789559, 1), (3437261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (1789559, 1), (3437261, 1)] : List FactorBlock).map factorBlockValue).prod) = 516699234063517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_1789559
      · exact prime_oneHundredSixtyFourFF_3437261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 516699234063517) ^ 258349617031758 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 516699234063517) ^ 172233078021172 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 516699234063517) ^ 73814176294788 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 516699234063517) ^ 288729924 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 516699234063517) ^ 150322956 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_703417345854631 : Nat.Prime 703417345854631 := by
  apply lucas_primality 703417345854631 (3 : ZMod 703417345854631)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (2131567714711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (2131567714711, 1)] : List FactorBlock).map factorBlockValue).prod) = 703417345854631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_11
      · exact prime_oneHundredSixtyFourFF_2131567714711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 703417345854631) ^ 351708672927315 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 703417345854631) ^ 234472448618210 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 703417345854631) ^ 140683469170926 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 703417345854631) ^ 63947031441330 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 703417345854631) ^ 330 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_832394148060743 : Nat.Prime 832394148060743 := by
  apply lucas_primality 832394148060743 (5 : ZMod 832394148060743)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (103, 1), (2029, 1), (3299, 1), (603667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (103, 1), (2029, 1), (3299, 1), (603667, 1)] : List FactorBlock).map factorBlockValue).prod) = 832394148060743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_103
      · exact prime_oneHundredSixtyFourFF_2029
      · exact prime_oneHundredSixtyFourFF_3299
      · exact prime_oneHundredSixtyFourFF_603667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 832394148060743) ^ 416197074030371 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 832394148060743) ^ 8081496583114 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 832394148060743) ^ 410248471198 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 832394148060743) ^ 252317110658 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 832394148060743) ^ 1378896226 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_869015822385539 : Nat.Prime 869015822385539 := by
  apply lucas_primality 869015822385539 (2 : ZMod 869015822385539)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19429, 1), (22363884461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19429, 1), (22363884461, 1)] : List FactorBlock).map factorBlockValue).prod) = 869015822385539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_19429
      · exact prime_oneHundredSixtyFourFF_22363884461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 869015822385539) ^ 434507911192769 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 869015822385539) ^ 44727768922 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 869015822385539) ^ 38858 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_913439410268023 : Nat.Prime 913439410268023 := by
  apply lucas_primality 913439410268023 (3 : ZMod 913439410268023)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (17, 1), (90457457939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (17, 1), (90457457939, 1)] : List FactorBlock).map factorBlockValue).prod) = 913439410268023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_11
      · exact prime_oneHundredSixtyFourFF_17
      · exact prime_oneHundredSixtyFourFF_90457457939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 913439410268023) ^ 456719705134011 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 913439410268023) ^ 304479803422674 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 913439410268023) ^ 83039946388002 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 913439410268023) ^ 53731730015766 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 913439410268023) ^ 10098 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_921314287658533 : Nat.Prime 921314287658533 := by
  apply lucas_primality 921314287658533 (2 : ZMod 921314287658533)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (284831, 1), (269549981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (284831, 1), (269549981, 1)] : List FactorBlock).map factorBlockValue).prod) = 921314287658533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_284831
      · exact prime_oneHundredSixtyFourFF_269549981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 921314287658533) ^ 460657143829266 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 921314287658533) ^ 307104762552844 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 921314287658533) ^ 3234599772 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 921314287658533) ^ 3417972 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_1102615096515773 : Nat.Prime 1102615096515773 := by
  apply lucas_primality 1102615096515773 (2 : ZMod 1102615096515773)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (1237, 1), (31834365877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (1237, 1), (31834365877, 1)] : List FactorBlock).map factorBlockValue).prod) = 1102615096515773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_1237
      · exact prime_oneHundredSixtyFourFF_31834365877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1102615096515773) ^ 551307548257886 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1102615096515773) ^ 157516442359396 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1102615096515773) ^ 891362244556 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1102615096515773) ^ 34636 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_1147081303111951 : Nat.Prime 1147081303111951 := by
  apply lucas_primality 1147081303111951 (6 : ZMod 1147081303111951)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 2), (89, 1), (17573, 1), (543281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 2), (89, 1), (17573, 1), (543281, 1)] : List FactorBlock).map factorBlockValue).prod) = 1147081303111951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_89
      · exact prime_oneHundredSixtyFourFF_17573
      · exact prime_oneHundredSixtyFourFF_543281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1147081303111951) ^ 573540651555975 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1147081303111951) ^ 382360434370650 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1147081303111951) ^ 229416260622390 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1147081303111951) ^ 12888553967550 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1147081303111951) ^ 65275212150 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1147081303111951) ^ 2111395950 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_1346306260670803 : Nat.Prime 1346306260670803 := by
  apply lucas_primality 1346306260670803 (3 : ZMod 1346306260670803)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (23, 1), (3251947489543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (23, 1), (3251947489543, 1)] : List FactorBlock).map factorBlockValue).prod) = 1346306260670803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_23
      · exact prime_oneHundredSixtyFourFF_3251947489543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1346306260670803) ^ 673153130335401 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1346306260670803) ^ 448768753556934 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1346306260670803) ^ 58535054811774 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1346306260670803) ^ 414 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_1459412986536101 : Nat.Prime 1459412986536101 := by
  apply lucas_primality 1459412986536101 (2 : ZMod 1459412986536101)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (643, 1), (22696936027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (643, 1), (22696936027, 1)] : List FactorBlock).map factorBlockValue).prod) = 1459412986536101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_643
      · exact prime_oneHundredSixtyFourFF_22696936027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1459412986536101) ^ 729706493268050 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1459412986536101) ^ 291882597307220 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1459412986536101) ^ 2269693602700 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1459412986536101) ^ 64300 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_1515334503875653 : Nat.Prime 1515334503875653 := by
  apply lucas_primality 1515334503875653 (2 : ZMod 1515334503875653)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (1439, 1), (123737, 1), (236399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (1439, 1), (123737, 1), (236399, 1)] : List FactorBlock).map factorBlockValue).prod) = 1515334503875653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_1439
      · exact prime_oneHundredSixtyFourFF_123737
      · exact prime_oneHundredSixtyFourFF_236399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1515334503875653) ^ 757667251937826 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1515334503875653) ^ 505111501291884 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1515334503875653) ^ 1053046910268 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1515334503875653) ^ 12246413796 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1515334503875653) ^ 6410071548 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_1595222941710373 : Nat.Prime 1595222941710373 := by
  apply lucas_primality 1595222941710373 (2 : ZMod 1595222941710373)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (2857, 1), (3579204791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (2857, 1), (3579204791, 1)] : List FactorBlock).map factorBlockValue).prod) = 1595222941710373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_13
      · exact prime_oneHundredSixtyFourFF_2857
      · exact prime_oneHundredSixtyFourFF_3579204791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1595222941710373) ^ 797611470855186 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1595222941710373) ^ 531740980570124 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1595222941710373) ^ 122709457054644 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1595222941710373) ^ 558355947396 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1595222941710373) ^ 445692 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_1642813630652009 : Nat.Prime 1642813630652009 := by
  apply lucas_primality 1642813630652009 (3 : ZMod 1642813630652009)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (2297, 1), (3082757177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (2297, 1), (3082757177, 1)] : List FactorBlock).map factorBlockValue).prod) = 1642813630652009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_29
      · exact prime_oneHundredSixtyFourFF_2297
      · exact prime_oneHundredSixtyFourFF_3082757177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1642813630652009) ^ 821406815326004 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1642813630652009) ^ 56648745884552 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1642813630652009) ^ 715199665064 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1642813630652009) ^ 532904 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_1778938514261231 : Nat.Prime 1778938514261231 := by
  apply lucas_primality 1778938514261231 (7 : ZMod 1778938514261231)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (11939, 1), (2128604351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (11939, 1), (2128604351, 1)] : List FactorBlock).map factorBlockValue).prod) = 1778938514261231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_11939
      · exact prime_oneHundredSixtyFourFF_2128604351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1778938514261231) ^ 889469257130615 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1778938514261231) ^ 355787702852246 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1778938514261231) ^ 254134073465890 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1778938514261231) ^ 149002304570 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1778938514261231) ^ 835730 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_2319007431785003 : Nat.Prime 2319007431785003 := by
  apply lucas_primality 2319007431785003 (5 : ZMod 2319007431785003)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 1), (15319, 1), (636055141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 1), (15319, 1), (636055141, 1)] : List FactorBlock).map factorBlockValue).prod) = 2319007431785003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_17
      · exact prime_oneHundredSixtyFourFF_15319
      · exact prime_oneHundredSixtyFourFF_636055141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2319007431785003) ^ 1159503715892501 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 2319007431785003) ^ 331286775969286 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 2319007431785003) ^ 136412201869706 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 2319007431785003) ^ 151381123558 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 2319007431785003) ^ 3645922 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_2344251628871513 : Nat.Prime 2344251628871513 := by
  apply lucas_primality 2344251628871513 (5 : ZMod 2344251628871513)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (15173, 1), (1016457397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (15173, 1), (1016457397, 1)] : List FactorBlock).map factorBlockValue).prod) = 2344251628871513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_19
      · exact prime_oneHundredSixtyFourFF_15173
      · exact prime_oneHundredSixtyFourFF_1016457397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2344251628871513) ^ 1172125814435756 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 2344251628871513) ^ 123381664677448 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 2344251628871513) ^ 154501524344 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 2344251628871513) ^ 2306296 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_2755381149319543 : Nat.Prime 2755381149319543 := by
  apply lucas_primality 2755381149319543 (3 : ZMod 2755381149319543)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (26399, 1), (370122169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (26399, 1), (370122169, 1)] : List FactorBlock).map factorBlockValue).prod) = 2755381149319543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_47
      · exact prime_oneHundredSixtyFourFF_26399
      · exact prime_oneHundredSixtyFourFF_370122169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2755381149319543) ^ 1377690574659771 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2755381149319543) ^ 918460383106514 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2755381149319543) ^ 58625130836586 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2755381149319543) ^ 104374451658 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2755381149319543) ^ 7444518 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_2926544933989319 : Nat.Prime 2926544933989319 := by
  apply lucas_primality 2926544933989319 (11 : ZMod 2926544933989319)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (47202337644989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (47202337644989, 1)] : List FactorBlock).map factorBlockValue).prod) = 2926544933989319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_31
      · exact prime_oneHundredSixtyFourFF_47202337644989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 2926544933989319) ^ 1463272466994659 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 2926544933989319) ^ 94404675289978 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 2926544933989319) ^ 62 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_3104478420411569 : Nat.Prime 3104478420411569 := by
  apply lucas_primality 3104478420411569 (3 : ZMod 3104478420411569)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (29, 1), (12143, 1), (19207, 1), (28687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (29, 1), (12143, 1), (19207, 1), (28687, 1)] : List FactorBlock).map factorBlockValue).prod) = 3104478420411569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_29
      · exact prime_oneHundredSixtyFourFF_12143
      · exact prime_oneHundredSixtyFourFF_19207
      · exact prime_oneHundredSixtyFourFF_28687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3104478420411569) ^ 1552239210205784 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3104478420411569) ^ 107050980014192 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3104478420411569) ^ 255659920976 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3104478420411569) ^ 161632655824 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3104478420411569) ^ 108218998864 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_3418943018211107 : Nat.Prime 3418943018211107 := by
  apply lucas_primality 3418943018211107 (5 : ZMod 3418943018211107)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (673, 1), (739, 1), (1123, 1), (1367, 1), (2239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (673, 1), (739, 1), (1123, 1), (1367, 1), (2239, 1)] : List FactorBlock).map factorBlockValue).prod) = 3418943018211107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_673
      · exact prime_oneHundredSixtyFourFF_739
      · exact prime_oneHundredSixtyFourFF_1123
      · exact prime_oneHundredSixtyFourFF_1367
      · exact prime_oneHundredSixtyFourFF_2239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3418943018211107) ^ 1709471509105553 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 3418943018211107) ^ 5080153073122 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 3418943018211107) ^ 4626445220854 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 3418943018211107) ^ 3044472856822 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 3418943018211107) ^ 2501055609518 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 3418943018211107) ^ 1526995541854 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_3601732387357921 : Nat.Prime 3601732387357921 := by
  apply lucas_primality 3601732387357921 (19 : ZMod 3601732387357921)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (11399, 1), (658269071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (11399, 1), (658269071, 1)] : List FactorBlock).map factorBlockValue).prod) = 3601732387357921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_11399
      · exact prime_oneHundredSixtyFourFF_658269071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 3601732387357921) ^ 1800866193678960 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (19 : ZMod 3601732387357921) ^ 1200577462452640 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (19 : ZMod 3601732387357921) ^ 720346477471584 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (19 : ZMod 3601732387357921) ^ 315969154080 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (19 : ZMod 3601732387357921) ^ 5471520 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_3969228357520873 : Nat.Prime 3969228357520873 := by
  apply lucas_primality 3969228357520873 (5 : ZMod 3969228357520873)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (165384514896703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (165384514896703, 1)] : List FactorBlock).map factorBlockValue).prod) = 3969228357520873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_165384514896703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3969228357520873) ^ 1984614178760436 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 3969228357520873) ^ 1323076119173624 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 3969228357520873) ^ 24 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_4297030639798109 : Nat.Prime 4297030639798109 := by
  apply lucas_primality 4297030639798109 (2 : ZMod 4297030639798109)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (257893, 1), (4165516939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (257893, 1), (4165516939, 1)] : List FactorBlock).map factorBlockValue).prod) = 4297030639798109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_257893
      · exact prime_oneHundredSixtyFourFF_4165516939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4297030639798109) ^ 2148515319899054 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4297030639798109) ^ 16662067756 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4297030639798109) ^ 1031572 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_5447137183249451 : Nat.Prime 5447137183249451 := by
  apply lucas_primality 5447137183249451 (2 : ZMod 5447137183249451)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (13, 1), (8380211051153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (13, 1), (8380211051153, 1)] : List FactorBlock).map factorBlockValue).prod) = 5447137183249451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_13
      · exact prime_oneHundredSixtyFourFF_8380211051153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5447137183249451) ^ 2723568591624725 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5447137183249451) ^ 1089427436649890 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5447137183249451) ^ 419010552557650 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5447137183249451) ^ 650 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_5975488216114349 : Nat.Prime 5975488216114349 := by
  apply lucas_primality 5975488216114349 (2 : ZMod 5975488216114349)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (37, 1), (137, 1), (1381, 1), (11231657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (37, 1), (137, 1), (1381, 1), (11231657, 1)] : List FactorBlock).map factorBlockValue).prod) = 5975488216114349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_19
      · exact prime_oneHundredSixtyFourFF_37
      · exact prime_oneHundredSixtyFourFF_137
      · exact prime_oneHundredSixtyFourFF_1381
      · exact prime_oneHundredSixtyFourFF_11231657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5975488216114349) ^ 2987744108057174 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5975488216114349) ^ 314499379795492 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5975488216114349) ^ 161499681516604 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5975488216114349) ^ 43616702307404 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5975488216114349) ^ 4326928469308 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5975488216114349) ^ 532021964 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_6436909211527021 : Nat.Prime 6436909211527021 := by
  apply lucas_primality 6436909211527021 (7 : ZMod 6436909211527021)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (29, 1), (37, 1), (99983057029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (29, 1), (37, 1), (99983057029, 1)] : List FactorBlock).map factorBlockValue).prod) = 6436909211527021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_29
      · exact prime_oneHundredSixtyFourFF_37
      · exact prime_oneHundredSixtyFourFF_99983057029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6436909211527021) ^ 3218454605763510 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 6436909211527021) ^ 2145636403842340 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 6436909211527021) ^ 1287381842305404 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 6436909211527021) ^ 221962386604380 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 6436909211527021) ^ 173970519230460 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 6436909211527021) ^ 64380 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_11107507708411489 : Nat.Prime 11107507708411489 := by
  apply lucas_primality 11107507708411489 (13 : ZMod 11107507708411489)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (11, 1), (72221, 1), (48547621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (11, 1), (72221, 1), (48547621, 1)] : List FactorBlock).map factorBlockValue).prod) = 11107507708411489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_11
      · exact prime_oneHundredSixtyFourFF_72221
      · exact prime_oneHundredSixtyFourFF_48547621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 11107507708411489) ^ 5553753854205744 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (13 : ZMod 11107507708411489) ^ 3702502569470496 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (13 : ZMod 11107507708411489) ^ 1009773428037408 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (13 : ZMod 11107507708411489) ^ 153798863328 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (13 : ZMod 11107507708411489) ^ 228796128 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_11686692549455557 : Nat.Prime 11686692549455557 := by
  apply lucas_primality 11686692549455557 (2 : ZMod 11686692549455557)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2437, 1), (399627019199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2437, 1), (399627019199, 1)] : List FactorBlock).map factorBlockValue).prod) = 11686692549455557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_2437
      · exact prime_oneHundredSixtyFourFF_399627019199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11686692549455557) ^ 5843346274727778 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 11686692549455557) ^ 3895564183151852 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 11686692549455557) ^ 4795524230388 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 11686692549455557) ^ 29244 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_17668655337510829 : Nat.Prime 17668655337510829 := by
  apply lucas_primality 17668655337510829 (13 : ZMod 17668655337510829)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (523, 1), (134060634143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (523, 1), (134060634143, 1)] : List FactorBlock).map factorBlockValue).prod) = 17668655337510829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_523
      · exact prime_oneHundredSixtyFourFF_134060634143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 17668655337510829) ^ 8834327668755414 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (13 : ZMod 17668655337510829) ^ 5889551779170276 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (13 : ZMod 17668655337510829) ^ 2524093619644404 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (13 : ZMod 17668655337510829) ^ 33783279804036 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (13 : ZMod 17668655337510829) ^ 131796 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_24575799027930583 : Nat.Prime 24575799027930583 := by
  apply lucas_primality 24575799027930583 (5 : ZMod 24575799027930583)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (23539, 1), (4046689961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (23539, 1), (4046689961, 1)] : List FactorBlock).map factorBlockValue).prod) = 24575799027930583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_43
      · exact prime_oneHundredSixtyFourFF_23539
      · exact prime_oneHundredSixtyFourFF_4046689961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 24575799027930583) ^ 12287899513965291 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 24575799027930583) ^ 8191933009310194 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 24575799027930583) ^ 571530209951874 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 24575799027930583) ^ 1044046009938 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 24575799027930583) ^ 6073062 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_42147896915954971 : Nat.Prime 42147896915954971 := by
  apply lucas_primality 42147896915954971 (2 : ZMod 42147896915954971)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (19, 1), (601, 1), (5858781301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (19, 1), (601, 1), (5858781301, 1)] : List FactorBlock).map factorBlockValue).prod) = 42147896915954971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_19
      · exact prime_oneHundredSixtyFourFF_601
      · exact prime_oneHundredSixtyFourFF_5858781301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 42147896915954971) ^ 21073948457977485 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 42147896915954971) ^ 14049298971984990 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 42147896915954971) ^ 8429579383190994 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 42147896915954971) ^ 6021128130850710 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 42147896915954971) ^ 2218310363997630 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 42147896915954971) ^ 70129612172970 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 42147896915954971) ^ 7193970 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_45892067362318349 : Nat.Prime 45892067362318349 := by
  apply lucas_primality 45892067362318349 (2 : ZMod 45892067362318349)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31513, 1), (43291, 1), (8409889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31513, 1), (43291, 1), (8409889, 1)] : List FactorBlock).map factorBlockValue).prod) = 45892067362318349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_31513
      · exact prime_oneHundredSixtyFourFF_43291
      · exact prime_oneHundredSixtyFourFF_8409889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 45892067362318349) ^ 22946033681159174 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 45892067362318349) ^ 1456290018796 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 45892067362318349) ^ 1060083328228 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 45892067362318349) ^ 5456917132 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_68177254042191571 : Nat.Prime 68177254042191571 := by
  apply lucas_primality 68177254042191571 (2 : ZMod 68177254042191571)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (29, 1), (523, 1), (8813930921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (29, 1), (523, 1), (8813930921, 1)] : List FactorBlock).map factorBlockValue).prod) = 68177254042191571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_17
      · exact prime_oneHundredSixtyFourFF_29
      · exact prime_oneHundredSixtyFourFF_523
      · exact prime_oneHundredSixtyFourFF_8813930921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 68177254042191571) ^ 34088627021095785 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 68177254042191571) ^ 22725751347397190 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 68177254042191571) ^ 13635450808438314 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 68177254042191571) ^ 4010426708364210 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 68177254042191571) ^ 2350939794558330 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 68177254042191571) ^ 130358038321590 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 68177254042191571) ^ 7735170 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_73257488963930321 : Nat.Prime 73257488963930321 := by
  apply lucas_primality 73257488963930321 (3 : ZMod 73257488963930321)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (7, 1), (130816944578447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (7, 1), (130816944578447, 1)] : List FactorBlock).map factorBlockValue).prod) = 73257488963930321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_130816944578447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 73257488963930321) ^ 36628744481965160 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 73257488963930321) ^ 14651497792786064 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 73257488963930321) ^ 10465355566275760 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 73257488963930321) ^ 560 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_140228518397647921 : Nat.Prime 140228518397647921 := by
  apply lucas_primality 140228518397647921 (14 : ZMod 140228518397647921)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (1693, 1), (345118424881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (1693, 1), (345118424881, 1)] : List FactorBlock).map factorBlockValue).prod) = 140228518397647921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_1693
      · exact prime_oneHundredSixtyFourFF_345118424881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 140228518397647921) ^ 70114259198823960 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (14 : ZMod 140228518397647921) ^ 46742839465882640 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (14 : ZMod 140228518397647921) ^ 28045703679529584 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (14 : ZMod 140228518397647921) ^ 82828421971440 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (14 : ZMod 140228518397647921) ^ 406320 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_181855155855089839 : Nat.Prime 181855155855089839 := by
  apply lucas_primality 181855155855089839 (3 : ZMod 181855155855089839)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (2755381149319543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (2755381149319543, 1)] : List FactorBlock).map factorBlockValue).prod) = 181855155855089839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_11
      · exact prime_oneHundredSixtyFourFF_2755381149319543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 181855155855089839) ^ 90927577927544919 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 181855155855089839) ^ 60618385285029946 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 181855155855089839) ^ 16532286895917258 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 181855155855089839) ^ 66 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_188148678680386871 : Nat.Prime 188148678680386871 := by
  apply lucas_primality 188148678680386871 (17 : ZMod 188148678680386871)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (79, 1), (238162884405553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (79, 1), (238162884405553, 1)] : List FactorBlock).map factorBlockValue).prod) = 188148678680386871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_79
      · exact prime_oneHundredSixtyFourFF_238162884405553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 188148678680386871) ^ 94074339340193435 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (17 : ZMod 188148678680386871) ^ 37629735736077374 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (17 : ZMod 188148678680386871) ^ 2381628844055530 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (17 : ZMod 188148678680386871) ^ 790 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_258910398667039607 : Nat.Prime 258910398667039607 := by
  apply lucas_primality 258910398667039607 (5 : ZMod 258910398667039607)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (40189, 1), (45368450737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (40189, 1), (45368450737, 1)] : List FactorBlock).map factorBlockValue).prod) = 258910398667039607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_71
      · exact prime_oneHundredSixtyFourFF_40189
      · exact prime_oneHundredSixtyFourFF_45368450737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 258910398667039607) ^ 129455199333519803 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 258910398667039607) ^ 3646625333338586 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 258910398667039607) ^ 6442320004654 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 258910398667039607) ^ 5706838 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_294952180746895531 : Nat.Prime 294952180746895531 := by
  apply lucas_primality 294952180746895531 (10 : ZMod 294952180746895531)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (59, 1), (4933, 1), (63601, 1), (531133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (59, 1), (4933, 1), (63601, 1), (531133, 1)] : List FactorBlock).map factorBlockValue).prod) = 294952180746895531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_59
      · exact prime_oneHundredSixtyFourFF_4933
      · exact prime_oneHundredSixtyFourFF_63601
      · exact prime_oneHundredSixtyFourFF_531133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 294952180746895531) ^ 147476090373447765 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (10 : ZMod 294952180746895531) ^ 98317393582298510 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (10 : ZMod 294952180746895531) ^ 58990436149379106 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (10 : ZMod 294952180746895531) ^ 4999189504184670 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (10 : ZMod 294952180746895531) ^ 59791644181410 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (10 : ZMod 294952180746895531) ^ 4637539987530 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (10 : ZMod 294952180746895531) ^ 555326407410 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_487934319167696389 : Nat.Prime 487934319167696389 := by
  apply lucas_primality 487934319167696389 (2 : ZMod 487934319167696389)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (1289, 1), (2426519858207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (1289, 1), (2426519858207, 1)] : List FactorBlock).map factorBlockValue).prod) = 487934319167696389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_13
      · exact prime_oneHundredSixtyFourFF_1289
      · exact prime_oneHundredSixtyFourFF_2426519858207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 487934319167696389) ^ 243967159583848194 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 487934319167696389) ^ 162644773055898796 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 487934319167696389) ^ 37533409166745876 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 487934319167696389) ^ 378537097880292 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 487934319167696389) ^ 201084 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_567946754125831019 : Nat.Prime 567946754125831019 := by
  apply lucas_primality 567946754125831019 (2 : ZMod 567946754125831019)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (913259, 1), (310945062751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (913259, 1), (310945062751, 1)] : List FactorBlock).map factorBlockValue).prod) = 567946754125831019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_913259
      · exact prime_oneHundredSixtyFourFF_310945062751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 567946754125831019) ^ 283973377062915509 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 567946754125831019) ^ 621890125502 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 567946754125831019) ^ 1826518 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_1364354448003220567 : Nat.Prime 1364354448003220567 := by
  apply lucas_primality 1364354448003220567 (3 : ZMod 1364354448003220567)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (97, 1), (2344251628871513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (97, 1), (2344251628871513, 1)] : List FactorBlock).map factorBlockValue).prod) = 1364354448003220567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_97
      · exact prime_oneHundredSixtyFourFF_2344251628871513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1364354448003220567) ^ 682177224001610283 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1364354448003220567) ^ 454784816001073522 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1364354448003220567) ^ 14065509773229078 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1364354448003220567) ^ 582 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_2220502305087140441 : Nat.Prime 2220502305087140441 := by
  apply lucas_primality 2220502305087140441 (3 : ZMod 2220502305087140441)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2220502305087140441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_101
      · exact prime_oneHundredSixtyFourFF_191
      · exact prime_oneHundredSixtyFourFF_48017
      · exact prime_oneHundredSixtyFourFF_59929613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2220502305087140441) ^ 1110251152543570220 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 444100461017428088 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 21985171337496440 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 11625666518780840 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 46244086575320 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 37051837880 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_3351654105219542953 : Nat.Prime 3351654105219542953 := by
  apply lucas_primality 3351654105219542953 (5 : ZMod 3351654105219542953)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (1637, 1), (56099, 1), (506900707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (1637, 1), (56099, 1), (506900707, 1)] : List FactorBlock).map factorBlockValue).prod) = 3351654105219542953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_1637
      · exact prime_oneHundredSixtyFourFF_56099
      · exact prime_oneHundredSixtyFourFF_506900707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3351654105219542953) ^ 1675827052609771476 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 3351654105219542953) ^ 1117218035073180984 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 3351654105219542953) ^ 2047436838863496 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 3351654105219542953) ^ 59745344929848 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 3351654105219542953) ^ 6612052536 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_4294340159084324117 : Nat.Prime 4294340159084324117 := by
  apply lucas_primality 4294340159084324117 (2 : ZMod 4294340159084324117)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (673, 1), (1595222941710373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (673, 1), (1595222941710373, 1)] : List FactorBlock).map factorBlockValue).prod) = 4294340159084324117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_673
      · exact prime_oneHundredSixtyFourFF_1595222941710373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4294340159084324117) ^ 2147170079542162058 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4294340159084324117) ^ 6380891766841492 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4294340159084324117) ^ 2692 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_5624545428789411469 : Nat.Prime 5624545428789411469 := by
  apply lucas_primality 5624545428789411469 (2 : ZMod 5624545428789411469)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (85639, 1), (800801, 1), (6834551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (85639, 1), (800801, 1), (6834551, 1)] : List FactorBlock).map factorBlockValue).prod) = 5624545428789411469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_85639
      · exact prime_oneHundredSixtyFourFF_800801
      · exact prime_oneHundredSixtyFourFF_6834551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5624545428789411469) ^ 2812272714394705734 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5624545428789411469) ^ 1874848476263137156 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5624545428789411469) ^ 65677383304212 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5624545428789411469) ^ 7023649357068 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5624545428789411469) ^ 822957562068 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_5782090582925066821 : Nat.Prime 5782090582925066821 := by
  apply lucas_primality 5782090582925066821 (2 : ZMod 5782090582925066821)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (137, 1), (703417345854631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (137, 1), (703417345854631, 1)] : List FactorBlock).map factorBlockValue).prod) = 5782090582925066821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_137
      · exact prime_oneHundredSixtyFourFF_703417345854631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5782090582925066821) ^ 2891045291462533410 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5782090582925066821) ^ 1927363527641688940 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5782090582925066821) ^ 1156418116585013364 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5782090582925066821) ^ 42205040751277860 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5782090582925066821) ^ 8220 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_6168559768548107981 : Nat.Prime 6168559768548107981 := by
  apply lucas_primality 6168559768548107981 (2 : ZMod 6168559768548107981)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (19, 1), (2319007431785003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (19, 1), (2319007431785003, 1)] : List FactorBlock).map factorBlockValue).prod) = 6168559768548107981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_19
      · exact prime_oneHundredSixtyFourFF_2319007431785003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6168559768548107981) ^ 3084279884274053990 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 6168559768548107981) ^ 1233711953709621596 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 6168559768548107981) ^ 881222824078301140 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 6168559768548107981) ^ 324661040449900420 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 6168559768548107981) ^ 2660 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_7960592447355846451 : Nat.Prime 7960592447355846451 := by
  apply lucas_primality 7960592447355846451 (3 : ZMod 7960592447355846451)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (142724963, 1), (371838361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (142724963, 1), (371838361, 1)] : List FactorBlock).map factorBlockValue).prod) = 7960592447355846451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_142724963
      · exact prime_oneHundredSixtyFourFF_371838361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7960592447355846451) ^ 3980296223677923225 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 7960592447355846451) ^ 2653530815785282150 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 7960592447355846451) ^ 1592118489471169290 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 7960592447355846451) ^ 55775754150 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 7960592447355846451) ^ 21408744450 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_12337119537096215963 : Nat.Prime 12337119537096215963 := by
  apply lucas_primality 12337119537096215963 (2 : ZMod 12337119537096215963)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6168559768548107981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6168559768548107981, 1)] : List FactorBlock).map factorBlockValue).prod) = 12337119537096215963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_6168559768548107981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 12337119537096215963) ^ 6168559768548107981 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 12337119537096215963) ^ 2 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_13565500811951685053 : Nat.Prime 13565500811951685053 := by
  apply lucas_primality 13565500811951685053 (2 : ZMod 13565500811951685053)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (197, 1), (283, 1), (661, 1), (92028367733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (197, 1), (283, 1), (661, 1), (92028367733, 1)] : List FactorBlock).map factorBlockValue).prod) = 13565500811951685053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_197
      · exact prime_oneHundredSixtyFourFF_283
      · exact prime_oneHundredSixtyFourFF_661
      · exact prime_oneHundredSixtyFourFF_92028367733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13565500811951685053) ^ 6782750405975842526 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 13565500811951685053) ^ 68860410212952716 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 13565500811951685053) ^ 47934631844352244 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 13565500811951685053) ^ 20522694117929932 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 13565500811951685053) ^ 147405644 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_24558942701919019327 : Nat.Prime 24558942701919019327 := by
  apply lucas_primality 24558942701919019327 (5 : ZMod 24558942701919019327)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (73, 1), (127, 1), (401, 1), (1101000362051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (73, 1), (127, 1), (401, 1), (1101000362051, 1)] : List FactorBlock).map factorBlockValue).prod) = 24558942701919019327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_73
      · exact prime_oneHundredSixtyFourFF_127
      · exact prime_oneHundredSixtyFourFF_401
      · exact prime_oneHundredSixtyFourFF_1101000362051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 24558942701919019327) ^ 12279471350959509663 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 24558942701919019327) ^ 8186314233973006442 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 24558942701919019327) ^ 336423872629027662 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 24558942701919019327) ^ 193377501589913538 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 24558942701919019327) ^ 61244246139448926 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 24558942701919019327) ^ 22306026 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_33551929945480087019 : Nat.Prime 33551929945480087019 := by
  apply lucas_primality 33551929945480087019 (2 : ZMod 33551929945480087019)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (229, 1), (73257488963930321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (229, 1), (73257488963930321, 1)] : List FactorBlock).map factorBlockValue).prod) = 33551929945480087019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_229
      · exact prime_oneHundredSixtyFourFF_73257488963930321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 33551929945480087019) ^ 16775964972740043509 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 33551929945480087019) ^ 146514977927860642 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 33551929945480087019) ^ 458 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_67340047169201976727 : Nat.Prime 67340047169201976727 := by
  apply lucas_primality 67340047169201976727 (3 : ZMod 67340047169201976727)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (397, 1), (619, 1), (1062117475429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (397, 1), (619, 1), (1062117475429, 1)] : List FactorBlock).map factorBlockValue).prod) = 67340047169201976727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_43
      · exact prime_oneHundredSixtyFourFF_397
      · exact prime_oneHundredSixtyFourFF_619
      · exact prime_oneHundredSixtyFourFF_1062117475429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 67340047169201976727) ^ 33670023584600988363 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 67340047169201976727) ^ 22446682389733992242 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 67340047169201976727) ^ 1566047608586092482 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 67340047169201976727) ^ 169622285060962158 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 67340047169201976727) ^ 108788444538290754 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 67340047169201976727) ^ 63401694 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_126629763789109058197 : Nat.Prime 126629763789109058197 := by
  apply lucas_primality 126629763789109058197 (2 : ZMod 126629763789109058197)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (107, 1), (3163, 1), (959377, 1), (32499919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (107, 1), (3163, 1), (959377, 1), (32499919, 1)] : List FactorBlock).map factorBlockValue).prod) = 126629763789109058197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_107
      · exact prime_oneHundredSixtyFourFF_3163
      · exact prime_oneHundredSixtyFourFF_959377
      · exact prime_oneHundredSixtyFourFF_32499919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 126629763789109058197) ^ 63314881894554529098 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 126629763789109058197) ^ 42209921263036352732 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 126629763789109058197) ^ 1183455736346813628 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 126629763789109058197) ^ 40034702430954492 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 126629763789109058197) ^ 131991661035348 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 126629763789109058197) ^ 3896310135084 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_185581868523852011111 : Nat.Prime 185581868523852011111 := by
  apply lucas_primality 185581868523852011111 (29 : ZMod 185581868523852011111)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (74573, 1), (248859330486707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (74573, 1), (248859330486707, 1)] : List FactorBlock).map factorBlockValue).prod) = 185581868523852011111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_74573
      · exact prime_oneHundredSixtyFourFF_248859330486707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (29 : ZMod 185581868523852011111) ^ 92790934261926005555 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (29 : ZMod 185581868523852011111) ^ 37116373704770402222 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (29 : ZMod 185581868523852011111) ^ 2488593304867070 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (29 : ZMod 185581868523852011111) ^ 745730 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_190007876139113360479 : Nat.Prime 190007876139113360479 := by
  apply lucas_primality 190007876139113360479 (3 : ZMod 190007876139113360479)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (167, 1), (367, 1), (516699234063517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (167, 1), (367, 1), (516699234063517, 1)] : List FactorBlock).map factorBlockValue).prod) = 190007876139113360479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_167
      · exact prime_oneHundredSixtyFourFF_367
      · exact prime_oneHundredSixtyFourFF_516699234063517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 190007876139113360479) ^ 95003938069556680239 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 190007876139113360479) ^ 63335958713037786826 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 190007876139113360479) ^ 1137771713407864434 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 190007876139113360479) ^ 517732632531644034 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 190007876139113360479) ^ 367734 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_193321534648399602553 : Nat.Prime 193321534648399602553 := by
  apply lucas_primality 193321534648399602553 (5 : ZMod 193321534648399602553)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (83, 1), (301759, 1), (107203610803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (83, 1), (301759, 1), (107203610803, 1)] : List FactorBlock).map factorBlockValue).prod) = 193321534648399602553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_83
      · exact prime_oneHundredSixtyFourFF_301759
      · exact prime_oneHundredSixtyFourFF_107203610803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 193321534648399602553) ^ 96660767324199801276 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 193321534648399602553) ^ 64440511549466534184 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 193321534648399602553) ^ 2329175116245778344 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 193321534648399602553) ^ 640648778158728 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 193321534648399602553) ^ 1803311784 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_295369972205561217131 : Nat.Prime 295369972205561217131 := by
  apply lucas_primality 295369972205561217131 (2 : ZMod 295369972205561217131)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (21347, 1), (1146703, 1), (1206642293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (21347, 1), (1146703, 1), (1206642293, 1)] : List FactorBlock).map factorBlockValue).prod) = 295369972205561217131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_21347
      · exact prime_oneHundredSixtyFourFF_1146703
      · exact prime_oneHundredSixtyFourFF_1206642293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 295369972205561217131) ^ 147684986102780608565 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 295369972205561217131) ^ 59073994441112243426 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 295369972205561217131) ^ 13836603373099790 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 295369972205561217131) ^ 257581930286710 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 295369972205561217131) ^ 244786689410 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_320510527058681839513 : Nat.Prime 320510527058681839513 := by
  apply lucas_primality 320510527058681839513 (11 : ZMod 320510527058681839513)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (11549, 1), (385447666294679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (11549, 1), (385447666294679, 1)] : List FactorBlock).map factorBlockValue).prod) = 320510527058681839513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_11549
      · exact prime_oneHundredSixtyFourFF_385447666294679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 320510527058681839513) ^ 160255263529340919756 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 320510527058681839513) ^ 106836842352893946504 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 320510527058681839513) ^ 27752231973216888 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (11 : ZMod 320510527058681839513) ^ 831528 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_436828283214730158953 : Nat.Prime 436828283214730158953 := by
  apply lucas_primality 436828283214730158953 (3 : ZMod 436828283214730158953)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (59, 1), (773, 1), (1151, 1), (77527, 1), (13417171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (59, 1), (773, 1), (1151, 1), (77527, 1), (13417171, 1)] : List FactorBlock).map factorBlockValue).prod) = 436828283214730158953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_59
      · exact prime_oneHundredSixtyFourFF_773
      · exact prime_oneHundredSixtyFourFF_1151
      · exact prime_oneHundredSixtyFourFF_77527
      · exact prime_oneHundredSixtyFourFF_13417171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 436828283214730158953) ^ 218414141607365079476 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 436828283214730158953) ^ 7403869207029324728 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 436828283214730158953) ^ 565107740251914824 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 436828283214730158953) ^ 379520663088384152 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 436828283214730158953) ^ 5634530979074776 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 436828283214730158953) ^ 32557405969912 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_642943883070206397899 : Nat.Prime 642943883070206397899 := by
  apply lucas_primality 642943883070206397899 (2 : ZMod 642943883070206397899)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (109, 1), (1583, 1), (109593990089351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (109, 1), (1583, 1), (109593990089351, 1)] : List FactorBlock).map factorBlockValue).prod) = 642943883070206397899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_17
      · exact prime_oneHundredSixtyFourFF_109
      · exact prime_oneHundredSixtyFourFF_1583
      · exact prime_oneHundredSixtyFourFF_109593990089351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 642943883070206397899) ^ 321471941535103198949 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 642943883070206397899) ^ 37820228415894493994 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 642943883070206397899) ^ 5898567734589049522 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 642943883070206397899) ^ 406155327271134806 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 642943883070206397899) ^ 5866598 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_964943229083469351539 : Nat.Prime 964943229083469351539 := by
  apply lucas_primality 964943229083469351539 (2 : ZMod 964943229083469351539)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (121553, 1), (3969228357520873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (121553, 1), (3969228357520873, 1)] : List FactorBlock).map factorBlockValue).prod) = 964943229083469351539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_121553
      · exact prime_oneHundredSixtyFourFF_3969228357520873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 964943229083469351539) ^ 482471614541734675769 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 964943229083469351539) ^ 7938456715041746 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 964943229083469351539) ^ 243106 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_1247834419777495551863 : Nat.Prime 1247834419777495551863 := by
  apply lucas_primality 1247834419777495551863 (5 : ZMod 1247834419777495551863)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (337, 1), (12241, 1), (21606385793549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (337, 1), (12241, 1), (21606385793549, 1)] : List FactorBlock).map factorBlockValue).prod) = 1247834419777495551863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_337
      · exact prime_oneHundredSixtyFourFF_12241
      · exact prime_oneHundredSixtyFourFF_21606385793549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1247834419777495551863) ^ 623917209888747775931 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1247834419777495551863) ^ 178262059968213650266 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1247834419777495551863) ^ 3702772758983666326 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1247834419777495551863) ^ 101938928173964182 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1247834419777495551863) ^ 57753038 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_2361295683120577261463 : Nat.Prime 2361295683120577261463 := by
  apply lucas_primality 2361295683120577261463 (5 : ZMod 2361295683120577261463)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (14461, 1), (4297030639798109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (14461, 1), (4297030639798109, 1)] : List FactorBlock).map factorBlockValue).prod) = 2361295683120577261463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_19
      · exact prime_oneHundredSixtyFourFF_14461
      · exact prime_oneHundredSixtyFourFF_4297030639798109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2361295683120577261463) ^ 1180647841560288630731 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 2361295683120577261463) ^ 124278720164240908498 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 2361295683120577261463) ^ 163287164312328142 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 2361295683120577261463) ^ 549518 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_2900988442576810679081 : Nat.Prime 2900988442576810679081 := by
  apply lucas_primality 2900988442576810679081 (6 : ZMod 2900988442576810679081)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (37, 1), (96457, 1), (1563173487481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (37, 1), (96457, 1), (1563173487481, 1)] : List FactorBlock).map factorBlockValue).prod) = 2900988442576810679081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_13
      · exact prime_oneHundredSixtyFourFF_37
      · exact prime_oneHundredSixtyFourFF_96457
      · exact prime_oneHundredSixtyFourFF_1563173487481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2900988442576810679081) ^ 1450494221288405339540 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 2900988442576810679081) ^ 580197688515362135816 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 2900988442576810679081) ^ 223152957121293129160 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 2900988442576810679081) ^ 78405093042616504840 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 2900988442576810679081) ^ 30075457899134440 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 2900988442576810679081) ^ 1855832680 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_7825728875814895295329 : Nat.Prime 7825728875814895295329 := by
  apply lucas_primality 7825728875814895295329 (19 : ZMod 7825728875814895295329)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (13, 1), (1741, 1), (3601732387357921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (13, 1), (1741, 1), (3601732387357921, 1)] : List FactorBlock).map factorBlockValue).prod) = 7825728875814895295329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_13
      · exact prime_oneHundredSixtyFourFF_1741
      · exact prime_oneHundredSixtyFourFF_3601732387357921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 7825728875814895295329) ^ 3912864437907447647664 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (19 : ZMod 7825728875814895295329) ^ 2608576291938298431776 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (19 : ZMod 7825728875814895295329) ^ 601979144293453484256 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (19 : ZMod 7825728875814895295329) ^ 4494962019422685408 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (19 : ZMod 7825728875814895295329) ^ 2172768 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_20880029820496582229281 : Nat.Prime 20880029820496582229281 := by
  apply lucas_primality 20880029820496582229281 (13 : ZMod 20880029820496582229281)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (26479, 1), (1642813630652009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (26479, 1), (1642813630652009, 1)] : List FactorBlock).map factorBlockValue).prod) = 20880029820496582229281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_26479
      · exact prime_oneHundredSixtyFourFF_1642813630652009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 20880029820496582229281) ^ 10440014910248291114640 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (13 : ZMod 20880029820496582229281) ^ 6960009940165527409760 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (13 : ZMod 20880029820496582229281) ^ 4176005964099316445856 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (13 : ZMod 20880029820496582229281) ^ 788550542712964320 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (13 : ZMod 20880029820496582229281) ^ 12709920 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_21383825971815701546303 : Nat.Prime 21383825971815701546303 := by
  apply lucas_primality 21383825971815701546303 (5 : ZMod 21383825971815701546303)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (661, 1), (77347, 1), (3945795860701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (661, 1), (77347, 1), (3945795860701, 1)] : List FactorBlock).map factorBlockValue).prod) = 21383825971815701546303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_53
      · exact prime_oneHundredSixtyFourFF_661
      · exact prime_oneHundredSixtyFourFF_77347
      · exact prime_oneHundredSixtyFourFF_3945795860701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 21383825971815701546303) ^ 10691912985907850773151 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 21383825971815701546303) ^ 403468414562560406534 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 21383825971815701546303) ^ 32350720078389866182 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 21383825971815701546303) ^ 276466132775876266 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 21383825971815701546303) ^ 5419394902 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_27358662169937787530279 : Nat.Prime 27358662169937787530279 := by
  apply lucas_primality 27358662169937787530279 (7 : ZMod 27358662169937787530279)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (557, 1), (24558942701919019327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (557, 1), (24558942701919019327, 1)] : List FactorBlock).map factorBlockValue).prod) = 27358662169937787530279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_557
      · exact prime_oneHundredSixtyFourFF_24558942701919019327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 27358662169937787530279) ^ 13679331084968893765139 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 27358662169937787530279) ^ 49117885403838038654 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (7 : ZMod 27358662169937787530279) ^ 1114 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_41687230371793828461023 : Nat.Prime 41687230371793828461023 := by
  apply lucas_primality 41687230371793828461023 (5 : ZMod 41687230371793828461023)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 2), (47, 1), (113, 1), (3461, 1), (105619, 1), (20295391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 2), (47, 1), (113, 1), (3461, 1), (105619, 1), (20295391, 1)] : List FactorBlock).map factorBlockValue).prod) = 41687230371793828461023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_23
      · exact prime_oneHundredSixtyFourFF_47
      · exact prime_oneHundredSixtyFourFF_113
      · exact prime_oneHundredSixtyFourFF_3461
      · exact prime_oneHundredSixtyFourFF_105619
      · exact prime_oneHundredSixtyFourFF_20295391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 41687230371793828461023) ^ 20843615185896914230511 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 41687230371793828461023) ^ 1812488277034514280914 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 41687230371793828461023) ^ 886962348336038903426 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 41687230371793828461023) ^ 368913543113219720894 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 41687230371793828461023) ^ 12044851306499228102 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 41687230371793828461023) ^ 394694424031602538 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 41687230371793828461023) ^ 2054024501020642 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_58888919967460251514613 : Nat.Prime 58888919967460251514613 := by
  apply lucas_primality 58888919967460251514613 (2 : ZMod 58888919967460251514613)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (229043197, 1), (4944391472773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (229043197, 1), (4944391472773, 1)] : List FactorBlock).map factorBlockValue).prod) = 58888919967460251514613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_13
      · exact prime_oneHundredSixtyFourFF_229043197
      · exact prime_oneHundredSixtyFourFF_4944391472773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 58888919967460251514613) ^ 29444459983730125757306 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 58888919967460251514613) ^ 4529916920573865501124 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 58888919967460251514613) ^ 257108356584196 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 58888919967460251514613) ^ 11910246244 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_343036486536021029103367 : Nat.Prime 343036486536021029103367 := by
  apply lucas_primality 343036486536021029103367 (6 : ZMod 343036486536021029103367)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (46687, 1), (2911193, 1), (60093023953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (46687, 1), (2911193, 1), (60093023953, 1)] : List FactorBlock).map factorBlockValue).prod) = 343036486536021029103367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_46687
      · exact prime_oneHundredSixtyFourFF_2911193
      · exact prime_oneHundredSixtyFourFF_60093023953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 343036486536021029103367) ^ 171518243268010514551683 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 343036486536021029103367) ^ 114345495512007009701122 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 343036486536021029103367) ^ 49005212362288718443338 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 343036486536021029103367) ^ 7347580408593849018 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 343036486536021029103367) ^ 117833646390335862 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 343036486536021029103367) ^ 5708424438822 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_365361314137130083028281 : Nat.Prime 365361314137130083028281 := by
  apply lucas_primality 365361314137130083028281 (17 : ZMod 365361314137130083028281)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (43, 1), (191, 1), (23819, 1), (15563811684527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (43, 1), (191, 1), (23819, 1), (15563811684527, 1)] : List FactorBlock).map factorBlockValue).prod) = 365361314137130083028281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_43
      · exact prime_oneHundredSixtyFourFF_191
      · exact prime_oneHundredSixtyFourFF_23819
      · exact prime_oneHundredSixtyFourFF_15563811684527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 365361314137130083028281) ^ 182680657068565041514140 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (17 : ZMod 365361314137130083028281) ^ 121787104712376694342760 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (17 : ZMod 365361314137130083028281) ^ 73072262827426016605656 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (17 : ZMod 365361314137130083028281) ^ 8496774747375118209960 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (17 : ZMod 365361314137130083028281) ^ 1912886461450942843080 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (17 : ZMod 365361314137130083028281) ^ 15339070243802430120 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (17 : ZMod 365361314137130083028281) ^ 23475053640 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_434182931100737130401179 : Nat.Prime 434182931100737130401179 := by
  apply lucas_primality 434182931100737130401179 (10 : ZMod 434182931100737130401179)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (97, 1), (2385340501, 1), (312751484179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (97, 1), (2385340501, 1), (312751484179, 1)] : List FactorBlock).map factorBlockValue).prod) = 434182931100737130401179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_97
      · exact prime_oneHundredSixtyFourFF_2385340501
      · exact prime_oneHundredSixtyFourFF_312751484179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 434182931100737130401179) ^ 217091465550368565200589 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (10 : ZMod 434182931100737130401179) ^ 144727643700245710133726 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (10 : ZMod 434182931100737130401179) ^ 4476112691760176602074 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (10 : ZMod 434182931100737130401179) ^ 182021363792178 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (10 : ZMod 434182931100737130401179) ^ 1388268171582 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_497643265214472763492283 : Nat.Prime 497643265214472763492283 := by
  apply lucas_primality 497643265214472763492283 (2 : ZMod 497643265214472763492283)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (43, 1), (61, 1), (293, 1), (661, 1), (636931, 1), (69909419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (43, 1), (61, 1), (293, 1), (661, 1), (636931, 1), (69909419, 1)] : List FactorBlock).map factorBlockValue).prod) = 497643265214472763492283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_11
      · exact prime_oneHundredSixtyFourFF_43
      · exact prime_oneHundredSixtyFourFF_61
      · exact prime_oneHundredSixtyFourFF_293
      · exact prime_oneHundredSixtyFourFF_661
      · exact prime_oneHundredSixtyFourFF_636931
      · exact prime_oneHundredSixtyFourFF_69909419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 497643265214472763492283) ^ 248821632607236381746141 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 497643265214472763492283) ^ 45240296837679342135662 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 497643265214472763492283) ^ 11573099191034250313774 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 497643265214472763492283) ^ 8158086314991356778562 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 497643265214472763492283) ^ 1698441178206391684274 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 497643265214472763492283) ^ 752864243894815073362 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 497643265214472763492283) ^ 781314247876885822 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 497643265214472763492283) ^ 7118400815410478 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_524041722391674648201083 : Nat.Prime 524041722391674648201083 := by
  apply lucas_primality 524041722391674648201083 (2 : ZMod 524041722391674648201083)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (197, 1), (190007876139113360479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (197, 1), (190007876139113360479, 1)] : List FactorBlock).map factorBlockValue).prod) = 524041722391674648201083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_197
      · exact prime_oneHundredSixtyFourFF_190007876139113360479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 524041722391674648201083) ^ 262020861195837324100541 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 524041722391674648201083) ^ 74863103198810664028726 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 524041722391674648201083) ^ 2660110265947587046706 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 524041722391674648201083) ^ 2758 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_623382060343832397026233 : Nat.Prime 623382060343832397026233 := by
  apply lucas_primality 623382060343832397026233 (5 : ZMod 623382060343832397026233)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (2361295683120577261463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (2361295683120577261463, 1)] : List FactorBlock).map factorBlockValue).prod) = 623382060343832397026233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_11
      · exact prime_oneHundredSixtyFourFF_2361295683120577261463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 623382060343832397026233) ^ 311691030171916198513116 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 623382060343832397026233) ^ 207794020114610799008744 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 623382060343832397026233) ^ 56671096394893854275112 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 623382060343832397026233) ^ 264 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_1007491654938232674002927 : Nat.Prime 1007491654938232674002927 := by
  apply lucas_primality 1007491654938232674002927 (5 : ZMod 1007491654938232674002927)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1889, 1), (45767, 1), (832394148060743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1889, 1), (45767, 1), (832394148060743, 1)] : List FactorBlock).map factorBlockValue).prod) = 1007491654938232674002927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_1889
      · exact prime_oneHundredSixtyFourFF_45767
      · exact prime_oneHundredSixtyFourFF_832394148060743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1007491654938232674002927) ^ 503745827469116337001463 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1007491654938232674002927) ^ 143927379276890382000418 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1007491654938232674002927) ^ 533346561640144348334 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1007491654938232674002927) ^ 22013495639614409378 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1007491654938232674002927) ^ 1210354082 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_4628924702004509229877129 : Nat.Prime 4628924702004509229877129 := by
  apply lucas_primality 4628924702004509229877129 (19 : ZMod 4628924702004509229877129)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (127, 1), (3541, 1), (300416419, 1), (475876553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (127, 1), (3541, 1), (300416419, 1), (475876553, 1)] : List FactorBlock).map factorBlockValue).prod) = 4628924702004509229877129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_127
      · exact prime_oneHundredSixtyFourFF_3541
      · exact prime_oneHundredSixtyFourFF_300416419
      · exact prime_oneHundredSixtyFourFF_475876553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 4628924702004509229877129) ^ 2314462351002254614938564 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (19 : ZMod 4628924702004509229877129) ^ 1542974900668169743292376 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (19 : ZMod 4628924702004509229877129) ^ 36448226000035505747064 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (19 : ZMod 4628924702004509229877129) ^ 1307236572156031976808 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (19 : ZMod 4628924702004509229877129) ^ 15408361225437912 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (19 : ZMod 4628924702004509229877129) ^ 9727154390824776 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_9475236719584756785997327 : Nat.Prime 9475236719584756785997327 := by
  apply lucas_primality 9475236719584756785997327 (3 : ZMod 9475236719584756785997327)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (313, 1), (22811, 1), (24575799027930583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (313, 1), (22811, 1), (24575799027930583, 1)] : List FactorBlock).map factorBlockValue).prod) = 9475236719584756785997327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_313
      · exact prime_oneHundredSixtyFourFF_22811
      · exact prime_oneHundredSixtyFourFF_24575799027930583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9475236719584756785997327) ^ 4737618359792378392998663 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 9475236719584756785997327) ^ 3158412239861585595332442 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 9475236719584756785997327) ^ 30272321787810724555902 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 9475236719584756785997327) ^ 415380155170082713866 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 9475236719584756785997327) ^ 385551522 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_13163052884783630557492417 : Nat.Prime 13163052884783630557492417 := by
  apply lucas_primality 13163052884783630557492417 (10 : ZMod 13163052884783630557492417)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (2281, 1), (3119, 1), (8837, 1), (539111, 1), (2022701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (2281, 1), (3119, 1), (8837, 1), (539111, 1), (2022701, 1)] : List FactorBlock).map factorBlockValue).prod) = 13163052884783630557492417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_2281
      · exact prime_oneHundredSixtyFourFF_3119
      · exact prime_oneHundredSixtyFourFF_8837
      · exact prime_oneHundredSixtyFourFF_539111
      · exact prime_oneHundredSixtyFourFF_2022701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 13163052884783630557492417) ^ 6581526442391815278746208 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (10 : ZMod 13163052884783630557492417) ^ 4387684294927876852497472 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (10 : ZMod 13163052884783630557492417) ^ 5770737783771867846336 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (10 : ZMod 13163052884783630557492417) ^ 4220279860462850451264 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (10 : ZMod 13163052884783630557492417) ^ 1489538631298362629568 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (10 : ZMod 13163052884783630557492417) ^ 24416220193584680256 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (10 : ZMod 13163052884783630557492417) ^ 6507661233560289216 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_15638955395455950807538579 : Nat.Prime 15638955395455950807538579 := by
  apply lucas_primality 15638955395455950807538579 (2 : ZMod 15638955395455950807538579)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1889, 1), (3709, 1), (187513, 1), (1983975556951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1889, 1), (3709, 1), (187513, 1), (1983975556951, 1)] : List FactorBlock).map factorBlockValue).prod) = 15638955395455950807538579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_1889
      · exact prime_oneHundredSixtyFourFF_3709
      · exact prime_oneHundredSixtyFourFF_187513
      · exact prime_oneHundredSixtyFourFF_1983975556951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15638955395455950807538579) ^ 7819477697727975403769289 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 15638955395455950807538579) ^ 5212985131818650269179526 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 15638955395455950807538579) ^ 8278959976419243413202 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 15638955395455950807538579) ^ 4216488378392006149242 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 15638955395455950807538579) ^ 83401979571848089506 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 15638955395455950807538579) ^ 7882635116478 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_24668163994002910701254873 : Nat.Prime 24668163994002910701254873 := by
  apply lucas_primality 24668163994002910701254873 (3 : ZMod 24668163994002910701254873)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (37, 1), (47, 1), (1463747281, 1), (173054587543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (37, 1), (47, 1), (1463747281, 1), (173054587543, 1)] : List FactorBlock).map factorBlockValue).prod) = 24668163994002910701254873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_37
      · exact prime_oneHundredSixtyFourFF_47
      · exact prime_oneHundredSixtyFourFF_1463747281
      · exact prime_oneHundredSixtyFourFF_173054587543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 24668163994002910701254873) ^ 12334081997001455350627436 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 24668163994002910701254873) ^ 3524023427714701528750696 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 24668163994002910701254873) ^ 666707134973051640574456 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 24668163994002910701254873) ^ 524854553063891717047976 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 24668163994002910701254873) ^ 16852747953287512 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 24668163994002910701254873) ^ 142545565212904 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_52530958816814651344314089 : Nat.Prime 52530958816814651344314089 := by
  apply lucas_primality 52530958816814651344314089 (3 : ZMod 52530958816814651344314089)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (43, 1), (47, 1), (295369972205561217131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (43, 1), (47, 1), (295369972205561217131, 1)] : List FactorBlock).map factorBlockValue).prod) = 52530958816814651344314089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_11
      · exact prime_oneHundredSixtyFourFF_43
      · exact prime_oneHundredSixtyFourFF_47
      · exact prime_oneHundredSixtyFourFF_295369972205561217131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 52530958816814651344314089) ^ 26265479408407325672157044 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 52530958816814651344314089) ^ 4775541710619513758574008 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 52530958816814651344314089) ^ 1221650205042201194053816 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 52530958816814651344314089) ^ 1117679974825843645623704 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 52530958816814651344314089) ^ 177848 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_151123748240734901100439051 : Nat.Prime 151123748240734901100439051 := by
  apply lucas_primality 151123748240734901100439051 (2 : ZMod 151123748240734901100439051)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (1007491654938232674002927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (1007491654938232674002927, 1)] : List FactorBlock).map factorBlockValue).prod) = 151123748240734901100439051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_1007491654938232674002927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 151123748240734901100439051) ^ 75561874120367450550219525 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 151123748240734901100439051) ^ 50374582746911633700146350 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 151123748240734901100439051) ^ 30224749648146980220087810 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 151123748240734901100439051) ^ 150 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_156743548094472819815572597 : Nat.Prime 156743548094472819815572597 := by
  apply lucas_primality 156743548094472819815572597 (2 : ZMod 156743548094472819815572597)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (41, 1), (47, 1), (191, 1), (23143, 1), (5488591, 1), (93130421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (41, 1), (47, 1), (191, 1), (23143, 1), (5488591, 1), (93130421, 1)] : List FactorBlock).map factorBlockValue).prod) = 156743548094472819815572597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_41
      · exact prime_oneHundredSixtyFourFF_47
      · exact prime_oneHundredSixtyFourFF_191
      · exact prime_oneHundredSixtyFourFF_23143
      · exact prime_oneHundredSixtyFourFF_5488591
      · exact prime_oneHundredSixtyFourFF_93130421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 156743548094472819815572597) ^ 78371774047236409907786298 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 156743548094472819815572597) ^ 52247849364824273271857532 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 156743548094472819815572597) ^ 3823013368157873654038356 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 156743548094472819815572597) ^ 3334969108393038719480268 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 156743548094472819815572597) ^ 820646848662161360290956 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 156743548094472819815572597) ^ 6772827554529353144172 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 156743548094472819815572597) ^ 28558066741441076556 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 156743548094472819815572597) ^ 1683054220215248676 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_207370875928195591563490163 : Nat.Prime 207370875928195591563490163 := by
  apply lucas_primality 207370875928195591563490163 (5 : ZMod 207370875928195591563490163)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (19, 1), (739117, 1), (567946754125831019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (19, 1), (739117, 1), (567946754125831019, 1)] : List FactorBlock).map factorBlockValue).prod) = 207370875928195591563490163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_13
      · exact prime_oneHundredSixtyFourFF_19
      · exact prime_oneHundredSixtyFourFF_739117
      · exact prime_oneHundredSixtyFourFF_567946754125831019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 207370875928195591563490163) ^ 103685437964097795781745081 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 207370875928195591563490163) ^ 15951605840630430120268474 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 207370875928195591563490163) ^ 10914256627799767977025798 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 207370875928195591563490163) ^ 280565696538160523386 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 207370875928195591563490163) ^ 365123798 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_285976060461449672731361803 : Nat.Prime 285976060461449672731361803 := by
  apply lucas_primality 285976060461449672731361803 (2 : ZMod 285976060461449672731361803)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (13, 1), (127847857, 1), (869015822385539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (13, 1), (127847857, 1), (869015822385539, 1)] : List FactorBlock).map factorBlockValue).prod) = 285976060461449672731361803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_11
      · exact prime_oneHundredSixtyFourFF_13
      · exact prime_oneHundredSixtyFourFF_127847857
      · exact prime_oneHundredSixtyFourFF_869015822385539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 285976060461449672731361803) ^ 142988030230724836365680901 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 285976060461449672731361803) ^ 95325353487149890910453934 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 285976060461449672731361803) ^ 25997823678313606611941982 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 285976060461449672731361803) ^ 21998158497034590210104754 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 285976060461449672731361803) ^ 2236846726820377386 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 285976060461449672731361803) ^ 329080383918 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_296017967928034928415058477 : Nat.Prime 296017967928034928415058477 := by
  apply lucas_primality 296017967928034928415058477 (5 : ZMod 296017967928034928415058477)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (24668163994002910701254873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (24668163994002910701254873, 1)] : List FactorBlock).map factorBlockValue).prod) = 296017967928034928415058477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_24668163994002910701254873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 296017967928034928415058477) ^ 148008983964017464207529238 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 296017967928034928415058477) ^ 98672655976011642805019492 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 296017967928034928415058477) ^ 12 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_1154117672576564750665852991 : Nat.Prime 1154117672576564750665852991 := by
  apply lucas_primality 1154117672576564750665852991 (14 : ZMod 1154117672576564750665852991)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (17, 1), (97, 1), (1694450239, 1), (842955281741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (17, 1), (97, 1), (1694450239, 1), (842955281741, 1)] : List FactorBlock).map factorBlockValue).prod) = 1154117672576564750665852991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_17
      · exact prime_oneHundredSixtyFourFF_97
      · exact prime_oneHundredSixtyFourFF_1694450239
      · exact prime_oneHundredSixtyFourFF_842955281741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 1154117672576564750665852991) ^ 577058836288282375332926495 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (14 : ZMod 1154117672576564750665852991) ^ 230823534515312950133170598 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (14 : ZMod 1154117672576564750665852991) ^ 164873953225223535809407570 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (14 : ZMod 1154117672576564750665852991) ^ 67889274857444985333285470 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (14 : ZMod 1154117672576564750665852991) ^ 11898120335840873718204670 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (14 : ZMod 1154117672576564750665852991) ^ 681116297199545410 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (14 : ZMod 1154117672576564750665852991) ^ 1369132737614390 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_1189520055170937902526768727 : Nat.Prime 1189520055170937902526768727 := by
  apply lucas_primality 1189520055170937902526768727 (13 : ZMod 1189520055170937902526768727)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (15823, 1), (2960861, 1), (33476693, 1), (126406999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (15823, 1), (2960861, 1), (33476693, 1), (126406999, 1)] : List FactorBlock).map factorBlockValue).prod) = 1189520055170937902526768727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_15823
      · exact prime_oneHundredSixtyFourFF_2960861
      · exact prime_oneHundredSixtyFourFF_33476693
      · exact prime_oneHundredSixtyFourFF_126406999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 1189520055170937902526768727) ^ 594760027585468951263384363 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (13 : ZMod 1189520055170937902526768727) ^ 396506685056979300842256242 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (13 : ZMod 1189520055170937902526768727) ^ 75176645084430127189962 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (13 : ZMod 1189520055170937902526768727) ^ 401748023690047557966 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (13 : ZMod 1189520055170937902526768727) ^ 35532782618968304382 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (13 : ZMod 1189520055170937902526768727) ^ 9410238867951749274 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_6685923068719409590064251807 : Nat.Prime 6685923068719409590064251807 := by
  apply lucas_primality 6685923068719409590064251807 (3 : ZMod 6685923068719409590064251807)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (325925441143, 1), (3418943018211107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (325925441143, 1), (3418943018211107, 1)] : List FactorBlock).map factorBlockValue).prod) = 6685923068719409590064251807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_325925441143
      · exact prime_oneHundredSixtyFourFF_3418943018211107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6685923068719409590064251807) ^ 3342961534359704795032125903 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 6685923068719409590064251807) ^ 2228641022906469863354750602 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 6685923068719409590064251807) ^ 20513658109266642 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (3 : ZMod 6685923068719409590064251807) ^ 1955552646858 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_27698824141837554015980471783 : Nat.Prime 27698824141837554015980471783 := by
  apply lucas_primality 27698824141837554015980471783 (5 : ZMod 27698824141837554015980471783)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (859, 1), (343036486536021029103367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (859, 1), (343036486536021029103367, 1)] : List FactorBlock).map factorBlockValue).prod) = 27698824141837554015980471783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_47
      · exact prime_oneHundredSixtyFourFF_859
      · exact prime_oneHundredSixtyFourFF_343036486536021029103367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 27698824141837554015980471783) ^ 13849412070918777007990235891 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 27698824141837554015980471783) ^ 589336683868884127999584506 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 27698824141837554015980471783) ^ 32245429734385976735716498 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (5 : ZMod 27698824141837554015980471783) ^ 80746 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_38778353798572575622372660483 : Nat.Prime 38778353798572575622372660483 := by
  apply lucas_primality 38778353798572575622372660483 (2 : ZMod 38778353798572575622372660483)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (491, 1), (13163052884783630557492417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (491, 1), (13163052884783630557492417, 1)] : List FactorBlock).map factorBlockValue).prod) = 38778353798572575622372660483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_491
      · exact prime_oneHundredSixtyFourFF_13163052884783630557492417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 38778353798572575622372660483) ^ 19389176899286287811186330241 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 38778353798572575622372660483) ^ 12926117932857525207457553494 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 38778353798572575622372660483) ^ 78978317308701783344954502 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 38778353798572575622372660483) ^ 2946 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_96945884496431439055931651231 : Nat.Prime 96945884496431439055931651231 := by
  apply lucas_primality 96945884496431439055931651231 (14 : ZMod 96945884496431439055931651231)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (11, 2), (23, 1), (497643265214472763492283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (11, 2), (23, 1), (497643265214472763492283, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431439055931651231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_7
      · exact prime_oneHundredSixtyFourFF_11
      · exact prime_oneHundredSixtyFourFF_23
      · exact prime_oneHundredSixtyFourFF_497643265214472763492283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 96945884496431439055931651231) ^ 48472942248215719527965825615 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (14 : ZMod 96945884496431439055931651231) ^ 19389176899286287811186330246 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (14 : ZMod 96945884496431439055931651231) ^ 13849412070918777007990235890 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (14 : ZMod 96945884496431439055931651231) ^ 8813262226948312641448331930 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (14 : ZMod 96945884496431439055931651231) ^ 4215038456366584306779637010 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (14 : ZMod 96945884496431439055931651231) ^ 194810 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_193891768992862878111863302429 : Nat.Prime 193891768992862878111863302429 := by
  apply lucas_primality 193891768992862878111863302429 (6 : ZMod 193891768992862878111863302429)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1309677463, 1), (12337119537096215963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1309677463, 1), (12337119537096215963, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_1309677463
      · exact prime_oneHundredSixtyFourFF_12337119537096215963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 193891768992862878111863302429) ^ 96945884496431439055931651214 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 193891768992862878111863302429) ^ 64630589664287626037287767476 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 193891768992862878111863302429) ^ 148045434445154591556 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (6 : ZMod 193891768992862878111863302429) ^ 15716129556 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_193891768992862878111863302451 : Nat.Prime 193891768992862878111863302451 := by
  apply lucas_primality 193891768992862878111863302451 (2 : ZMod 193891768992862878111863302451)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (1336729, 1), (2900988442576810679081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (1336729, 1), (2900988442576810679081, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_5
      · exact prime_oneHundredSixtyFourFF_1336729
      · exact prime_oneHundredSixtyFourFF_2900988442576810679081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 193891768992862878111863302451) ^ 96945884496431439055931651225 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 193891768992862878111863302451) ^ 38778353798572575622372660490 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 193891768992862878111863302451) ^ 145049422128840533954050 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (2 : ZMod 193891768992862878111863302451) ^ 66836450 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFourFF_193891768992862878111863302459 : Nat.Prime 193891768992862878111863302459 := by
  apply lucas_primality 193891768992862878111863302459 (10 : ZMod 193891768992862878111863302459)
  · rw [← oneHundredSixtyFourFFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (13, 1), (19, 1), (2797, 1), (2921563, 1), (1778938514261231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (13, 1), (19, 1), (2797, 1), (2921563, 1), (1778938514261231, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFourFF_2
      · exact prime_oneHundredSixtyFourFF_3
      · exact prime_oneHundredSixtyFourFF_13
      · exact prime_oneHundredSixtyFourFF_19
      · exact prime_oneHundredSixtyFourFF_2797
      · exact prime_oneHundredSixtyFourFF_2921563
      · exact prime_oneHundredSixtyFourFF_1778938514261231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 193891768992862878111863302459) ^ 96945884496431439055931651229 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (10 : ZMod 193891768992862878111863302459) ^ 64630589664287626037287767486 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (10 : ZMod 193891768992862878111863302459) ^ 14914751460989452162451023266 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (10 : ZMod 193891768992862878111863302459) ^ 10204829946992783058519121182 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (10 : ZMod 193891768992862878111863302459) ^ 69321333211606320383218914 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (10 : ZMod 193891768992862878111863302459) ^ 66365766883295988521166 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide
    · change (10 : ZMod 193891768992862878111863302459) ^ 108992957001318 ≠ 1
      rw [← oneHundredSixtyFourFFFastPow_eq_pow]
      decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302400 : Nat.totient 193891768992862878111863302400 = 75664639013442998702653440000 := by
  rw [← show ((([(2, 8), (5, 2), (41, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302400 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_5, prime_oneHundredSixtyFourFF_41, prime_oneHundredSixtyFourFF_171401, prime_oneHundredSixtyFourFF_714027719, prime_oneHundredSixtyFourFF_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302401 : Nat.totient 193891768992862878111863302401 = 122116850842008345457933537488 := by
  rw [← show ((([(3, 1), (19, 1), (359, 1), (9475236719584756785997327, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302401 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_3, prime_oneHundredSixtyFourFF_19, prime_oneHundredSixtyFourFF_359, prime_oneHundredSixtyFourFF_9475236719584756785997327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302402 : Nat.totient 193891768992862878111863302402 = 95617858372219338825403451520 := by
  rw [← show ((([(2, 1), (73, 1), (309250261, 1), (4294340159084324117, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302402 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_73, prime_oneHundredSixtyFourFF_309250261, prime_oneHundredSixtyFourFF_4294340159084324117]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302403 : Nat.totient 193891768992862878111863302403 = 187205845924143468521799050568 := by
  rw [← show ((([(29, 1), (6685923068719409590064251807, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302403 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_29, prime_oneHundredSixtyFourFF_6685923068719409590064251807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302404 : Nat.totient 193891768992862878111863302404 = 55397606526223623977360235264 := by
  rw [← show ((([(2, 2), (3, 3), (7, 1), (1326653, 1), (193321534648399602553, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302404 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_3, prime_oneHundredSixtyFourFF_7, prime_oneHundredSixtyFourFF_1326653, prime_oneHundredSixtyFourFF_193321534648399602553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302405 : Nat.totient 193891768992862878111863302405 = 132717360594045178600633703680 := by
  rw [← show ((([(5, 1), (11, 1), (17, 1), (207370875928195591563490163, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302405 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_5, prime_oneHundredSixtyFourFF_11, prime_oneHundredSixtyFourFF_17, prime_oneHundredSixtyFourFF_207370875928195591563490163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302406 : Nat.totient 193891768992862878111863302406 = 89488491917630644646398692864 := by
  rw [← show ((([(2, 1), (13, 1), (5312953, 1), (31601290729, 1), (44416591663, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302406 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_13, prime_oneHundredSixtyFourFF_5312953, prime_oneHundredSixtyFourFF_31601290729, prime_oneHundredSixtyFourFF_44416591663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302407 : Nat.totient 193891768992862878111863302407 = 129261179325846543083827452792 := by
  rw [← show ((([(3, 1), (47370820507, 1), (1364354448003220567, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302407 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_3, prime_oneHundredSixtyFourFF_47370820507, prime_oneHundredSixtyFourFF_1364354448003220567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302408 : Nat.totient 193891768992862878111863302408 = 95247738588602089082395506432 := by
  rw [← show ((([(2, 3), (59, 1), (1733, 1), (39668467, 1), (5975488216114349, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302408 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_59, prime_oneHundredSixtyFourFF_1733, prime_oneHundredSixtyFourFF_39668467, prime_oneHundredSixtyFourFF_5975488216114349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302409 : Nat.totient 193891768992862878111863302409 = 189761598818196832773354258432 := by
  rw [← show ((([(83, 1), (109, 1), (5167, 1), (13644685697, 1), (303985441553, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302409 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_83, prime_oneHundredSixtyFourFF_109, prime_oneHundredSixtyFourFF_5167, prime_oneHundredSixtyFourFF_13644685697, prime_oneHundredSixtyFourFF_303985441553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302410 : Nat.totient 193891768992862878111863302410 = 51599167308351831785370270720 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (491, 1), (13163052884783630557492417, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302410 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_3, prime_oneHundredSixtyFourFF_5, prime_oneHundredSixtyFourFF_491, prime_oneHundredSixtyFourFF_13163052884783630557492417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302411 : Nat.totient 193891768992862878111863302411 = 162555677788250875376940026400 := by
  rw [← show ((([(7, 1), (79, 1), (107, 1), (11109611, 1), (294952180746895531, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302411 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_7, prime_oneHundredSixtyFourFF_79, prime_oneHundredSixtyFourFF_107, prime_oneHundredSixtyFourFF_11109611, prime_oneHundredSixtyFourFF_294952180746895531]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302412 : Nat.totient 193891768992862878111863302412 = 96941550516081060875445490176 := by
  rw [← show ((([(2, 2), (22369, 1), (2352041639, 1), (921314287658533, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302412 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_22369, prime_oneHundredSixtyFourFF_2352041639, prime_oneHundredSixtyFourFF_921314287658533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302413 : Nat.totient 193891768992862878111863302413 = 129115235312830389982419106560 := by
  rw [← show ((([(3, 2), (1063, 1), (5791, 1), (67559, 1), (974969, 1), (53131981699, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302413 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_3, prime_oneHundredSixtyFourFF_1063, prime_oneHundredSixtyFourFF_5791, prime_oneHundredSixtyFourFF_67559, prime_oneHundredSixtyFourFF_974969, prime_oneHundredSixtyFourFF_53131981699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302414 : Nat.totient 193891768992862878111863302414 = 92727672448624267905896036640 := by
  rw [← show ((([(2, 1), (23, 1), (30427, 1), (736277, 1), (188148678680386871, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302414 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_23, prime_oneHundredSixtyFourFF_30427, prime_oneHundredSixtyFourFF_736277, prime_oneHundredSixtyFourFF_188148678680386871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302415 : Nat.totient 193891768992862878111863302415 = 155113415194290302489490641928 := by
  rw [← show ((([(5, 1), (38778353798572575622372660483, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302415 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_5, prime_oneHundredSixtyFourFF_38778353798572575622372660483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302416 : Nat.totient 193891768992862878111863302416 = 57873527091198768303676523520 := by
  rw [← show ((([(2, 4), (3, 1), (11, 1), (67, 1), (12547, 1), (436828283214730158953, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302416 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_3, prime_oneHundredSixtyFourFF_11, prime_oneHundredSixtyFourFF_67, prime_oneHundredSixtyFourFF_12547, prime_oneHundredSixtyFourFF_436828283214730158953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302417 : Nat.totient 193891768992862878111863302417 = 191892845160131213454886153728 := by
  rw [← show ((([(97, 1), (6004067, 1), (25064989, 1), (13282339919447, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302417 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_97, prime_oneHundredSixtyFourFF_6004067, prime_oneHundredSixtyFourFF_25064989, prime_oneHundredSixtyFourFF_13282339919447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302418 : Nat.totient 193891768992862878111863302418 = 82538777555914039898626539360 := by
  rw [← show ((([(2, 1), (7, 2), (149, 1), (194763479, 1), (68177254042191571, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302418 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_7, prime_oneHundredSixtyFourFF_149, prime_oneHundredSixtyFourFF_194763479, prime_oneHundredSixtyFourFF_68177254042191571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302419 : Nat.totient 193891768992862878111863302419 = 116412724378976173049981159808 := by
  rw [← show ((([(3, 1), (13, 1), (53, 1), (179, 1), (524041722391674648201083, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302419 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_3, prime_oneHundredSixtyFourFF_13, prime_oneHundredSixtyFourFF_53, prime_oneHundredSixtyFourFF_179, prime_oneHundredSixtyFourFF_524041722391674648201083]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302420 : Nat.totient 193891768992862878111863302420 = 71068727784699485501257175040 := by
  rw [← show ((([(2, 2), (5, 1), (19, 1), (43, 1), (103, 1), (164627, 1), (498521, 1), (1403736441413, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302420 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_5, prime_oneHundredSixtyFourFF_19, prime_oneHundredSixtyFourFF_43, prime_oneHundredSixtyFourFF_103, prime_oneHundredSixtyFourFF_164627, prime_oneHundredSixtyFourFF_498521, prime_oneHundredSixtyFourFF_1403736441413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302421 : Nat.totient 193891768992862878111863302421 = 193855783232673480572613770032 := by
  rw [← show ((([(5399, 1), (2647343, 1), (13565500811951685053, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302421 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_5399, prime_oneHundredSixtyFourFF_2647343, prime_oneHundredSixtyFourFF_13565500811951685053]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302422 : Nat.totient 193891768992862878111863302422 = 60226525021971367431652761600 := by
  rw [← show ((([(2, 1), (3, 2), (17, 1), (101, 1), (852412270823, 1), (7359814694369, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302422 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_3, prime_oneHundredSixtyFourFF_17, prime_oneHundredSixtyFourFF_101, prime_oneHundredSixtyFourFF_852412270823, prime_oneHundredSixtyFourFF_7359814694369]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302423 : Nat.totient 193891768992862878111863302423 = 193887140068160873602633383408 := by
  rw [← show ((([(41887, 1), (4628924702004509229877129, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302423 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_41887, prime_oneHundredSixtyFourFF_4628924702004509229877129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302424 : Nat.totient 193891768992862878111863302424 = 93818559438509113334594592000 := by
  rw [← show ((([(2, 3), (31, 1), (2439301, 1), (320510527058681839513, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302424 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_31, prime_oneHundredSixtyFourFF_2439301, prime_oneHundredSixtyFourFF_320510527058681839513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302425 : Nat.totient 193891768992862878111863302425 = 88636237253794554465254668800 := by
  rw [← show ((([(3, 1), (5, 2), (7, 1), (1038269493017, 1), (355705005018821, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302425 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_3, prime_oneHundredSixtyFourFF_5, prime_oneHundredSixtyFourFF_7, prime_oneHundredSixtyFourFF_1038269493017, prime_oneHundredSixtyFourFF_355705005018821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302426 : Nat.totient 193891768992862878111863302426 = 96510935370978836162156078208 := by
  rw [← show ((([(2, 1), (223, 1), (450529, 1), (964943229083469351539, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302426 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_223, prime_oneHundredSixtyFourFF_450529, prime_oneHundredSixtyFourFF_964943229083469351539]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302427 : Nat.totient 193891768992862878111863302427 = 172512490029497168729592883200 := by
  rw [← show ((([(11, 1), (47, 1), (104123, 1), (226649, 1), (14356061, 1), (1106962873, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302427 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_11, prime_oneHundredSixtyFourFF_47, prime_oneHundredSixtyFourFF_104123, prime_oneHundredSixtyFourFF_226649, prime_oneHundredSixtyFourFF_14356061, prime_oneHundredSixtyFourFF_1106962873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302428 : Nat.totient 193891768992862878111863302428 = 64630589614939147883664193776 := by
  rw [← show ((([(2, 2), (3, 1), (1309677463, 1), (12337119537096215963, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302428 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_3, prime_oneHundredSixtyFourFF_1309677463, prime_oneHundredSixtyFourFF_12337119537096215963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302429 : Nat.totient 193891768992862878111863302429 = 193891768992862878111863302428 := by
  rw [← show ((([(193891768992862878111863302429, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302429 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_193891768992862878111863302429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302430 : Nat.totient 193891768992862878111863302430 = 75460400676633428927359289856 := by
  rw [← show ((([(2, 1), (5, 1), (37, 1), (419953, 1), (1247834419777495551863, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302430 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_5, prime_oneHundredSixtyFourFF_37, prime_oneHundredSixtyFourFF_419953, prime_oneHundredSixtyFourFF_1247834419777495551863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302431 : Nat.totient 193891768992862878111863302431 = 129124678784314951538158634496 := by
  rw [← show ((([(3, 6), (947, 1), (25285133, 1), (11107507708411489, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302431 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_3, prime_oneHundredSixtyFourFF_947, prime_oneHundredSixtyFourFF_25285133, prime_oneHundredSixtyFourFF_11107507708411489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302432 : Nat.totient 193891768992862878111863302432 = 73834406294833035102828036096 := by
  rw [← show ((([(2, 5), (7, 1), (13, 1), (29, 1), (337, 1), (13963, 1), (487934319167696389, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302432 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_7, prime_oneHundredSixtyFourFF_13, prime_oneHundredSixtyFourFF_29, prime_oneHundredSixtyFourFF_337, prime_oneHundredSixtyFourFF_13963, prime_oneHundredSixtyFourFF_487934319167696389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302433 : Nat.totient 193891768992862878111863302433 = 193740645244622143210762862100 := by
  rw [← show ((([(1283, 1), (151123748240734901100439051, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302433 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_1283, prime_oneHundredSixtyFourFF_151123748240734901100439051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302434 : Nat.totient 193891768992862878111863302434 = 64058637543364726691825043648 := by
  rw [← show ((([(2, 1), (3, 1), (113, 1), (285976060461449672731361803, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302434 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_3, prime_oneHundredSixtyFourFF_113, prime_oneHundredSixtyFourFF_285976060461449672731361803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302435 : Nat.totient 193891768992862878111863302435 = 153929343322578162775830407520 := by
  rw [← show ((([(5, 1), (131, 1), (296017967928034928415058477, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302435 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_5, prime_oneHundredSixtyFourFF_131, prime_oneHundredSixtyFourFF_296017967928034928415058477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302436 : Nat.totient 193891768992862878111863302436 = 96945884496429506044308647208 := by
  rw [← show ((([(2, 2), (53066401233983, 1), (913439410268023, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302436 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_53066401233983, prime_oneHundredSixtyFourFF_913439410268023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302437 : Nat.totient 193891768992862878111863302437 = 123251090275701885277858581504 := by
  rw [← show ((([(3, 1), (23, 1), (317, 1), (62383637, 1), (261919789, 1), (542515333, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302437 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_3, prime_oneHundredSixtyFourFF_23, prime_oneHundredSixtyFourFF_317, prime_oneHundredSixtyFourFF_62383637, prime_oneHundredSixtyFourFF_261919789, prime_oneHundredSixtyFourFF_542515333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302438 : Nat.totient 193891768992862878111863302438 = 88102200200024758925988754560 := by
  rw [← show ((([(2, 1), (11, 1), (2897, 1), (2259666419, 1), (1346306260670803, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302438 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_11, prime_oneHundredSixtyFourFF_2897, prime_oneHundredSixtyFourFF_2259666419, prime_oneHundredSixtyFourFF_1346306260670803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302439 : Nat.totient 193891768992862878111863302439 = 146096617486504772251119513600 := by
  rw [← show ((([(7, 1), (17, 1), (19, 1), (71, 1), (208889, 1), (5782090582925066821, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302439 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_7, prime_oneHundredSixtyFourFF_17, prime_oneHundredSixtyFourFF_19, prime_oneHundredSixtyFourFF_71, prime_oneHundredSixtyFourFF_208889, prime_oneHundredSixtyFourFF_5782090582925066821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302440 : Nat.totient 193891768992862878111863302440 = 51681166830840801415660830720 := by
  rw [← show ((([(2, 3), (3, 2), (5, 1), (2221, 1), (2096209, 1), (140866157, 1), (821234273, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302440 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_3, prime_oneHundredSixtyFourFF_5, prime_oneHundredSixtyFourFF_2221, prime_oneHundredSixtyFourFF_2096209, prime_oneHundredSixtyFourFF_140866157, prime_oneHundredSixtyFourFF_821234273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302441 : Nat.totient 193891768992862878111863302441 = 189137683166101479865304121600 := by
  rw [← show ((([(41, 1), (7561, 1), (2416168199, 1), (258862483991359, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302441 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_41, prime_oneHundredSixtyFourFF_7561, prime_oneHundredSixtyFourFF_2416168199, prime_oneHundredSixtyFourFF_258862483991359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302442 : Nat.totient 193891768992862878111863302442 = 96930245541035983105124106444 := by
  rw [← show ((([(2, 1), (6199, 1), (15638955395455950807538579, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302442 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_6199, prime_oneHundredSixtyFourFF_15638955395455950807538579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302443 : Nat.totient 193891768992862878111863302443 = 129261179328057430777990826984 := by
  rw [← show ((([(3, 1), (249625314383, 1), (258910398667039607, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302443 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_3, prime_oneHundredSixtyFourFF_249625314383, prime_oneHundredSixtyFourFF_258910398667039607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302444 : Nat.totient 193891768992862878111863302444 = 96323292108109198449967104000 := by
  rw [← show ((([(2, 2), (281, 1), (349, 1), (125711, 1), (3248689, 1), (1210281000961, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302444 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_281, prime_oneHundredSixtyFourFF_349, prime_oneHundredSixtyFourFF_125711, prime_oneHundredSixtyFourFF_3248689, prime_oneHundredSixtyFourFF_1210281000961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302445 : Nat.totient 193891768992862878111863302445 = 141379529072135045147854497792 := by
  rw [← show ((([(5, 1), (13, 1), (167, 1), (199, 1), (617, 1), (230268887, 1), (631765699379, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302445 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_5, prime_oneHundredSixtyFourFF_13, prime_oneHundredSixtyFourFF_167, prime_oneHundredSixtyFourFF_199, prime_oneHundredSixtyFourFF_617, prime_oneHundredSixtyFourFF_230268887, prime_oneHundredSixtyFourFF_631765699379]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302446 : Nat.totient 193891768992862878111863302446 = 54961446324260585531671250400 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (127, 1), (12420845651, 1), (2926544933989319, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302446 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_3, prime_oneHundredSixtyFourFF_7, prime_oneHundredSixtyFourFF_127, prime_oneHundredSixtyFourFF_12420845651, prime_oneHundredSixtyFourFF_2926544933989319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302447 : Nat.totient 193891768992862878111863302447 = 190713183904721117657390352480 := by
  rw [← show ((([(61, 1), (6065483, 1), (3503121703, 1), (149592190823, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302447 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_61, prime_oneHundredSixtyFourFF_6065483, prime_oneHundredSixtyFourFF_3503121703, prime_oneHundredSixtyFourFF_149592190823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302448 : Nat.totient 193891768992862878111863302448 = 96945713425823664530314747200 := by
  rw [← show ((([(2, 4), (566701, 1), (21383825971815701546303, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302448 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_566701, prime_oneHundredSixtyFourFF_21383825971815701546303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302449 : Nat.totient 193891768992862878111863302449 = 117389879931214441040186327040 := by
  rw [← show ((([(3, 2), (11, 1), (977, 1), (34681573, 1), (37742767, 1), (1531429793, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302449 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_3, prime_oneHundredSixtyFourFF_11, prime_oneHundredSixtyFourFF_977, prime_oneHundredSixtyFourFF_34681573, prime_oneHundredSixtyFourFF_37742767, prime_oneHundredSixtyFourFF_1531429793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302450 : Nat.totient 193891768992862878111863302450 = 77556649577376299708505004800 := by
  rw [← show ((([(2, 1), (5, 2), (1336729, 1), (2900988442576810679081, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302450 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_5, prime_oneHundredSixtyFourFF_1336729, prime_oneHundredSixtyFourFF_2900988442576810679081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302451 : Nat.totient 193891768992862878111863302451 = 193891768992862878111863302450 := by
  rw [← show ((([(193891768992862878111863302451, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302451 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_193891768992862878111863302451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302452 : Nat.totient 193891768992862878111863302452 = 64630589664216947758014218976 := by
  rw [← show ((([(2, 2), (3, 1), (914480876299, 1), (17668655337510829, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302452 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_3, prime_oneHundredSixtyFourFF_914480876299, prime_oneHundredSixtyFourFF_17668655337510829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302453 : Nat.totient 193891768992862878111863302453 = 165911659531607756366726353920 := by
  rw [← show ((([(7, 1), (593, 1), (203221, 1), (963239, 1), (4674443, 1), (51047459, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302453 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_7, prime_oneHundredSixtyFourFF_593, prime_oneHundredSixtyFourFF_203221, prime_oneHundredSixtyFourFF_963239, prime_oneHundredSixtyFourFF_4674443, prime_oneHundredSixtyFourFF_51047459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302454 : Nat.totient 193891768992862878111863302454 = 96943921597675690524417876480 := by
  rw [← show ((([(2, 1), (49393, 1), (632230331, 1), (3104478420411569, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302454 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_49393, prime_oneHundredSixtyFourFF_632230331, prime_oneHundredSixtyFourFF_3104478420411569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302455 : Nat.totient 193891768992862878111863302455 = 99955849470103007152037222400 := by
  rw [← show ((([(3, 1), (5, 1), (31, 2), (853, 1), (39231469, 1), (401939904288361, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302455 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_3, prime_oneHundredSixtyFourFF_5, prime_oneHundredSixtyFourFF_31, prime_oneHundredSixtyFourFF_853, prime_oneHundredSixtyFourFF_39231469, prime_oneHundredSixtyFourFF_401939904288361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302456 : Nat.totient 193891768992862878111863302456 = 91203288956544055014525846528 := by
  rw [← show ((([(2, 3), (17, 1), (2287, 1), (623382060343832397026233, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302456 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_17, prime_oneHundredSixtyFourFF_2287, prime_oneHundredSixtyFourFF_623382060343832397026233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302457 : Nat.totient 193891768992862878111863302457 = 192326231420493869810967640512 := by
  rw [← show ((([(173, 1), (443, 1), (19979, 1), (126629763789109058197, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302457 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_173, prime_oneHundredSixtyFourFF_443, prime_oneHundredSixtyFourFF_19979, prime_oneHundredSixtyFourFF_126629763789109058197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302458 : Nat.totient 193891768992862878111863302458 = 56498831801085209813855988480 := by
  rw [← show ((([(2, 1), (3, 3), (13, 1), (19, 1), (2797, 1), (2921563, 1), (1778938514261231, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302458 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_3, prime_oneHundredSixtyFourFF_13, prime_oneHundredSixtyFourFF_19, prime_oneHundredSixtyFourFF_2797, prime_oneHundredSixtyFourFF_2921563, prime_oneHundredSixtyFourFF_1778938514261231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302459 : Nat.totient 193891768992862878111863302459 = 193891768992862878111863302458 := by
  rw [← show ((([(193891768992862878111863302459, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302459 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_193891768992862878111863302459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302460 : Nat.totient 193891768992862878111863302460 = 57806241687313156207263477120 := by
  rw [← show ((([(2, 2), (5, 1), (7, 1), (11, 2), (23, 1), (497643265214472763492283, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302460 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_5, prime_oneHundredSixtyFourFF_7, prime_oneHundredSixtyFourFF_11, prime_oneHundredSixtyFourFF_23, prime_oneHundredSixtyFourFF_497643265214472763492283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302461 : Nat.totient 193891768992862878111863302461 = 123709023864277519237162758144 := by
  rw [← show ((([(3, 1), (29, 1), (193, 1), (277, 1), (41687230371793828461023, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302461 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_3, prime_oneHundredSixtyFourFF_29, prime_oneHundredSixtyFourFF_193, prime_oneHundredSixtyFourFF_277, prime_oneHundredSixtyFourFF_41687230371793828461023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302462 : Nat.totient 193891768992862878111863302462 = 96945884496431439055931651230 := by
  rw [← show ((([(2, 1), (96945884496431439055931651231, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302462 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_96945884496431439055931651231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302463 : Nat.totient 193891768992862878111863302463 = 189247287980285285257046080800 := by
  rw [← show ((([(43, 1), (1399, 1), (2208487759, 1), (1459412986536101, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302463 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_43, prime_oneHundredSixtyFourFF_1399, prime_oneHundredSixtyFourFF_2208487759, prime_oneHundredSixtyFourFF_1459412986536101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302464 : Nat.totient 193891768992862878111863302464 = 64630585354524607207401492480 := by
  rw [← show ((([(2, 6), (3, 1), (14996321, 1), (67340047169201976727, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302464 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_3, prime_oneHundredSixtyFourFF_14996321, prime_oneHundredSixtyFourFF_67340047169201976727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302465 : Nat.totient 193891768992862878111863302465 = 153370565428994298874643049984 := by
  rw [← show ((([(5, 1), (89, 1), (82087267, 1), (291155483, 1), (18230500517, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302465 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_5, prime_oneHundredSixtyFourFF_89, prime_oneHundredSixtyFourFF_82087267, prime_oneHundredSixtyFourFF_291155483, prime_oneHundredSixtyFourFF_18230500517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302466 : Nat.totient 193891768992862878111863302466 = 96944856158016939239622685440 := by
  rw [← show ((([(2, 1), (97003, 1), (5646349, 1), (8248369, 1), (21458947231, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302466 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_97003, prime_oneHundredSixtyFourFF_5646349, prime_oneHundredSixtyFourFF_8248369, prime_oneHundredSixtyFourFF_21458947231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302467 : Nat.totient 193891768992862878111863302467 = 105973690246815802621381549056 := by
  rw [← show ((([(3, 2), (7, 2), (37, 1), (59, 1), (17233577, 1), (11686692549455557, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302467 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_3, prime_oneHundredSixtyFourFF_7, prime_oneHundredSixtyFourFF_37, prime_oneHundredSixtyFourFF_59, prime_oneHundredSixtyFourFF_17233577, prime_oneHundredSixtyFourFF_11686692549455557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302468 : Nat.totient 193891768992862878111863302468 = 96168245403091350821568768000 := by
  rw [← show ((([(2, 2), (139, 1), (1201, 1), (2070643, 1), (140228518397647921, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302468 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_139, prime_oneHundredSixtyFourFF_1201, prime_oneHundredSixtyFourFF_2070643, prime_oneHundredSixtyFourFF_140228518397647921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302469 : Nat.totient 193891768992862878111863302469 = 193891766180886789922198296256 := by
  rw [← show ((([(129862517, 1), (147009893, 1), (10156147401149, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302469 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_129862517, prime_oneHundredSixtyFourFF_147009893, prime_oneHundredSixtyFourFF_10156147401149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302470 : Nat.totient 193891768992862878111863302470 = 51704471686433737390322273280 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (1149081121, 1), (5624545428789411469, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302470 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_3, prime_oneHundredSixtyFourFF_5, prime_oneHundredSixtyFourFF_1149081121, prime_oneHundredSixtyFourFF_5624545428789411469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302471 : Nat.totient 193891768992862878111863302471 = 162703873970851927636863129600 := by
  rw [← show ((([(11, 1), (13, 1), (64937, 1), (20880029820496582229281, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302471 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_11, prime_oneHundredSixtyFourFF_13, prime_oneHundredSixtyFourFF_64937, prime_oneHundredSixtyFourFF_20880029820496582229281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302472 : Nat.totient 193891768992862878111863302472 = 94891110427629495552041015040 := by
  rw [← show ((([(2, 3), (53, 1), (811, 1), (877, 1), (642943883070206397899, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302472 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_53, prime_oneHundredSixtyFourFF_811, prime_oneHundredSixtyFourFF_877, prime_oneHundredSixtyFourFF_642943883070206397899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302473 : Nat.totient 193891768992862878111863302473 = 121654772126731893731368574976 := by
  rw [← show ((([(3, 1), (17, 1), (43319, 1), (19563937889, 1), (4485950726053, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302473 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_3, prime_oneHundredSixtyFourFF_17, prime_oneHundredSixtyFourFF_43319, prime_oneHundredSixtyFourFF_19563937889, prime_oneHundredSixtyFourFF_4485950726053]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302474 : Nat.totient 193891768992862878111863302474 = 81233784303622067859909895728 := by
  rw [← show ((([(2, 1), (7, 1), (47, 1), (859, 1), (343036486536021029103367, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302474 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_7, prime_oneHundredSixtyFourFF_47, prime_oneHundredSixtyFourFF_859, prime_oneHundredSixtyFourFF_343036486536021029103367]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302475 : Nat.totient 193891768992862878111863302475 = 152900699781080766301740748800 := by
  rw [← show ((([(5, 2), (73, 1), (1741, 1), (1064016167, 1), (57352123987729, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302475 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_5, prime_oneHundredSixtyFourFF_73, prime_oneHundredSixtyFourFF_1741, prime_oneHundredSixtyFourFF_1064016167, prime_oneHundredSixtyFourFF_57352123987729]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302476 : Nat.totient 193891768992862878111863302476 = 64629603278223853187790654336 := by
  rw [← show ((([(2, 2), (3, 2), (108739, 1), (166189, 1), (20697107, 1), (14399904703, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302476 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_3, prime_oneHundredSixtyFourFF_108739, prime_oneHundredSixtyFourFF_166189, prime_oneHundredSixtyFourFF_20697107, prime_oneHundredSixtyFourFF_14399904703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302477 : Nat.totient 193891768992862878111863302477 = 183686939045850081389529910320 := by
  rw [← show ((([(19, 1), (9255115388171, 1), (1102615096515773, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302477 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_19, prime_oneHundredSixtyFourFF_9255115388171, prime_oneHundredSixtyFourFF_1102615096515773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302478 : Nat.totient 193891768992862878111863302478 = 96945884496385544876093472280 := by
  rw [← show ((([(2, 1), (2112475860611, 1), (45892067362318349, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302478 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_2112475860611, prime_oneHundredSixtyFourFF_45892067362318349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302479 : Nat.totient 193891768992862878111863302479 = 129261140583098365914027588000 := by
  rw [← show ((([(3, 1), (4576063, 1), (12312661, 1), (1147081303111951, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302479 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_3, prime_oneHundredSixtyFourFF_4576063, prime_oneHundredSixtyFourFF_12312661, prime_oneHundredSixtyFourFF_1147081303111951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302480 : Nat.totient 193891768992862878111863302480 = 77528617384563916185900916736 := by
  rw [← show ((([(2, 4), (5, 1), (3137, 1), (23027, 1), (33551929945480087019, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302480 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_5, prime_oneHundredSixtyFourFF_3137, prime_oneHundredSixtyFourFF_23027, prime_oneHundredSixtyFourFF_33551929945480087019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302481 : Nat.totient 193891768992862878111863302481 = 166192944851025324095882830692 := by
  rw [← show ((([(7, 1), (27698824141837554015980471783, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302481 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_7, prime_oneHundredSixtyFourFF_27698824141837554015980471783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302482 : Nat.totient 193891768992862878111863302482 = 57196870799651649463672320000 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (41, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302482 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_3, prime_oneHundredSixtyFourFF_11, prime_oneHundredSixtyFourFF_41, prime_oneHundredSixtyFourFF_461, prime_oneHundredSixtyFourFF_69997, prime_oneHundredSixtyFourFF_2220502305087140441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302483 : Nat.totient 193891768992862878111863302483 = 182693595564929629504242784800 := by
  rw [← show ((([(23, 1), (67, 1), (15805613, 1), (7960592447355846451, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302483 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_23, prime_oneHundredSixtyFourFF_67, prime_oneHundredSixtyFourFF_15805613, prime_oneHundredSixtyFourFF_7960592447355846451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302484 : Nat.totient 193891768992862878111863302484 = 88825151537332519283458283520 := by
  rw [← show ((([(2, 2), (13, 1), (137, 1), (10139, 1), (63689, 1), (42147896915954971, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302484 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_13, prime_oneHundredSixtyFourFF_137, prime_oneHundredSixtyFourFF_10139, prime_oneHundredSixtyFourFF_63689, prime_oneHundredSixtyFourFF_42147896915954971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302485 : Nat.totient 193891768992862878111863302485 = 103382637448242328293682108800 := by
  rw [← show ((([(3, 3), (5, 1), (3931, 1), (365361314137130083028281, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302485 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_3, prime_oneHundredSixtyFourFF_5, prime_oneHundredSixtyFourFF_3931, prime_oneHundredSixtyFourFF_365361314137130083028281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302486 : Nat.totient 193891768992862878111863302486 = 93074168702128353178005756000 := by
  rw [← show ((([(2, 1), (31, 1), (151, 1), (757, 1), (27358662169937787530279, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302486 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_31, prime_oneHundredSixtyFourFF_151, prime_oneHundredSixtyFourFF_757, prime_oneHundredSixtyFourFF_27358662169937787530279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302487 : Nat.totient 193891768992862878111863302487 = 193761552893231933256364997760 := by
  rw [← show ((([(1489, 1), (85932246011, 1), (1515334503875653, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302487 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_1489, prime_oneHundredSixtyFourFF_85932246011, prime_oneHundredSixtyFourFF_1515334503875653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302488 : Nat.totient 193891768992862878111863302488 = 55397648283675108031960943520 := by
  rw [← show ((([(2, 3), (3, 1), (7, 1), (1154117672576564750665852991, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302488 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_3, prime_oneHundredSixtyFourFF_7, prime_oneHundredSixtyFourFF_1154117672576564750665852991]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302489 : Nat.totient 193891768992862878111863302489 = 193735025444768405292047728656 := by
  rw [← show ((([(1237, 1), (156743548094472819815572597, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302489 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_1237, prime_oneHundredSixtyFourFF_156743548094472819815572597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302490 : Nat.totient 193891768992862878111863302490 = 69552285826786101714911477760 := by
  rw [← show ((([(2, 1), (5, 1), (17, 3), (29, 1), (79, 1), (2131, 1), (159869, 1), (5056381242277, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302490 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_5, prime_oneHundredSixtyFourFF_17, prime_oneHundredSixtyFourFF_29, prime_oneHundredSixtyFourFF_79, prime_oneHundredSixtyFourFF_2131, prime_oneHundredSixtyFourFF_159869, prime_oneHundredSixtyFourFF_5056381242277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302491 : Nat.totient 193891768992862878111863302491 = 129261179328211541052073413672 := by
  rw [← show ((([(3, 1), (355395970823, 1), (181855155855089839, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302491 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_3, prime_oneHundredSixtyFourFF_355395970823, prime_oneHundredSixtyFourFF_181855155855089839]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302492 : Nat.totient 193891768992862878111863302492 = 95772080254260082259001476160 := by
  rw [← show ((([(2, 2), (83, 1), (16567, 1), (325921333, 1), (108159489589871, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302492 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_83, prime_oneHundredSixtyFourFF_16567, prime_oneHundredSixtyFourFF_325921333, prime_oneHundredSixtyFourFF_108159489589871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302493 : Nat.totient 193891768992862878111863302493 = 176260902709655245457662220880 := by
  rw [← show ((([(11, 1), (40597, 1), (434182931100737130401179, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302493 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_11, prime_oneHundredSixtyFourFF_40597, prime_oneHundredSixtyFourFF_434182931100737130401179]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302494 : Nat.totient 193891768992862878111863302494 = 64630589664248994541393898640 := by
  rw [← show ((([(2, 1), (3, 2), (1673437451123, 1), (6436909211527021, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302494 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_3, prime_oneHundredSixtyFourFF_1673437451123, prime_oneHundredSixtyFourFF_6436909211527021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302495 : Nat.totient 193891768992862878111863302495 = 132954351426855414703541579040 := by
  rw [← show ((([(5, 1), (7, 1), (29850787, 1), (185581868523852011111, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302495 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_5, prime_oneHundredSixtyFourFF_7, prime_oneHundredSixtyFourFF_29850787, prime_oneHundredSixtyFourFF_185581868523852011111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302496 : Nat.totient 193891768992862878111863302496 = 91783053839443070738808714240 := by
  rw [← show ((([(2, 5), (19, 1), (1559, 1), (61031, 1), (3351654105219542953, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302496 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_19, prime_oneHundredSixtyFourFF_1559, prime_oneHundredSixtyFourFF_61031, prime_oneHundredSixtyFourFF_3351654105219542953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302497 : Nat.totient 193891768992862878111863302497 = 119317823870422597742105851392 := by
  rw [← show ((([(3, 1), (13, 1), (635287, 1), (7825728875814895295329, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302497 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_3, prime_oneHundredSixtyFourFF_13, prime_oneHundredSixtyFourFF_635287, prime_oneHundredSixtyFourFF_7825728875814895295329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302498 : Nat.totient 193891768992862878111863302498 = 96945884496425974121163866100 := by
  rw [← show ((([(2, 1), (17797584535699, 1), (5447137183249451, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302498 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_17797584535699, prime_oneHundredSixtyFourFF_5447137183249451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302499 : Nat.totient 193891768992862878111863302499 = 193839238034046063460518984720 := by
  rw [← show ((([(3691, 1), (52530958816814651344314089, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302499 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_3691, prime_oneHundredSixtyFourFF_52530958816814651344314089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302500 : Nat.totient 193891768992862878111863302500 = 51586693891495180326800112000 := by
  rw [← show ((([(2, 2), (3, 1), (5, 4), (439, 1), (58888919967460251514613, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302500 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_2, prime_oneHundredSixtyFourFF_3, prime_oneHundredSixtyFourFF_5, prime_oneHundredSixtyFourFF_439, prime_oneHundredSixtyFourFF_58888919967460251514613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFourFF_193891768992862878111863302501 : Nat.totient 193891768992862878111863302501 = 192702248937691940209336533612 := by
  rw [← show ((([(163, 1), (1189520055170937902526768727, 1)] : List FactorBlock).map factorBlockValue).prod) = 193891768992862878111863302501 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFourFF_163, prime_oneHundredSixtyFourFF_1189520055170937902526768727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredSixtyFourFF : certifiedKill 1 193891768992862878111863302399 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredSixtyFourFF_193891768992862878111863302400, phi_oneHundredSixtyFourFF_193891768992862878111863302401, phi_oneHundredSixtyFourFF_193891768992862878111863302402,
    phi_oneHundredSixtyFourFF_193891768992862878111863302403, phi_oneHundredSixtyFourFF_193891768992862878111863302404, phi_oneHundredSixtyFourFF_193891768992862878111863302405,
    phi_oneHundredSixtyFourFF_193891768992862878111863302406, phi_oneHundredSixtyFourFF_193891768992862878111863302407, phi_oneHundredSixtyFourFF_193891768992862878111863302408,
    phi_oneHundredSixtyFourFF_193891768992862878111863302409, phi_oneHundredSixtyFourFF_193891768992862878111863302410, phi_oneHundredSixtyFourFF_193891768992862878111863302411,
    phi_oneHundredSixtyFourFF_193891768992862878111863302412, phi_oneHundredSixtyFourFF_193891768992862878111863302413, phi_oneHundredSixtyFourFF_193891768992862878111863302414,
    phi_oneHundredSixtyFourFF_193891768992862878111863302415, phi_oneHundredSixtyFourFF_193891768992862878111863302416, phi_oneHundredSixtyFourFF_193891768992862878111863302417,
    phi_oneHundredSixtyFourFF_193891768992862878111863302418, phi_oneHundredSixtyFourFF_193891768992862878111863302419, phi_oneHundredSixtyFourFF_193891768992862878111863302420,
    phi_oneHundredSixtyFourFF_193891768992862878111863302421, phi_oneHundredSixtyFourFF_193891768992862878111863302422, phi_oneHundredSixtyFourFF_193891768992862878111863302423,
    phi_oneHundredSixtyFourFF_193891768992862878111863302424, phi_oneHundredSixtyFourFF_193891768992862878111863302425, phi_oneHundredSixtyFourFF_193891768992862878111863302426,
    phi_oneHundredSixtyFourFF_193891768992862878111863302427, phi_oneHundredSixtyFourFF_193891768992862878111863302428, phi_oneHundredSixtyFourFF_193891768992862878111863302429,
    phi_oneHundredSixtyFourFF_193891768992862878111863302430, phi_oneHundredSixtyFourFF_193891768992862878111863302431, phi_oneHundredSixtyFourFF_193891768992862878111863302432,
    phi_oneHundredSixtyFourFF_193891768992862878111863302433, phi_oneHundredSixtyFourFF_193891768992862878111863302434, phi_oneHundredSixtyFourFF_193891768992862878111863302435,
    phi_oneHundredSixtyFourFF_193891768992862878111863302436, phi_oneHundredSixtyFourFF_193891768992862878111863302437, phi_oneHundredSixtyFourFF_193891768992862878111863302438,
    phi_oneHundredSixtyFourFF_193891768992862878111863302439, phi_oneHundredSixtyFourFF_193891768992862878111863302440, phi_oneHundredSixtyFourFF_193891768992862878111863302441,
    phi_oneHundredSixtyFourFF_193891768992862878111863302442, phi_oneHundredSixtyFourFF_193891768992862878111863302443, phi_oneHundredSixtyFourFF_193891768992862878111863302444,
    phi_oneHundredSixtyFourFF_193891768992862878111863302445, phi_oneHundredSixtyFourFF_193891768992862878111863302446, phi_oneHundredSixtyFourFF_193891768992862878111863302447,
    phi_oneHundredSixtyFourFF_193891768992862878111863302448, phi_oneHundredSixtyFourFF_193891768992862878111863302449, phi_oneHundredSixtyFourFF_193891768992862878111863302450,
    phi_oneHundredSixtyFourFF_193891768992862878111863302451, phi_oneHundredSixtyFourFF_193891768992862878111863302452, phi_oneHundredSixtyFourFF_193891768992862878111863302453,
    phi_oneHundredSixtyFourFF_193891768992862878111863302454, phi_oneHundredSixtyFourFF_193891768992862878111863302455, phi_oneHundredSixtyFourFF_193891768992862878111863302456,
    phi_oneHundredSixtyFourFF_193891768992862878111863302457, phi_oneHundredSixtyFourFF_193891768992862878111863302458, phi_oneHundredSixtyFourFF_193891768992862878111863302459,
    phi_oneHundredSixtyFourFF_193891768992862878111863302460, phi_oneHundredSixtyFourFF_193891768992862878111863302461, phi_oneHundredSixtyFourFF_193891768992862878111863302462,
    phi_oneHundredSixtyFourFF_193891768992862878111863302463, phi_oneHundredSixtyFourFF_193891768992862878111863302464, phi_oneHundredSixtyFourFF_193891768992862878111863302465,
    phi_oneHundredSixtyFourFF_193891768992862878111863302466, phi_oneHundredSixtyFourFF_193891768992862878111863302467, phi_oneHundredSixtyFourFF_193891768992862878111863302468,
    phi_oneHundredSixtyFourFF_193891768992862878111863302469, phi_oneHundredSixtyFourFF_193891768992862878111863302470, phi_oneHundredSixtyFourFF_193891768992862878111863302471,
    phi_oneHundredSixtyFourFF_193891768992862878111863302472, phi_oneHundredSixtyFourFF_193891768992862878111863302473, phi_oneHundredSixtyFourFF_193891768992862878111863302474,
    phi_oneHundredSixtyFourFF_193891768992862878111863302475, phi_oneHundredSixtyFourFF_193891768992862878111863302476, phi_oneHundredSixtyFourFF_193891768992862878111863302477,
    phi_oneHundredSixtyFourFF_193891768992862878111863302478, phi_oneHundredSixtyFourFF_193891768992862878111863302479, phi_oneHundredSixtyFourFF_193891768992862878111863302480,
    phi_oneHundredSixtyFourFF_193891768992862878111863302481, phi_oneHundredSixtyFourFF_193891768992862878111863302482, phi_oneHundredSixtyFourFF_193891768992862878111863302483,
    phi_oneHundredSixtyFourFF_193891768992862878111863302484, phi_oneHundredSixtyFourFF_193891768992862878111863302485, phi_oneHundredSixtyFourFF_193891768992862878111863302486,
    phi_oneHundredSixtyFourFF_193891768992862878111863302487, phi_oneHundredSixtyFourFF_193891768992862878111863302488, phi_oneHundredSixtyFourFF_193891768992862878111863302489,
    phi_oneHundredSixtyFourFF_193891768992862878111863302490, phi_oneHundredSixtyFourFF_193891768992862878111863302491, phi_oneHundredSixtyFourFF_193891768992862878111863302492,
    phi_oneHundredSixtyFourFF_193891768992862878111863302493, phi_oneHundredSixtyFourFF_193891768992862878111863302494, phi_oneHundredSixtyFourFF_193891768992862878111863302495,
    phi_oneHundredSixtyFourFF_193891768992862878111863302496, phi_oneHundredSixtyFourFF_193891768992862878111863302497, phi_oneHundredSixtyFourFF_193891768992862878111863302498,
    phi_oneHundredSixtyFourFF_193891768992862878111863302499, phi_oneHundredSixtyFourFF_193891768992862878111863302500, phi_oneHundredSixtyFourFF_193891768992862878111863302501]

end TotientTailPeriodKiller
end Erdos249257
