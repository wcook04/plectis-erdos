import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredTwentyEightDVFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredTwentyEightDVFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredTwentyEightDVFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredTwentyEightDVFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredTwentyEightDVFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredTwentyEightDVFastPow a n * oneHundredTwentyEightDVFastPow a n * a else oneHundredTwentyEightDVFastPow a n * oneHundredTwentyEightDVFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredTwentyEightDV_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredTwentyEightDV_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredTwentyEightDV_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredTwentyEightDV_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredTwentyEightDV_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredTwentyEightDV_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredTwentyEightDV_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredTwentyEightDV_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredTwentyEightDV_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredTwentyEightDV_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredTwentyEightDV_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredTwentyEightDV_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredTwentyEightDV_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredTwentyEightDV_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredTwentyEightDV_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredTwentyEightDV_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredTwentyEightDV_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredTwentyEightDV_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredTwentyEightDV_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredTwentyEightDV_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredTwentyEightDV_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredTwentyEightDV_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredTwentyEightDV_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredTwentyEightDV_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredTwentyEightDV_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredTwentyEightDV_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredTwentyEightDV_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredTwentyEightDV_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredTwentyEightDV_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredTwentyEightDV_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredTwentyEightDV_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredTwentyEightDV_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredTwentyEightDV_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredTwentyEightDV_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredTwentyEightDV_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredTwentyEightDV_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredTwentyEightDV_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredTwentyEightDV_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredTwentyEightDV_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredTwentyEightDV_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredTwentyEightDV_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredTwentyEightDV_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredTwentyEightDV_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredTwentyEightDV_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredTwentyEightDV_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredTwentyEightDV_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredTwentyEightDV_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredTwentyEightDV_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredTwentyEightDV_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredTwentyEightDV_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredTwentyEightDV_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredTwentyEightDV_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredTwentyEightDV_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredTwentyEightDV_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredTwentyEightDV_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredTwentyEightDV_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredTwentyEightDV_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredTwentyEightDV_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredTwentyEightDV_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredTwentyEightDV_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredTwentyEightDV_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredTwentyEightDV_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredTwentyEightDV_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredTwentyEightDV_367 : Nat.Prime 367 := by norm_num

private theorem prime_oneHundredTwentyEightDV_401 : Nat.Prime 401 := by norm_num

private theorem prime_oneHundredTwentyEightDV_409 : Nat.Prime 409 := by norm_num

private theorem prime_oneHundredTwentyEightDV_431 : Nat.Prime 431 := by norm_num

private theorem prime_oneHundredTwentyEightDV_433 : Nat.Prime 433 := by norm_num

private theorem prime_oneHundredTwentyEightDV_449 : Nat.Prime 449 := by norm_num

private theorem prime_oneHundredTwentyEightDV_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredTwentyEightDV_463 : Nat.Prime 463 := by norm_num

private theorem prime_oneHundredTwentyEightDV_467 : Nat.Prime 467 := by norm_num

private theorem prime_oneHundredTwentyEightDV_487 : Nat.Prime 487 := by norm_num

private theorem prime_oneHundredTwentyEightDV_521 : Nat.Prime 521 := by norm_num

private theorem prime_oneHundredTwentyEightDV_569 : Nat.Prime 569 := by norm_num

private theorem prime_oneHundredTwentyEightDV_571 : Nat.Prime 571 := by norm_num

private theorem prime_oneHundredTwentyEightDV_577 : Nat.Prime 577 := by norm_num

private theorem prime_oneHundredTwentyEightDV_599 : Nat.Prime 599 := by norm_num

private theorem prime_oneHundredTwentyEightDV_601 : Nat.Prime 601 := by norm_num

private theorem prime_oneHundredTwentyEightDV_613 : Nat.Prime 613 := by norm_num

private theorem prime_oneHundredTwentyEightDV_619 : Nat.Prime 619 := by norm_num

private theorem prime_oneHundredTwentyEightDV_631 : Nat.Prime 631 := by norm_num

private theorem prime_oneHundredTwentyEightDV_643 : Nat.Prime 643 := by norm_num

private theorem prime_oneHundredTwentyEightDV_653 : Nat.Prime 653 := by norm_num

private theorem prime_oneHundredTwentyEightDV_659 : Nat.Prime 659 := by norm_num

private theorem prime_oneHundredTwentyEightDV_673 : Nat.Prime 673 := by norm_num

private theorem prime_oneHundredTwentyEightDV_677 : Nat.Prime 677 := by norm_num

private theorem prime_oneHundredTwentyEightDV_691 : Nat.Prime 691 := by norm_num

private theorem prime_oneHundredTwentyEightDV_701 : Nat.Prime 701 := by norm_num

private theorem prime_oneHundredTwentyEightDV_719 : Nat.Prime 719 := by norm_num

private theorem prime_oneHundredTwentyEightDV_733 : Nat.Prime 733 := by norm_num

private theorem prime_oneHundredTwentyEightDV_743 : Nat.Prime 743 := by norm_num

private theorem prime_oneHundredTwentyEightDV_751 : Nat.Prime 751 := by norm_num

private theorem prime_oneHundredTwentyEightDV_809 : Nat.Prime 809 := by norm_num

private theorem prime_oneHundredTwentyEightDV_827 : Nat.Prime 827 := by norm_num

private theorem prime_oneHundredTwentyEightDV_829 : Nat.Prime 829 := by norm_num

private theorem prime_oneHundredTwentyEightDV_887 : Nat.Prime 887 := by norm_num

private theorem prime_oneHundredTwentyEightDV_911 : Nat.Prime 911 := by norm_num

private theorem prime_oneHundredTwentyEightDV_947 : Nat.Prime 947 := by norm_num

private theorem prime_oneHundredTwentyEightDV_953 : Nat.Prime 953 := by norm_num

private theorem prime_oneHundredTwentyEightDV_967 : Nat.Prime 967 := by norm_num

private theorem prime_oneHundredTwentyEightDV_983 : Nat.Prime 983 := by norm_num

private theorem prime_oneHundredTwentyEightDV_997 : Nat.Prime 997 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1009 : Nat.Prime 1009 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1013 : Nat.Prime 1013 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1049 : Nat.Prime 1049 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1063 : Nat.Prime 1063 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1069 : Nat.Prime 1069 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1087 : Nat.Prime 1087 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1151 : Nat.Prime 1151 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1163 : Nat.Prime 1163 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1181 : Nat.Prime 1181 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1217 : Nat.Prime 1217 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1229 : Nat.Prime 1229 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1259 : Nat.Prime 1259 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1277 : Nat.Prime 1277 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1289 : Nat.Prime 1289 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1319 : Nat.Prime 1319 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1321 : Nat.Prime 1321 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1327 : Nat.Prime 1327 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1453 : Nat.Prime 1453 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1487 : Nat.Prime 1487 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1523 : Nat.Prime 1523 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1543 : Nat.Prime 1543 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1553 : Nat.Prime 1553 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1571 : Nat.Prime 1571 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1583 : Nat.Prime 1583 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1613 : Nat.Prime 1613 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1621 : Nat.Prime 1621 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1627 : Nat.Prime 1627 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1637 : Nat.Prime 1637 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1667 : Nat.Prime 1667 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1741 : Nat.Prime 1741 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1901 : Nat.Prime 1901 := by norm_num

private theorem prime_oneHundredTwentyEightDV_2129 : Nat.Prime 2129 := by norm_num

private theorem prime_oneHundredTwentyEightDV_2237 : Nat.Prime 2237 := by norm_num

private theorem prime_oneHundredTwentyEightDV_2297 : Nat.Prime 2297 := by norm_num

private theorem prime_oneHundredTwentyEightDV_2399 : Nat.Prime 2399 := by norm_num

private theorem prime_oneHundredTwentyEightDV_2521 : Nat.Prime 2521 := by norm_num

private theorem prime_oneHundredTwentyEightDV_2707 : Nat.Prime 2707 := by norm_num

private theorem prime_oneHundredTwentyEightDV_2711 : Nat.Prime 2711 := by norm_num

private theorem prime_oneHundredTwentyEightDV_2731 : Nat.Prime 2731 := by norm_num

private theorem prime_oneHundredTwentyEightDV_2777 : Nat.Prime 2777 := by norm_num

private theorem prime_oneHundredTwentyEightDV_2843 : Nat.Prime 2843 := by norm_num

private theorem prime_oneHundredTwentyEightDV_2909 : Nat.Prime 2909 := by norm_num

private theorem prime_oneHundredTwentyEightDV_3041 : Nat.Prime 3041 := by norm_num

private theorem prime_oneHundredTwentyEightDV_3203 : Nat.Prime 3203 := by norm_num

private theorem prime_oneHundredTwentyEightDV_3221 : Nat.Prime 3221 := by norm_num

private theorem prime_oneHundredTwentyEightDV_3253 : Nat.Prime 3253 := by norm_num

private theorem prime_oneHundredTwentyEightDV_3343 : Nat.Prime 3343 := by norm_num

private theorem prime_oneHundredTwentyEightDV_3361 : Nat.Prime 3361 := by norm_num

private theorem prime_oneHundredTwentyEightDV_3373 : Nat.Prime 3373 := by norm_num

private theorem prime_oneHundredTwentyEightDV_3413 : Nat.Prime 3413 := by norm_num

private theorem prime_oneHundredTwentyEightDV_3559 : Nat.Prime 3559 := by norm_num

private theorem prime_oneHundredTwentyEightDV_3623 : Nat.Prime 3623 := by norm_num

private theorem prime_oneHundredTwentyEightDV_3709 : Nat.Prime 3709 := by norm_num

private theorem prime_oneHundredTwentyEightDV_3739 : Nat.Prime 3739 := by norm_num

private theorem prime_oneHundredTwentyEightDV_3803 : Nat.Prime 3803 := by norm_num

private theorem prime_oneHundredTwentyEightDV_3823 : Nat.Prime 3823 := by norm_num

private theorem prime_oneHundredTwentyEightDV_3833 : Nat.Prime 3833 := by norm_num

private theorem prime_oneHundredTwentyEightDV_3947 : Nat.Prime 3947 := by norm_num

private theorem prime_oneHundredTwentyEightDV_4001 : Nat.Prime 4001 := by norm_num

private theorem prime_oneHundredTwentyEightDV_4003 : Nat.Prime 4003 := by norm_num

private theorem prime_oneHundredTwentyEightDV_4051 : Nat.Prime 4051 := by norm_num

private theorem prime_oneHundredTwentyEightDV_4099 : Nat.Prime 4099 := by norm_num

private theorem prime_oneHundredTwentyEightDV_4129 : Nat.Prime 4129 := by norm_num

private theorem prime_oneHundredTwentyEightDV_4297 : Nat.Prime 4297 := by norm_num

private theorem prime_oneHundredTwentyEightDV_4327 : Nat.Prime 4327 := by norm_num

private theorem prime_oneHundredTwentyEightDV_4691 : Nat.Prime 4691 := by norm_num

private theorem prime_oneHundredTwentyEightDV_4759 : Nat.Prime 4759 := by norm_num

private theorem prime_oneHundredTwentyEightDV_5231 : Nat.Prime 5231 := by norm_num

private theorem prime_oneHundredTwentyEightDV_5303 : Nat.Prime 5303 := by norm_num

private theorem prime_oneHundredTwentyEightDV_5309 : Nat.Prime 5309 := by norm_num

private theorem prime_oneHundredTwentyEightDV_5407 : Nat.Prime 5407 := by norm_num

private theorem prime_oneHundredTwentyEightDV_5651 : Nat.Prime 5651 := by norm_num

private theorem prime_oneHundredTwentyEightDV_5701 : Nat.Prime 5701 := by norm_num

private theorem prime_oneHundredTwentyEightDV_5807 : Nat.Prime 5807 := by norm_num

private theorem prime_oneHundredTwentyEightDV_6133 : Nat.Prime 6133 := by norm_num

private theorem prime_oneHundredTwentyEightDV_6353 : Nat.Prime 6353 := by norm_num

private theorem prime_oneHundredTwentyEightDV_6449 : Nat.Prime 6449 := by norm_num

private theorem prime_oneHundredTwentyEightDV_6451 : Nat.Prime 6451 := by norm_num

private theorem prime_oneHundredTwentyEightDV_6761 : Nat.Prime 6761 := by norm_num

private theorem prime_oneHundredTwentyEightDV_6997 : Nat.Prime 6997 := by norm_num

private theorem prime_oneHundredTwentyEightDV_7187 : Nat.Prime 7187 := by norm_num

private theorem prime_oneHundredTwentyEightDV_7297 : Nat.Prime 7297 := by norm_num

private theorem prime_oneHundredTwentyEightDV_7481 : Nat.Prime 7481 := by norm_num

private theorem prime_oneHundredTwentyEightDV_7541 : Nat.Prime 7541 := by norm_num

private theorem prime_oneHundredTwentyEightDV_7561 : Nat.Prime 7561 := by norm_num

private theorem prime_oneHundredTwentyEightDV_7607 : Nat.Prime 7607 := by norm_num

private theorem prime_oneHundredTwentyEightDV_8089 : Nat.Prime 8089 := by norm_num

private theorem prime_oneHundredTwentyEightDV_8273 : Nat.Prime 8273 := by norm_num

private theorem prime_oneHundredTwentyEightDV_8537 : Nat.Prime 8537 := by norm_num

private theorem prime_oneHundredTwentyEightDV_8893 : Nat.Prime 8893 := by norm_num

private theorem prime_oneHundredTwentyEightDV_8941 : Nat.Prime 8941 := by norm_num

private theorem prime_oneHundredTwentyEightDV_9377 : Nat.Prime 9377 := by norm_num

private theorem prime_oneHundredTwentyEightDV_9511 : Nat.Prime 9511 := by norm_num

private theorem prime_oneHundredTwentyEightDV_9631 : Nat.Prime 9631 := by norm_num

private theorem prime_oneHundredTwentyEightDV_10259 : Nat.Prime 10259 := by norm_num

private theorem prime_oneHundredTwentyEightDV_10663 : Nat.Prime 10663 := by norm_num

private theorem prime_oneHundredTwentyEightDV_10789 : Nat.Prime 10789 := by norm_num

private theorem prime_oneHundredTwentyEightDV_10847 : Nat.Prime 10847 := by norm_num

private theorem prime_oneHundredTwentyEightDV_11027 : Nat.Prime 11027 := by norm_num

private theorem prime_oneHundredTwentyEightDV_11497 : Nat.Prime 11497 := by norm_num

private theorem prime_oneHundredTwentyEightDV_12197 : Nat.Prime 12197 := by norm_num

private theorem prime_oneHundredTwentyEightDV_12541 : Nat.Prime 12541 := by norm_num

private theorem prime_oneHundredTwentyEightDV_12641 : Nat.Prime 12641 := by norm_num

private theorem prime_oneHundredTwentyEightDV_12919 : Nat.Prime 12919 := by norm_num

private theorem prime_oneHundredTwentyEightDV_13003 : Nat.Prime 13003 := by norm_num

private theorem prime_oneHundredTwentyEightDV_13411 : Nat.Prime 13411 := by norm_num

private theorem prime_oneHundredTwentyEightDV_13421 : Nat.Prime 13421 := by norm_num

private theorem prime_oneHundredTwentyEightDV_13627 : Nat.Prime 13627 := by norm_num

private theorem prime_oneHundredTwentyEightDV_14851 : Nat.Prime 14851 := by norm_num

private theorem prime_oneHundredTwentyEightDV_16693 : Nat.Prime 16693 := by norm_num

private theorem prime_oneHundredTwentyEightDV_16823 : Nat.Prime 16823 := by norm_num

private theorem prime_oneHundredTwentyEightDV_16963 : Nat.Prime 16963 := by norm_num

private theorem prime_oneHundredTwentyEightDV_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredTwentyEightDV_17299 : Nat.Prime 17299 := by norm_num

private theorem prime_oneHundredTwentyEightDV_17351 : Nat.Prime 17351 := by norm_num

private theorem prime_oneHundredTwentyEightDV_17959 : Nat.Prime 17959 := by norm_num

private theorem prime_oneHundredTwentyEightDV_18181 : Nat.Prime 18181 := by norm_num

private theorem prime_oneHundredTwentyEightDV_20357 : Nat.Prime 20357 := by norm_num

private theorem prime_oneHundredTwentyEightDV_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredTwentyEightDV_20759 : Nat.Prime 20759 := by norm_num

private theorem prime_oneHundredTwentyEightDV_21017 : Nat.Prime 21017 := by norm_num

private theorem prime_oneHundredTwentyEightDV_21767 : Nat.Prime 21767 := by norm_num

private theorem prime_oneHundredTwentyEightDV_21787 : Nat.Prime 21787 := by norm_num

private theorem prime_oneHundredTwentyEightDV_22307 : Nat.Prime 22307 := by norm_num

private theorem prime_oneHundredTwentyEightDV_22447 : Nat.Prime 22447 := by norm_num

private theorem prime_oneHundredTwentyEightDV_23333 : Nat.Prime 23333 := by norm_num

private theorem prime_oneHundredTwentyEightDV_24841 : Nat.Prime 24841 := by norm_num

private theorem prime_oneHundredTwentyEightDV_25237 : Nat.Prime 25237 := by norm_num

private theorem prime_oneHundredTwentyEightDV_25733 : Nat.Prime 25733 := by norm_num

private theorem prime_oneHundredTwentyEightDV_26683 : Nat.Prime 26683 := by norm_num

private theorem prime_oneHundredTwentyEightDV_26947 : Nat.Prime 26947 := by norm_num

private theorem prime_oneHundredTwentyEightDV_27409 : Nat.Prime 27409 := by norm_num

private theorem prime_oneHundredTwentyEightDV_28649 : Nat.Prime 28649 := by norm_num

private theorem prime_oneHundredTwentyEightDV_29389 : Nat.Prime 29389 := by norm_num

private theorem prime_oneHundredTwentyEightDV_31013 : Nat.Prime 31013 := by norm_num

private theorem prime_oneHundredTwentyEightDV_31643 : Nat.Prime 31643 := by norm_num

private theorem prime_oneHundredTwentyEightDV_32327 : Nat.Prime 32327 := by norm_num

private theorem prime_oneHundredTwentyEightDV_32587 : Nat.Prime 32587 := by norm_num

private theorem prime_oneHundredTwentyEightDV_32797 : Nat.Prime 32797 := by norm_num

private theorem prime_oneHundredTwentyEightDV_32917 : Nat.Prime 32917 := by norm_num

private theorem prime_oneHundredTwentyEightDV_33941 : Nat.Prime 33941 := by norm_num

private theorem prime_oneHundredTwentyEightDV_36097 : Nat.Prime 36097 := by norm_num

private theorem prime_oneHundredTwentyEightDV_38153 : Nat.Prime 38153 := by norm_num

private theorem prime_oneHundredTwentyEightDV_38639 : Nat.Prime 38639 := by norm_num

private theorem prime_oneHundredTwentyEightDV_39581 : Nat.Prime 39581 := by norm_num

private theorem prime_oneHundredTwentyEightDV_39607 : Nat.Prime 39607 := by norm_num

private theorem prime_oneHundredTwentyEightDV_41143 : Nat.Prime 41143 := by norm_num

private theorem prime_oneHundredTwentyEightDV_42407 : Nat.Prime 42407 := by norm_num

private theorem prime_oneHundredTwentyEightDV_42863 : Nat.Prime 42863 := by norm_num

private theorem prime_oneHundredTwentyEightDV_43543 : Nat.Prime 43543 := by norm_num

private theorem prime_oneHundredTwentyEightDV_44071 : Nat.Prime 44071 := by norm_num

private theorem prime_oneHundredTwentyEightDV_48017 : Nat.Prime 48017 := by norm_num

private theorem prime_oneHundredTwentyEightDV_49157 : Nat.Prime 49157 := by norm_num

private theorem prime_oneHundredTwentyEightDV_51071 : Nat.Prime 51071 := by norm_num

private theorem prime_oneHundredTwentyEightDV_52631 : Nat.Prime 52631 := by norm_num

private theorem prime_oneHundredTwentyEightDV_53279 : Nat.Prime 53279 := by norm_num

private theorem prime_oneHundredTwentyEightDV_53591 : Nat.Prime 53591 := by norm_num

private theorem prime_oneHundredTwentyEightDV_55313 : Nat.Prime 55313 := by norm_num

private theorem prime_oneHundredTwentyEightDV_60887 : Nat.Prime 60887 := by norm_num

private theorem prime_oneHundredTwentyEightDV_62731 : Nat.Prime 62731 := by norm_num

private theorem prime_oneHundredTwentyEightDV_63353 : Nat.Prime 63353 := by norm_num

private theorem prime_oneHundredTwentyEightDV_64667 : Nat.Prime 64667 := by norm_num

private theorem prime_oneHundredTwentyEightDV_65119 : Nat.Prime 65119 := by norm_num

private theorem prime_oneHundredTwentyEightDV_66713 : Nat.Prime 66713 := by norm_num

private theorem prime_oneHundredTwentyEightDV_69931 : Nat.Prime 69931 := by norm_num

private theorem prime_oneHundredTwentyEightDV_69997 : Nat.Prime 69997 := by norm_num

private theorem prime_oneHundredTwentyEightDV_71341 : Nat.Prime 71341 := by norm_num

private theorem prime_oneHundredTwentyEightDV_71909 : Nat.Prime 71909 := by norm_num

private theorem prime_oneHundredTwentyEightDV_71933 : Nat.Prime 71933 := by norm_num

private theorem prime_oneHundredTwentyEightDV_71983 : Nat.Prime 71983 := by norm_num

private theorem prime_oneHundredTwentyEightDV_79613 : Nat.Prime 79613 := by norm_num

private theorem prime_oneHundredTwentyEightDV_80989 : Nat.Prime 80989 := by norm_num

private theorem prime_oneHundredTwentyEightDV_83207 : Nat.Prime 83207 := by norm_num

private theorem prime_oneHundredTwentyEightDV_83273 : Nat.Prime 83273 := by norm_num

private theorem prime_oneHundredTwentyEightDV_84191 : Nat.Prime 84191 := by norm_num

private theorem prime_oneHundredTwentyEightDV_88867 : Nat.Prime 88867 := by norm_num

private theorem prime_oneHundredTwentyEightDV_90997 : Nat.Prime 90997 := by norm_num

private theorem prime_oneHundredTwentyEightDV_92507 : Nat.Prime 92507 := by norm_num

private theorem prime_oneHundredTwentyEightDV_94433 : Nat.Prime 94433 := by norm_num

private theorem prime_oneHundredTwentyEightDV_102329 : Nat.Prime 102329 := by norm_num

private theorem prime_oneHundredTwentyEightDV_102931 : Nat.Prime 102931 := by norm_num

private theorem prime_oneHundredTwentyEightDV_118691 : Nat.Prime 118691 := by norm_num

private theorem prime_oneHundredTwentyEightDV_119549 : Nat.Prime 119549 := by norm_num

private theorem prime_oneHundredTwentyEightDV_124067 : Nat.Prime 124067 := by norm_num

private theorem prime_oneHundredTwentyEightDV_126601 : Nat.Prime 126601 := by norm_num

private theorem prime_oneHundredTwentyEightDV_132361 : Nat.Prime 132361 := by norm_num

private theorem prime_oneHundredTwentyEightDV_133711 : Nat.Prime 133711 := by norm_num

private theorem prime_oneHundredTwentyEightDV_134243 : Nat.Prime 134243 := by norm_num

private theorem prime_oneHundredTwentyEightDV_135347 : Nat.Prime 135347 := by norm_num

private theorem prime_oneHundredTwentyEightDV_135589 : Nat.Prime 135589 := by norm_num

private theorem prime_oneHundredTwentyEightDV_150107 : Nat.Prime 150107 := by norm_num

private theorem prime_oneHundredTwentyEightDV_170603 : Nat.Prime 170603 := by norm_num

private theorem prime_oneHundredTwentyEightDV_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredTwentyEightDV_171827 : Nat.Prime 171827 := by norm_num

private theorem prime_oneHundredTwentyEightDV_191123 : Nat.Prime 191123 := by norm_num

private theorem prime_oneHundredTwentyEightDV_199673 : Nat.Prime 199673 := by norm_num

private theorem prime_oneHundredTwentyEightDV_205663 : Nat.Prime 205663 := by norm_num

private theorem prime_oneHundredTwentyEightDV_217367 : Nat.Prime 217367 := by norm_num

private theorem prime_oneHundredTwentyEightDV_223547 : Nat.Prime 223547 := by norm_num

private theorem prime_oneHundredTwentyEightDV_240953 : Nat.Prime 240953 := by norm_num

private theorem prime_oneHundredTwentyEightDV_245299 : Nat.Prime 245299 := by norm_num

private theorem prime_oneHundredTwentyEightDV_252827 : Nat.Prime 252827 := by norm_num

private theorem prime_oneHundredTwentyEightDV_256889 : Nat.Prime 256889 := by norm_num

private theorem prime_oneHundredTwentyEightDV_274777 : Nat.Prime 274777 := by norm_num

private theorem prime_oneHundredTwentyEightDV_279353 : Nat.Prime 279353 := by norm_num

private theorem prime_oneHundredTwentyEightDV_286199 : Nat.Prime 286199 := by norm_num

private theorem prime_oneHundredTwentyEightDV_319817 : Nat.Prime 319817 := by norm_num

private theorem prime_oneHundredTwentyEightDV_354551 : Nat.Prime 354551 := by norm_num

private theorem prime_oneHundredTwentyEightDV_362027 : Nat.Prime 362027 := by norm_num

private theorem prime_oneHundredTwentyEightDV_379033 : Nat.Prime 379033 := by norm_num

private theorem prime_oneHundredTwentyEightDV_417023 : Nat.Prime 417023 := by norm_num

private theorem prime_oneHundredTwentyEightDV_424429 : Nat.Prime 424429 := by norm_num

private theorem prime_oneHundredTwentyEightDV_425713 : Nat.Prime 425713 := by norm_num

private theorem prime_oneHundredTwentyEightDV_443689 : Nat.Prime 443689 := by norm_num

private theorem prime_oneHundredTwentyEightDV_447463 : Nat.Prime 447463 := by norm_num

private theorem prime_oneHundredTwentyEightDV_476027 : Nat.Prime 476027 := by norm_num

private theorem prime_oneHundredTwentyEightDV_502841 : Nat.Prime 502841 := by norm_num

private theorem prime_oneHundredTwentyEightDV_550937 : Nat.Prime 550937 := by norm_num

private theorem prime_oneHundredTwentyEightDV_560969 : Nat.Prime 560969 := by norm_num

private theorem prime_oneHundredTwentyEightDV_609709 : Nat.Prime 609709 := by norm_num

private theorem prime_oneHundredTwentyEightDV_616387 : Nat.Prime 616387 := by norm_num

private theorem prime_oneHundredTwentyEightDV_643691 : Nat.Prime 643691 := by norm_num

private theorem prime_oneHundredTwentyEightDV_644197 : Nat.Prime 644197 := by norm_num

private theorem prime_oneHundredTwentyEightDV_722093 : Nat.Prime 722093 := by norm_num

private theorem prime_oneHundredTwentyEightDV_762959 : Nat.Prime 762959 := by norm_num

private theorem prime_oneHundredTwentyEightDV_767681 : Nat.Prime 767681 := by norm_num

private theorem prime_oneHundredTwentyEightDV_787217 : Nat.Prime 787217 := by norm_num

private theorem prime_oneHundredTwentyEightDV_787903 : Nat.Prime 787903 := by norm_num

private theorem prime_oneHundredTwentyEightDV_810697 : Nat.Prime 810697 := by norm_num

private theorem prime_oneHundredTwentyEightDV_846733 : Nat.Prime 846733 := by norm_num

private theorem prime_oneHundredTwentyEightDV_866431 : Nat.Prime 866431 := by norm_num

private theorem prime_oneHundredTwentyEightDV_912481 : Nat.Prime 912481 := by norm_num

private theorem prime_oneHundredTwentyEightDV_972991 : Nat.Prime 972991 := by norm_num

private theorem prime_oneHundredTwentyEightDV_975977 : Nat.Prime 975977 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1072517 : Nat.Prime 1072517 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1229519 : Nat.Prime 1229519 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1233371 : Nat.Prime 1233371 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1249273 : Nat.Prime 1249273 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1288117 : Nat.Prime 1288117 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1378103 : Nat.Prime 1378103 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1447583 : Nat.Prime 1447583 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1493963 : Nat.Prime 1493963 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1536649 : Nat.Prime 1536649 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1545121 : Nat.Prime 1545121 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1551167 : Nat.Prime 1551167 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1563619 : Nat.Prime 1563619 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1602907 : Nat.Prime 1602907 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1603111 : Nat.Prime 1603111 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1766153 : Nat.Prime 1766153 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1767089 : Nat.Prime 1767089 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1977961 : Nat.Prime 1977961 := by norm_num

private theorem prime_oneHundredTwentyEightDV_1991617 : Nat.Prime 1991617 := by norm_num

private theorem prime_oneHundredTwentyEightDV_2045567 : Nat.Prime 2045567 := by norm_num

private theorem prime_oneHundredTwentyEightDV_2155177 : Nat.Prime 2155177 := by norm_num

private theorem prime_oneHundredTwentyEightDV_2293919 : Nat.Prime 2293919 := by norm_num

private theorem prime_oneHundredTwentyEightDV_2329331 : Nat.Prime 2329331 := by norm_num

private theorem prime_oneHundredTwentyEightDV_2755243 : Nat.Prime 2755243 := by norm_num

private theorem prime_oneHundredTwentyEightDV_2830249 : Nat.Prime 2830249 := by norm_num

private theorem prime_oneHundredTwentyEightDV_3027523 : Nat.Prime 3027523 := by norm_num

private theorem prime_oneHundredTwentyEightDV_3056083 : Nat.Prime 3056083 := by norm_num

private theorem prime_oneHundredTwentyEightDV_3281297 : Nat.Prime 3281297 := by norm_num

private theorem prime_oneHundredTwentyEightDV_3298423 : Nat.Prime 3298423 := by norm_num

private theorem prime_oneHundredTwentyEightDV_3301789 : Nat.Prime 3301789 := by norm_num

private theorem prime_oneHundredTwentyEightDV_3360223 : Nat.Prime 3360223 := by norm_num

private theorem prime_oneHundredTwentyEightDV_3414239 : Nat.Prime 3414239 := by norm_num

private theorem prime_oneHundredTwentyEightDV_3484759 : Nat.Prime 3484759 := by norm_num

private theorem prime_oneHundredTwentyEightDV_3545263 : Nat.Prime 3545263 := by norm_num

private theorem prime_oneHundredTwentyEightDV_3594403 : Nat.Prime 3594403 := by norm_num

private theorem prime_oneHundredTwentyEightDV_3598501 : Nat.Prime 3598501 := by norm_num

private theorem prime_oneHundredTwentyEightDV_3769669 : Nat.Prime 3769669 := by norm_num

private theorem prime_oneHundredTwentyEightDV_4034873 : Nat.Prime 4034873 := by norm_num

private theorem prime_oneHundredTwentyEightDV_4393003 : Nat.Prime 4393003 := by norm_num

private theorem prime_oneHundredTwentyEightDV_4430887 : Nat.Prime 4430887 := by norm_num

private theorem prime_oneHundredTwentyEightDV_4440187 : Nat.Prime 4440187 := by norm_num

private theorem prime_oneHundredTwentyEightDV_4668691 : Nat.Prime 4668691 := by norm_num

private theorem prime_oneHundredTwentyEightDV_5334239 : Nat.Prime 5334239 := by norm_num

private theorem prime_oneHundredTwentyEightDV_5716031 : Nat.Prime 5716031 := by norm_num

private theorem prime_oneHundredTwentyEightDV_5725547 : Nat.Prime 5725547 := by norm_num

private theorem prime_oneHundredTwentyEightDV_6557819 : Nat.Prime 6557819 := by norm_num

private theorem prime_oneHundredTwentyEightDV_6585809 : Nat.Prime 6585809 := by norm_num

private theorem prime_oneHundredTwentyEightDV_6881383 : Nat.Prime 6881383 := by norm_num

private theorem prime_oneHundredTwentyEightDV_7130231 : Nat.Prime 7130231 := by norm_num

private theorem prime_oneHundredTwentyEightDV_7151687 : Nat.Prime 7151687 := by norm_num

private theorem prime_oneHundredTwentyEightDV_7156091 : Nat.Prime 7156091 := by norm_num

private theorem prime_oneHundredTwentyEightDV_7318973 : Nat.Prime 7318973 := by norm_num

private theorem prime_oneHundredTwentyEightDV_7388921 : Nat.Prime 7388921 := by norm_num

private theorem prime_oneHundredTwentyEightDV_7805591 : Nat.Prime 7805591 := by norm_num

private theorem prime_oneHundredTwentyEightDV_8506063 : Nat.Prime 8506063 := by norm_num

private theorem prime_oneHundredTwentyEightDV_8844323 : Nat.Prime 8844323 := by norm_num

private theorem prime_oneHundredTwentyEightDV_9767969 : Nat.Prime 9767969 := by norm_num

private theorem prime_oneHundredTwentyEightDV_9913723 : Nat.Prime 9913723 := by norm_num

private theorem prime_oneHundredTwentyEightDV_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredTwentyEightDV_11197063 : Nat.Prime 11197063 := by norm_num

private theorem prime_oneHundredTwentyEightDV_11498719 : Nat.Prime 11498719 := by norm_num

private theorem prime_oneHundredTwentyEightDV_11818663 : Nat.Prime 11818663 := by norm_num

private theorem prime_oneHundredTwentyEightDV_12031387 : Nat.Prime 12031387 := by norm_num

private theorem prime_oneHundredTwentyEightDV_12461689 : Nat.Prime 12461689 := by norm_num

private theorem prime_oneHundredTwentyEightDV_12597401 : Nat.Prime 12597401 := by norm_num

private theorem prime_oneHundredTwentyEightDV_13100981 : Nat.Prime 13100981 := by norm_num

private theorem prime_oneHundredTwentyEightDV_13511921 : Nat.Prime 13511921 := by norm_num

private theorem prime_oneHundredTwentyEightDV_14642821 : Nat.Prime 14642821 := by norm_num

private theorem prime_oneHundredTwentyEightDV_15126779 : Nat.Prime 15126779 := by norm_num

private theorem prime_oneHundredTwentyEightDV_15405947 : Nat.Prime 15405947 := by norm_num

private theorem prime_oneHundredTwentyEightDV_16062503 : Nat.Prime 16062503 := by norm_num

private theorem prime_oneHundredTwentyEightDV_16243697 : Nat.Prime 16243697 := by norm_num

private theorem prime_oneHundredTwentyEightDV_16991327 : Nat.Prime 16991327 := by norm_num

private theorem prime_oneHundredTwentyEightDV_17263031 : Nat.Prime 17263031 := by norm_num

private theorem prime_oneHundredTwentyEightDV_17293091 : Nat.Prime 17293091 := by norm_num

private theorem prime_oneHundredTwentyEightDV_18657169 : Nat.Prime 18657169 := by norm_num

private theorem prime_oneHundredTwentyEightDV_19156283 : Nat.Prime 19156283 := by norm_num

private theorem prime_oneHundredTwentyEightDV_19359973 : Nat.Prime 19359973 := by norm_num

private theorem prime_oneHundredTwentyEightDV_19705843 : Nat.Prime 19705843 := by norm_num

private theorem prime_oneHundredTwentyEightDV_20291147 : Nat.Prime 20291147 := by norm_num

private theorem prime_oneHundredTwentyEightDV_21599471 : Nat.Prime 21599471 := by norm_num

private theorem prime_oneHundredTwentyEightDV_21727217 : Nat.Prime 21727217 := by norm_num

private theorem prime_oneHundredTwentyEightDV_22528931 : Nat.Prime 22528931 := by norm_num

private theorem prime_oneHundredTwentyEightDV_23701079 : Nat.Prime 23701079 := by norm_num

private theorem prime_oneHundredTwentyEightDV_24311933 : Nat.Prime 24311933 := by norm_num

private theorem prime_oneHundredTwentyEightDV_26486477 : Nat.Prime 26486477 := by norm_num

private theorem prime_oneHundredTwentyEightDV_26655217 : Nat.Prime 26655217 := by norm_num

private theorem prime_oneHundredTwentyEightDV_35059867 : Nat.Prime 35059867 := by
  apply lucas_primality 35059867 (2 : ZMod 35059867)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (239, 1), (1063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (239, 1), (1063, 1)] : List FactorBlock).map factorBlockValue).prod) = 35059867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_23
      · exact prime_oneHundredTwentyEightDV_239
      · exact prime_oneHundredTwentyEightDV_1063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 35059867) ^ 17529933 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 35059867) ^ 11686622 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 35059867) ^ 1524342 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 35059867) ^ 146694 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 35059867) ^ 32982 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_37534067 : Nat.Prime 37534067 := by
  apply lucas_primality 37534067 (2 : ZMod 37534067)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (431, 1), (43543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (431, 1), (43543, 1)] : List FactorBlock).map factorBlockValue).prod) = 37534067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_431
      · exact prime_oneHundredTwentyEightDV_43543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 37534067) ^ 18767033 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 37534067) ^ 87086 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 37534067) ^ 862 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_37669439 : Nat.Prime 37669439 := by
  apply lucas_primality 37669439 (11 : ZMod 37669439)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (631, 1), (1571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (631, 1), (1571, 1)] : List FactorBlock).map factorBlockValue).prod) = 37669439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_19
      · exact prime_oneHundredTwentyEightDV_631
      · exact prime_oneHundredTwentyEightDV_1571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 37669439) ^ 18834719 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (11 : ZMod 37669439) ^ 1982602 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (11 : ZMod 37669439) ^ 59698 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (11 : ZMod 37669439) ^ 23978 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_40371833 : Nat.Prime 40371833 := by
  apply lucas_primality 40371833 (3 : ZMod 40371833)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (281, 1), (17959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (281, 1), (17959, 1)] : List FactorBlock).map factorBlockValue).prod) = 40371833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_281
      · exact prime_oneHundredTwentyEightDV_17959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 40371833) ^ 20185916 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 40371833) ^ 143672 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 40371833) ^ 2248 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_40985101 : Nat.Prime 40985101 := by
  apply lucas_primality 40985101 (2 : ZMod 40985101)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (13, 1), (31, 1), (113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (13, 1), (31, 1), (113, 1)] : List FactorBlock).map factorBlockValue).prod) = 40985101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_13
      · exact prime_oneHundredTwentyEightDV_31
      · exact prime_oneHundredTwentyEightDV_113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 40985101) ^ 20492550 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 40985101) ^ 13661700 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 40985101) ^ 8197020 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 40985101) ^ 3152700 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 40985101) ^ 1322100 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 40985101) ^ 362700 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_44788253 : Nat.Prime 44788253 := by
  apply lucas_primality 44788253 (2 : ZMod 44788253)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11197063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11197063, 1)] : List FactorBlock).map factorBlockValue).prod) = 44788253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_11197063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 44788253) ^ 22394126 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 44788253) ^ 4 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_45994279 : Nat.Prime 45994279 := by
  apply lucas_primality 45994279 (3 : ZMod 45994279)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 2), (63353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 2), (63353, 1)] : List FactorBlock).map factorBlockValue).prod) = 45994279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_11
      · exact prime_oneHundredTwentyEightDV_63353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 45994279) ^ 22997139 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 45994279) ^ 15331426 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 45994279) ^ 4181298 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 45994279) ^ 726 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_46025471 : Nat.Prime 46025471 := by
  apply lucas_primality 46025471 (7 : ZMod 46025471)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (367, 1), (12541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (367, 1), (12541, 1)] : List FactorBlock).map factorBlockValue).prod) = 46025471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_367
      · exact prime_oneHundredTwentyEightDV_12541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 46025471) ^ 23012735 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 46025471) ^ 9205094 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 46025471) ^ 125410 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 46025471) ^ 3670 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_46501019 : Nat.Prime 46501019 := by
  apply lucas_primality 46501019 (2 : ZMod 46501019)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (19, 1), (71983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (19, 1), (71983, 1)] : List FactorBlock).map factorBlockValue).prod) = 46501019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_17
      · exact prime_oneHundredTwentyEightDV_19
      · exact prime_oneHundredTwentyEightDV_71983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 46501019) ^ 23250509 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 46501019) ^ 2735354 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 46501019) ^ 2447422 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 46501019) ^ 646 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_46833547 : Nat.Prime 46833547 := by
  apply lucas_primality 46833547 (2 : ZMod 46833547)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7805591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7805591, 1)] : List FactorBlock).map factorBlockValue).prod) = 46833547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_7805591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 46833547) ^ 23416773 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 46833547) ^ 15611182 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 46833547) ^ 6 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_58667113 : Nat.Prime 58667113 := by
  apply lucas_primality 58667113 (13 : ZMod 58667113)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (7, 2), (23, 1), (241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (7, 2), (23, 1), (241, 1)] : List FactorBlock).map factorBlockValue).prod) = 58667113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_7
      · exact prime_oneHundredTwentyEightDV_23
      · exact prime_oneHundredTwentyEightDV_241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 58667113) ^ 29333556 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (13 : ZMod 58667113) ^ 19555704 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (13 : ZMod 58667113) ^ 8381016 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (13 : ZMod 58667113) ^ 2550744 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (13 : ZMod 58667113) ^ 243432 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_59432203 : Nat.Prime 59432203 := by
  apply lucas_primality 59432203 (2 : ZMod 59432203)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (3301789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (3301789, 1)] : List FactorBlock).map factorBlockValue).prod) = 59432203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_3301789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59432203) ^ 29716101 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 59432203) ^ 19810734 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 59432203) ^ 18 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_59929613 : Nat.Prime 59929613 := by
  apply lucas_primality 59929613 (2 : ZMod 59929613)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) = 59929613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_1811
      · exact prime_oneHundredTwentyEightDV_8273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59929613) ^ 29964806 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 33092 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 7244 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_65337023 : Nat.Prime 65337023 := by
  apply lucas_primality 65337023 (5 : ZMod 65337023)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (616387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (616387, 1)] : List FactorBlock).map factorBlockValue).prod) = 65337023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_53
      · exact prime_oneHundredTwentyEightDV_616387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 65337023) ^ 32668511 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 65337023) ^ 1232774 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 65337023) ^ 106 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_69967783 : Nat.Prime 69967783 := by
  apply lucas_primality 69967783 (5 : ZMod 69967783)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (733, 1), (5303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (733, 1), (5303, 1)] : List FactorBlock).map factorBlockValue).prod) = 69967783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_733
      · exact prime_oneHundredTwentyEightDV_5303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 69967783) ^ 34983891 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 69967783) ^ 23322594 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 69967783) ^ 95454 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 69967783) ^ 13194 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_70968847 : Nat.Prime 70968847 := by
  apply lucas_primality 70968847 (3 : ZMod 70968847)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 2), (17, 1), (23, 1), (179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 2), (17, 1), (23, 1), (179, 1)] : List FactorBlock).map factorBlockValue).prod) = 70968847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_13
      · exact prime_oneHundredTwentyEightDV_17
      · exact prime_oneHundredTwentyEightDV_23
      · exact prime_oneHundredTwentyEightDV_179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 70968847) ^ 35484423 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 70968847) ^ 23656282 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 70968847) ^ 5459142 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 70968847) ^ 4174638 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 70968847) ^ 3085602 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 70968847) ^ 396474 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_71947873 : Nat.Prime 71947873 := by
  apply lucas_primality 71947873 (10 : ZMod 71947873)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (83273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (83273, 1)] : List FactorBlock).map factorBlockValue).prod) = 71947873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_83273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 71947873) ^ 35973936 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (10 : ZMod 71947873) ^ 23982624 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (10 : ZMod 71947873) ^ 864 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_74579611 : Nat.Prime 74579611 := by
  apply lucas_primality 74579611 (2 : ZMod 74579611)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (131, 1), (2711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (131, 1), (2711, 1)] : List FactorBlock).map factorBlockValue).prod) = 74579611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_7
      · exact prime_oneHundredTwentyEightDV_131
      · exact prime_oneHundredTwentyEightDV_2711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 74579611) ^ 37289805 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 74579611) ^ 24859870 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 74579611) ^ 14915922 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 74579611) ^ 10654230 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 74579611) ^ 569310 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 74579611) ^ 27510 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_78605887 : Nat.Prime 78605887 := by
  apply lucas_primality 78605887 (3 : ZMod 78605887)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13100981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13100981, 1)] : List FactorBlock).map factorBlockValue).prod) = 78605887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_13100981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 78605887) ^ 39302943 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 78605887) ^ 26201962 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 78605887) ^ 6 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_78945989 : Nat.Prime 78945989 := by
  apply lucas_primality 78945989 (2 : ZMod 78945989)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (19, 1), (94433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (19, 1), (94433, 1)] : List FactorBlock).map factorBlockValue).prod) = 78945989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_11
      · exact prime_oneHundredTwentyEightDV_19
      · exact prime_oneHundredTwentyEightDV_94433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 78945989) ^ 39472994 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 78945989) ^ 7176908 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 78945989) ^ 4155052 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 78945989) ^ 836 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_81036133 : Nat.Prime 81036133 := by
  apply lucas_primality 81036133 (2 : ZMod 81036133)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (73, 1), (92507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (73, 1), (92507, 1)] : List FactorBlock).map factorBlockValue).prod) = 81036133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_73
      · exact prime_oneHundredTwentyEightDV_92507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 81036133) ^ 40518066 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 81036133) ^ 27012044 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 81036133) ^ 1110084 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 81036133) ^ 876 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_91568473 : Nat.Prime 91568473 := by
  apply lucas_primality 91568473 (5 : ZMod 91568473)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (59, 1), (64667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (59, 1), (64667, 1)] : List FactorBlock).map factorBlockValue).prod) = 91568473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_59
      · exact prime_oneHundredTwentyEightDV_64667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 91568473) ^ 45784236 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 91568473) ^ 30522824 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 91568473) ^ 1552008 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 91568473) ^ 1416 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_92103133 : Nat.Prime 92103133 := by
  apply lucas_primality 92103133 (5 : ZMod 92103133)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (23, 2), (1319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (23, 2), (1319, 1)] : List FactorBlock).map factorBlockValue).prod) = 92103133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_11
      · exact prime_oneHundredTwentyEightDV_23
      · exact prime_oneHundredTwentyEightDV_1319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 92103133) ^ 46051566 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 92103133) ^ 30701044 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 92103133) ^ 8373012 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 92103133) ^ 4004484 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 92103133) ^ 69828 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_93706127 : Nat.Prime 93706127 := by
  apply lucas_primality 93706127 (5 : ZMod 93706127)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (61, 1), (20759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (61, 1), (20759, 1)] : List FactorBlock).map factorBlockValue).prod) = 93706127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_37
      · exact prime_oneHundredTwentyEightDV_61
      · exact prime_oneHundredTwentyEightDV_20759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 93706127) ^ 46853063 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 93706127) ^ 2532598 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 93706127) ^ 1536166 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 93706127) ^ 4514 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_97730779 : Nat.Prime 97730779 := by
  apply lucas_primality 97730779 (2 : ZMod 97730779)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (179, 1), (90997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (179, 1), (90997, 1)] : List FactorBlock).map factorBlockValue).prod) = 97730779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_179
      · exact prime_oneHundredTwentyEightDV_90997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 97730779) ^ 48865389 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 97730779) ^ 32576926 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 97730779) ^ 545982 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 97730779) ^ 1074 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_100123619 : Nat.Prime 100123619 := by
  apply lucas_primality 100123619 (2 : ZMod 100123619)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (7151687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (7151687, 1)] : List FactorBlock).map factorBlockValue).prod) = 100123619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_7
      · exact prime_oneHundredTwentyEightDV_7151687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 100123619) ^ 50061809 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 100123619) ^ 14303374 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 100123619) ^ 14 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_102534983 : Nat.Prime 102534983 := by
  apply lucas_primality 102534983 (5 : ZMod 102534983)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (245299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (245299, 1)] : List FactorBlock).map factorBlockValue).prod) = 102534983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_11
      · exact prime_oneHundredTwentyEightDV_19
      · exact prime_oneHundredTwentyEightDV_245299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 102534983) ^ 51267491 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 9321362 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 5396578 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 418 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_105803123 : Nat.Prime 105803123 := by
  apply lucas_primality 105803123 (2 : ZMod 105803123)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1613, 1), (32797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1613, 1), (32797, 1)] : List FactorBlock).map factorBlockValue).prod) = 105803123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_1613
      · exact prime_oneHundredTwentyEightDV_32797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 105803123) ^ 52901561 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 105803123) ^ 65594 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 105803123) ^ 3226 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_127625803 : Nat.Prime 127625803 := by
  apply lucas_primality 127625803 (2 : ZMod 127625803)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (53, 1), (10847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (53, 1), (10847, 1)] : List FactorBlock).map factorBlockValue).prod) = 127625803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_37
      · exact prime_oneHundredTwentyEightDV_53
      · exact prime_oneHundredTwentyEightDV_10847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 127625803) ^ 63812901 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 127625803) ^ 42541934 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 127625803) ^ 3449346 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 127625803) ^ 2408034 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 127625803) ^ 11766 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_129949577 : Nat.Prime 129949577 := by
  apply lucas_primality 129949577 (3 : ZMod 129949577)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (16243697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (16243697, 1)] : List FactorBlock).map factorBlockValue).prod) = 129949577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_16243697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 129949577) ^ 64974788 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 129949577) ^ 8 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_144742421 : Nat.Prime 144742421 := by
  apply lucas_primality 144742421 (3 : ZMod 144742421)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 1), (425713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 1), (425713, 1)] : List FactorBlock).map factorBlockValue).prod) = 144742421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_17
      · exact prime_oneHundredTwentyEightDV_425713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 144742421) ^ 72371210 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 144742421) ^ 28948484 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 144742421) ^ 8514260 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 144742421) ^ 340 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_147701293 : Nat.Prime 147701293 := by
  apply lucas_primality 147701293 (2 : ZMod 147701293)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (424429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (424429, 1)] : List FactorBlock).map factorBlockValue).prod) = 147701293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_29
      · exact prime_oneHundredTwentyEightDV_424429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 147701293) ^ 73850646 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 147701293) ^ 49233764 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 147701293) ^ 5093148 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 147701293) ^ 348 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_158554247 : Nat.Prime 158554247 := by
  apply lucas_primality 158554247 (5 : ZMod 158554247)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (277, 1), (286199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (277, 1), (286199, 1)] : List FactorBlock).map factorBlockValue).prod) = 158554247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_277
      · exact prime_oneHundredTwentyEightDV_286199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 158554247) ^ 79277123 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 158554247) ^ 572398 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 158554247) ^ 554 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_170413949 : Nat.Prime 170413949 := by
  apply lucas_primality 170413949 (2 : ZMod 170413949)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (59, 1), (722093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (59, 1), (722093, 1)] : List FactorBlock).map factorBlockValue).prod) = 170413949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_59
      · exact prime_oneHundredTwentyEightDV_722093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 170413949) ^ 85206974 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 170413949) ^ 2888372 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 170413949) ^ 236 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_175183913 : Nat.Prime 175183913 := by
  apply lucas_primality 175183913 (3 : ZMod 175183913)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (1288117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (1288117, 1)] : List FactorBlock).map factorBlockValue).prod) = 175183913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_17
      · exact prime_oneHundredTwentyEightDV_1288117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 175183913) ^ 87591956 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 175183913) ^ 10304936 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 175183913) ^ 136 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_189175471 : Nat.Prime 189175471 := by
  apply lucas_primality 189175471 (7 : ZMod 189175471)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (47, 1), (12197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (47, 1), (12197, 1)] : List FactorBlock).map factorBlockValue).prod) = 189175471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_11
      · exact prime_oneHundredTwentyEightDV_47
      · exact prime_oneHundredTwentyEightDV_12197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 189175471) ^ 94587735 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 189175471) ^ 63058490 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 189175471) ^ 37835094 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 189175471) ^ 17197770 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 189175471) ^ 4025010 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 189175471) ^ 15510 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_209788487 : Nat.Prime 209788487 := by
  apply lucas_primality 209788487 (5 : ZMod 209788487)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (89, 1), (27409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (89, 1), (27409, 1)] : List FactorBlock).map factorBlockValue).prod) = 209788487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_43
      · exact prime_oneHundredTwentyEightDV_89
      · exact prime_oneHundredTwentyEightDV_27409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 209788487) ^ 104894243 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 209788487) ^ 4878802 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 209788487) ^ 2357174 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 209788487) ^ 7654 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_247392461 : Nat.Prime 247392461 := by
  apply lucas_primality 247392461 (2 : ZMod 247392461)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (1767089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (1767089, 1)] : List FactorBlock).map factorBlockValue).prod) = 247392461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_7
      · exact prime_oneHundredTwentyEightDV_1767089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 247392461) ^ 123696230 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 247392461) ^ 49478492 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 247392461) ^ 35341780 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 247392461) ^ 140 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_248129153 : Nat.Prime 248129153 := by
  apply lucas_primality 248129153 (3 : ZMod 248129153)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (23, 1), (89, 1), (947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (23, 1), (89, 1), (947, 1)] : List FactorBlock).map factorBlockValue).prod) = 248129153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_23
      · exact prime_oneHundredTwentyEightDV_89
      · exact prime_oneHundredTwentyEightDV_947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 248129153) ^ 124064576 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 248129153) ^ 10788224 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 248129153) ^ 2787968 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 248129153) ^ 262016 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_266552171 : Nat.Prime 266552171 := by
  apply lucas_primality 266552171 (2 : ZMod 266552171)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (26655217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (26655217, 1)] : List FactorBlock).map factorBlockValue).prod) = 266552171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_26655217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 266552171) ^ 133276085 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 266552171) ^ 53310434 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 266552171) ^ 10 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_270573497 : Nat.Prime 270573497 := by
  apply lucas_primality 270573497 (3 : ZMod 270573497)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (463, 1), (4297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (463, 1), (4297, 1)] : List FactorBlock).map factorBlockValue).prod) = 270573497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_17
      · exact prime_oneHundredTwentyEightDV_463
      · exact prime_oneHundredTwentyEightDV_4297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 270573497) ^ 135286748 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 270573497) ^ 15916088 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 270573497) ^ 584392 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 270573497) ^ 62968 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_288995191 : Nat.Prime 288995191 := by
  apply lucas_primality 288995191 (6 : ZMod 288995191)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 2), (79613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 2), (79613, 1)] : List FactorBlock).map factorBlockValue).prod) = 288995191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_11
      · exact prime_oneHundredTwentyEightDV_79613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 288995191) ^ 144497595 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 288995191) ^ 96331730 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 288995191) ^ 57799038 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 288995191) ^ 26272290 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 288995191) ^ 3630 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_317375587 : Nat.Prime 317375587 := by
  apply lucas_primality 317375587 (2 : ZMod 317375587)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (1602907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (1602907, 1)] : List FactorBlock).map factorBlockValue).prod) = 317375587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_11
      · exact prime_oneHundredTwentyEightDV_1602907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 317375587) ^ 158687793 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 317375587) ^ 105791862 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 317375587) ^ 28852326 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 317375587) ^ 198 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_328073819 : Nat.Prime 328073819 := by
  apply lucas_primality 328073819 (2 : ZMod 328073819)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (71, 1), (49157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (71, 1), (49157, 1)] : List FactorBlock).map factorBlockValue).prod) = 328073819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_47
      · exact prime_oneHundredTwentyEightDV_71
      · exact prime_oneHundredTwentyEightDV_49157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 328073819) ^ 164036909 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 328073819) ^ 6980294 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 328073819) ^ 4620758 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 328073819) ^ 6674 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_333868229 : Nat.Prime 333868229 := by
  apply lucas_primality 333868229 (2 : ZMod 333868229)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (4393003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (4393003, 1)] : List FactorBlock).map factorBlockValue).prod) = 333868229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_19
      · exact prime_oneHundredTwentyEightDV_4393003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 333868229) ^ 166934114 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 333868229) ^ 17572012 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 333868229) ^ 76 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_345434291 : Nat.Prime 345434291 := by
  apply lucas_primality 345434291 (2 : ZMod 345434291)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (173, 1), (199673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (173, 1), (199673, 1)] : List FactorBlock).map factorBlockValue).prod) = 345434291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_173
      · exact prime_oneHundredTwentyEightDV_199673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 345434291) ^ 172717145 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 345434291) ^ 69086858 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 345434291) ^ 1996730 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 345434291) ^ 1730 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_375770641 : Nat.Prime 375770641 := by
  apply lucas_primality 375770641 (34 : ZMod 375770641)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (7, 1), (47, 1), (4759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (7, 1), (47, 1), (4759, 1)] : List FactorBlock).map factorBlockValue).prod) = 375770641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_7
      · exact prime_oneHundredTwentyEightDV_47
      · exact prime_oneHundredTwentyEightDV_4759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (34 : ZMod 375770641) ^ 187885320 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (34 : ZMod 375770641) ^ 125256880 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (34 : ZMod 375770641) ^ 75154128 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (34 : ZMod 375770641) ^ 53681520 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (34 : ZMod 375770641) ^ 7995120 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (34 : ZMod 375770641) ^ 78960 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_457396609 : Nat.Prime 457396609 := by
  apply lucas_primality 457396609 (7 : ZMod 457396609)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (349, 1), (3413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (349, 1), (3413, 1)] : List FactorBlock).map factorBlockValue).prod) = 457396609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_349
      · exact prime_oneHundredTwentyEightDV_3413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 457396609) ^ 228698304 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 457396609) ^ 152465536 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 457396609) ^ 1310592 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 457396609) ^ 134016 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_459097039 : Nat.Prime 459097039 := by
  apply lucas_primality 459097039 (3 : ZMod 459097039)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (19, 1), (447463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (19, 1), (447463, 1)] : List FactorBlock).map factorBlockValue).prod) = 459097039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_19
      · exact prime_oneHundredTwentyEightDV_447463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 459097039) ^ 229548519 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 459097039) ^ 153032346 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 459097039) ^ 24163002 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 459097039) ^ 1026 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_468045269 : Nat.Prime 468045269 := by
  apply lucas_primality 468045269 (2 : ZMod 468045269)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (4034873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (4034873, 1)] : List FactorBlock).map factorBlockValue).prod) = 468045269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_29
      · exact prime_oneHundredTwentyEightDV_4034873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 468045269) ^ 234022634 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 468045269) ^ 16139492 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 468045269) ^ 116 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_473425327 : Nat.Prime 473425327 := by
  apply lucas_primality 473425327 (3 : ZMod 473425327)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 2), (217367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 2), (217367, 1)] : List FactorBlock).map factorBlockValue).prod) = 473425327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_11
      · exact prime_oneHundredTwentyEightDV_217367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 473425327) ^ 236712663 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 473425327) ^ 157808442 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 473425327) ^ 43038666 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 473425327) ^ 2178 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_486329783 : Nat.Prime 486329783 := by
  apply lucas_primality 486329783 (5 : ZMod 486329783)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (1637, 1), (3623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (1637, 1), (3623, 1)] : List FactorBlock).map factorBlockValue).prod) = 486329783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_41
      · exact prime_oneHundredTwentyEightDV_1637
      · exact prime_oneHundredTwentyEightDV_3623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 486329783) ^ 243164891 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 486329783) ^ 11861702 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 486329783) ^ 297086 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 486329783) ^ 134234 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_494784923 : Nat.Prime 494784923 := by
  apply lucas_primality 494784923 (2 : ZMod 494784923)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (247392461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (247392461, 1)] : List FactorBlock).map factorBlockValue).prod) = 494784923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_247392461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 494784923) ^ 247392461 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 494784923) ^ 2 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_649537433 : Nat.Prime 649537433 := by
  apply lucas_primality 649537433 (3 : ZMod 649537433)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (229, 1), (354551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (229, 1), (354551, 1)] : List FactorBlock).map factorBlockValue).prod) = 649537433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_229
      · exact prime_oneHundredTwentyEightDV_354551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 649537433) ^ 324768716 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 649537433) ^ 2836408 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 649537433) ^ 1832 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_665705087 : Nat.Prime 665705087 := by
  apply lucas_primality 665705087 (5 : ZMod 665705087)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (167, 1), (42407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (167, 1), (42407, 1)] : List FactorBlock).map factorBlockValue).prod) = 665705087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_47
      · exact prime_oneHundredTwentyEightDV_167
      · exact prime_oneHundredTwentyEightDV_42407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 665705087) ^ 332852543 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 665705087) ^ 14163938 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 665705087) ^ 3986258 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 665705087) ^ 15698 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_17203
      · exact prime_oneHundredTwentyEightDV_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_764417231 : Nat.Prime 764417231 := by
  apply lucas_primality 764417231 (7 : ZMod 764417231)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (61, 1), (97, 1), (12919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (61, 1), (97, 1), (12919, 1)] : List FactorBlock).map factorBlockValue).prod) = 764417231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_61
      · exact prime_oneHundredTwentyEightDV_97
      · exact prime_oneHundredTwentyEightDV_12919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 764417231) ^ 382208615 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 764417231) ^ 152883446 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 764417231) ^ 12531430 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 764417231) ^ 7880590 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 764417231) ^ 59170 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_796052281 : Nat.Prime 796052281 := by
  apply lucas_primality 796052281 (7 : ZMod 796052281)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (577, 1), (11497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (577, 1), (11497, 1)] : List FactorBlock).map factorBlockValue).prod) = 796052281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_577
      · exact prime_oneHundredTwentyEightDV_11497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 796052281) ^ 398026140 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 796052281) ^ 265350760 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 796052281) ^ 159210456 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 796052281) ^ 1379640 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 796052281) ^ 69240 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_900641003 : Nat.Prime 900641003 := by
  apply lucas_primality 900641003 (2 : ZMod 900641003)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (23701079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (23701079, 1)] : List FactorBlock).map factorBlockValue).prod) = 900641003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_19
      · exact prime_oneHundredTwentyEightDV_23701079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 900641003) ^ 450320501 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 900641003) ^ 47402158 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 900641003) ^ 38 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_907908979 : Nat.Prime 907908979 := by
  apply lucas_primality 907908979 (2 : ZMod 907908979)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3823, 1), (39581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3823, 1), (39581, 1)] : List FactorBlock).map factorBlockValue).prod) = 907908979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_3823
      · exact prime_oneHundredTwentyEightDV_39581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 907908979) ^ 453954489 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 907908979) ^ 302636326 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 907908979) ^ 237486 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 907908979) ^ 22938 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_912071411 : Nat.Prime 912071411 := by
  apply lucas_primality 912071411 (2 : ZMod 912071411)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (101, 2), (8941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (101, 2), (8941, 1)] : List FactorBlock).map factorBlockValue).prod) = 912071411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_101
      · exact prime_oneHundredTwentyEightDV_8941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 912071411) ^ 456035705 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 912071411) ^ 182414282 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 912071411) ^ 9030410 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 912071411) ^ 102010 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_968413097 : Nat.Prime 968413097 := by
  apply lucas_primality 968413097 (3 : ZMod 968413097)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (17293091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (17293091, 1)] : List FactorBlock).map factorBlockValue).prod) = 968413097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_7
      · exact prime_oneHundredTwentyEightDV_17293091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 968413097) ^ 484206548 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 968413097) ^ 138344728 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 968413097) ^ 56 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_1063332497 : Nat.Prime 1063332497 := by
  apply lucas_primality 1063332497 (3 : ZMod 1063332497)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (109, 1), (609709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (109, 1), (609709, 1)] : List FactorBlock).map factorBlockValue).prod) = 1063332497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_109
      · exact prime_oneHundredTwentyEightDV_609709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1063332497) ^ 531666248 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1063332497) ^ 9755344 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1063332497) ^ 1744 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_1226793751 : Nat.Prime 1226793751 := by
  apply lucas_primality 1226793751 (3 : ZMod 1226793751)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 5), (7, 1), (13, 1), (719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 5), (7, 1), (13, 1), (719, 1)] : List FactorBlock).map factorBlockValue).prod) = 1226793751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_7
      · exact prime_oneHundredTwentyEightDV_13
      · exact prime_oneHundredTwentyEightDV_719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1226793751) ^ 613396875 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1226793751) ^ 408931250 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1226793751) ^ 245358750 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1226793751) ^ 175256250 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1226793751) ^ 94368750 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1226793751) ^ 1706250 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_1282450937 : Nat.Prime 1282450937 := by
  apply lucas_primality 1282450937 (3 : ZMod 1282450937)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (733, 1), (16823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (733, 1), (16823, 1)] : List FactorBlock).map factorBlockValue).prod) = 1282450937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_13
      · exact prime_oneHundredTwentyEightDV_733
      · exact prime_oneHundredTwentyEightDV_16823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1282450937) ^ 641225468 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1282450937) ^ 98650072 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1282450937) ^ 1749592 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1282450937) ^ 76232 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_1298701153 : Nat.Prime 1298701153 := by
  apply lucas_primality 1298701153 (10 : ZMod 1298701153)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (7, 1), (644197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (7, 1), (644197, 1)] : List FactorBlock).map factorBlockValue).prod) = 1298701153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_7
      · exact prime_oneHundredTwentyEightDV_644197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 1298701153) ^ 649350576 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (10 : ZMod 1298701153) ^ 432900384 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (10 : ZMod 1298701153) ^ 185528736 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (10 : ZMod 1298701153) ^ 2016 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_1299989947 : Nat.Prime 1299989947 := by
  apply lucas_primality 1299989947 (2 : ZMod 1299989947)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (1667, 1), (5651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (1667, 1), (5651, 1)] : List FactorBlock).map factorBlockValue).prod) = 1299989947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_23
      · exact prime_oneHundredTwentyEightDV_1667
      · exact prime_oneHundredTwentyEightDV_5651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1299989947) ^ 649994973 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299989947) ^ 433329982 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299989947) ^ 56521302 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299989947) ^ 779838 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299989947) ^ 230046 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_1305718679 : Nat.Prime 1305718679 := by
  apply lucas_primality 1305718679 (11 : ZMod 1305718679)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (29, 1), (37, 1), (55313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (29, 1), (37, 1), (55313, 1)] : List FactorBlock).map factorBlockValue).prod) = 1305718679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_11
      · exact prime_oneHundredTwentyEightDV_29
      · exact prime_oneHundredTwentyEightDV_37
      · exact prime_oneHundredTwentyEightDV_55313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1305718679) ^ 652859339 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (11 : ZMod 1305718679) ^ 118701698 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (11 : ZMod 1305718679) ^ 45024782 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (11 : ZMod 1305718679) ^ 35289694 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (11 : ZMod 1305718679) ^ 23606 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_1403802133 : Nat.Prime 1403802133 := by
  apply lucas_primality 1403802133 (2 : ZMod 1403802133)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (6881383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (6881383, 1)] : List FactorBlock).map factorBlockValue).prod) = 1403802133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_17
      · exact prime_oneHundredTwentyEightDV_6881383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1403802133) ^ 701901066 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1403802133) ^ 467934044 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1403802133) ^ 82576596 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1403802133) ^ 204 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_1405006411 : Nat.Prime 1405006411 := by
  apply lucas_primality 1405006411 (2 : ZMod 1405006411)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (46833547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (46833547, 1)] : List FactorBlock).map factorBlockValue).prod) = 1405006411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_46833547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1405006411) ^ 702503205 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1405006411) ^ 468335470 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1405006411) ^ 281001282 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1405006411) ^ 30 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_1437161029 : Nat.Prime 1437161029 := by
  apply lucas_primality 1437161029 (2 : ZMod 1437161029)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (41, 1), (171827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (41, 1), (171827, 1)] : List FactorBlock).map factorBlockValue).prod) = 1437161029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_17
      · exact prime_oneHundredTwentyEightDV_41
      · exact prime_oneHundredTwentyEightDV_171827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1437161029) ^ 718580514 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1437161029) ^ 479053676 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1437161029) ^ 84538884 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1437161029) ^ 35052708 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1437161029) ^ 8364 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_1545249437 : Nat.Prime 1545249437 := by
  apply lucas_primality 1545249437 (2 : ZMod 1545249437)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (12461689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (12461689, 1)] : List FactorBlock).map factorBlockValue).prod) = 1545249437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_31
      · exact prime_oneHundredTwentyEightDV_12461689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1545249437) ^ 772624718 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1545249437) ^ 49846756 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1545249437) ^ 124 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_1725109657 : Nat.Prime 1725109657 := by
  apply lucas_primality 1725109657 (5 : ZMod 1725109657)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (131, 1), (193, 1), (2843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (131, 1), (193, 1), (2843, 1)] : List FactorBlock).map factorBlockValue).prod) = 1725109657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_131
      · exact prime_oneHundredTwentyEightDV_193
      · exact prime_oneHundredTwentyEightDV_2843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1725109657) ^ 862554828 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1725109657) ^ 575036552 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1725109657) ^ 13168776 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1725109657) ^ 8938392 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1725109657) ^ 606792 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_1953042799 : Nat.Prime 1953042799 := by
  apply lucas_primality 1953042799 (3 : ZMod 1953042799)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (46501019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (46501019, 1)] : List FactorBlock).map factorBlockValue).prod) = 1953042799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_7
      · exact prime_oneHundredTwentyEightDV_46501019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1953042799) ^ 976521399 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1953042799) ^ 651014266 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1953042799) ^ 279006114 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1953042799) ^ 42 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_2075756107 : Nat.Prime 2075756107 := by
  apply lucas_primality 2075756107 (2 : ZMod 2075756107)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (109, 1), (1259, 1), (2521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (109, 1), (1259, 1), (2521, 1)] : List FactorBlock).map factorBlockValue).prod) = 2075756107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_109
      · exact prime_oneHundredTwentyEightDV_1259
      · exact prime_oneHundredTwentyEightDV_2521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2075756107) ^ 1037878053 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2075756107) ^ 691918702 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2075756107) ^ 19043634 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2075756107) ^ 1648734 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2075756107) ^ 823386 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_2156978093 : Nat.Prime 2156978093 := by
  apply lucas_primality 2156978093 (2 : ZMod 2156978093)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (139, 1), (827, 1), (4691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (139, 1), (827, 1), (4691, 1)] : List FactorBlock).map factorBlockValue).prod) = 2156978093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_139
      · exact prime_oneHundredTwentyEightDV_827
      · exact prime_oneHundredTwentyEightDV_4691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2156978093) ^ 1078489046 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2156978093) ^ 15517828 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2156978093) ^ 2608196 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2156978093) ^ 459812 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_2416168199 : Nat.Prime 2416168199 := by
  apply lucas_primality 2416168199 (7 : ZMod 2416168199)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (71, 1), (362027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (71, 1), (362027, 1)] : List FactorBlock).map factorBlockValue).prod) = 2416168199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_47
      · exact prime_oneHundredTwentyEightDV_71
      · exact prime_oneHundredTwentyEightDV_362027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2416168199) ^ 1208084099 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 51407834 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 34030538 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 6674 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_2503053647 : Nat.Prime 2503053647 := by
  apply lucas_primality 2503053647 (5 : ZMod 2503053647)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (40371833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (40371833, 1)] : List FactorBlock).map factorBlockValue).prod) = 2503053647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_31
      · exact prime_oneHundredTwentyEightDV_40371833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2503053647) ^ 1251526823 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 2503053647) ^ 80743666 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 2503053647) ^ 62 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_2652445933 : Nat.Prime 2652445933 := by
  apply lucas_primality 2652445933 (2 : ZMod 2652445933)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (31, 1), (7130231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (31, 1), (7130231, 1)] : List FactorBlock).map factorBlockValue).prod) = 2652445933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_31
      · exact prime_oneHundredTwentyEightDV_7130231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2652445933) ^ 1326222966 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2652445933) ^ 884148644 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2652445933) ^ 85562772 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2652445933) ^ 372 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_2977549837 : Nat.Prime 2977549837 := by
  apply lucas_primality 2977549837 (2 : ZMod 2977549837)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (248129153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (248129153, 1)] : List FactorBlock).map factorBlockValue).prod) = 2977549837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_248129153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2977549837) ^ 1488774918 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2977549837) ^ 992516612 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2977549837) ^ 12 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_3244440161 : Nat.Prime 3244440161 := by
  apply lucas_primality 3244440161 (3 : ZMod 3244440161)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (13, 1), (31, 1), (67, 1), (751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (13, 1), (31, 1), (67, 1), (751, 1)] : List FactorBlock).map factorBlockValue).prod) = 3244440161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_13
      · exact prime_oneHundredTwentyEightDV_31
      · exact prime_oneHundredTwentyEightDV_67
      · exact prime_oneHundredTwentyEightDV_751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3244440161) ^ 1622220080 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3244440161) ^ 648888032 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3244440161) ^ 249572320 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3244440161) ^ 104659360 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3244440161) ^ 48424480 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3244440161) ^ 4320160 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_4853859953 : Nat.Prime 4853859953 := by
  apply lucas_primality 4853859953 (3 : ZMod 4853859953)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (43, 1), (47, 1), (150107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (43, 1), (47, 1), (150107, 1)] : List FactorBlock).map factorBlockValue).prod) = 4853859953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_43
      · exact prime_oneHundredTwentyEightDV_47
      · exact prime_oneHundredTwentyEightDV_150107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4853859953) ^ 2426929976 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 4853859953) ^ 112880464 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 4853859953) ^ 103273616 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 4853859953) ^ 32336 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_5607137911 : Nat.Prime 5607137911 := by
  apply lucas_primality 5607137911 (7 : ZMod 5607137911)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (16991327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (16991327, 1)] : List FactorBlock).map factorBlockValue).prod) = 5607137911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_11
      · exact prime_oneHundredTwentyEightDV_16991327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 5607137911) ^ 2803568955 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 5607137911) ^ 1869045970 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 5607137911) ^ 1121427582 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 5607137911) ^ 509739810 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 5607137911) ^ 330 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_5748644117 : Nat.Prime 5748644117 := by
  apply lucas_primality 5748644117 (2 : ZMod 5748644117)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1437161029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1437161029, 1)] : List FactorBlock).map factorBlockValue).prod) = 5748644117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_1437161029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 5748644117) ^ 2874322058 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 5748644117) ^ 4 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_31
      · exact prime_oneHundredTwentyEightDV_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_6237579697 : Nat.Prime 6237579697 := by
  apply lucas_primality 6237579697 (5 : ZMod 6237579697)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (129949577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (129949577, 1)] : List FactorBlock).map factorBlockValue).prod) = 6237579697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_129949577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 6237579697) ^ 3118789848 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 6237579697) ^ 2079193232 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 6237579697) ^ 48 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_7729837097 : Nat.Prime 7729837097 := by
  apply lucas_primality 7729837097 (3 : ZMod 7729837097)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (283, 1), (3414239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (283, 1), (3414239, 1)] : List FactorBlock).map factorBlockValue).prod) = 7729837097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_283
      · exact prime_oneHundredTwentyEightDV_3414239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 7729837097) ^ 3864918548 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 7729837097) ^ 27313912 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 7729837097) ^ 2264 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_8528447371 : Nat.Prime 8528447371 := by
  apply lucas_primality 8528447371 (3 : ZMod 8528447371)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (79, 1), (3598501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (79, 1), (3598501, 1)] : List FactorBlock).map factorBlockValue).prod) = 8528447371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_79
      · exact prime_oneHundredTwentyEightDV_3598501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8528447371) ^ 4264223685 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 8528447371) ^ 2842815790 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 8528447371) ^ 1705689474 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 8528447371) ^ 107955030 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 8528447371) ^ 2370 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_9956251801 : Nat.Prime 9956251801 := by
  apply lucas_primality 9956251801 (13 : ZMod 9956251801)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 2), (11, 1), (502841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 2), (11, 1), (502841, 1)] : List FactorBlock).map factorBlockValue).prod) = 9956251801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_11
      · exact prime_oneHundredTwentyEightDV_502841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 9956251801) ^ 4978125900 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (13 : ZMod 9956251801) ^ 3318750600 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (13 : ZMod 9956251801) ^ 1991250360 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (13 : ZMod 9956251801) ^ 905113800 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (13 : ZMod 9956251801) ^ 19800 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_11211686891 : Nat.Prime 11211686891 := by
  apply lucas_primality 11211686891 (6 : ZMod 11211686891)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (89, 1), (12597401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (89, 1), (12597401, 1)] : List FactorBlock).map factorBlockValue).prod) = 11211686891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_89
      · exact prime_oneHundredTwentyEightDV_12597401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 11211686891) ^ 5605843445 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 11211686891) ^ 2242337378 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 11211686891) ^ 125974010 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 11211686891) ^ 890 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_12320745817 : Nat.Prime 12320745817 := by
  apply lucas_primality 12320745817 (10 : ZMod 12320745817)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (29, 1), (47, 1), (157, 1), (2399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (29, 1), (47, 1), (157, 1), (2399, 1)] : List FactorBlock).map factorBlockValue).prod) = 12320745817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_29
      · exact prime_oneHundredTwentyEightDV_47
      · exact prime_oneHundredTwentyEightDV_157
      · exact prime_oneHundredTwentyEightDV_2399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 12320745817) ^ 6160372908 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (10 : ZMod 12320745817) ^ 4106915272 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (10 : ZMod 12320745817) ^ 424853304 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (10 : ZMod 12320745817) ^ 262143528 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (10 : ZMod 12320745817) ^ 78476088 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (10 : ZMod 12320745817) ^ 5135784 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_12347476763 : Nat.Prime 12347476763 := by
  apply lucas_primality 12347476763 (2 : ZMod 12347476763)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (31, 1), (983, 1), (10663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (31, 1), (983, 1), (10663, 1)] : List FactorBlock).map factorBlockValue).prod) = 12347476763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_19
      · exact prime_oneHundredTwentyEightDV_31
      · exact prime_oneHundredTwentyEightDV_983
      · exact prime_oneHundredTwentyEightDV_10663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12347476763) ^ 6173738381 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 12347476763) ^ 649867198 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 12347476763) ^ 398305702 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 12347476763) ^ 12561014 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 12347476763) ^ 1157974 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_12361995497 : Nat.Prime 12361995497 := by
  apply lucas_primality 12361995497 (3 : ZMod 12361995497)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1545249437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1545249437, 1)] : List FactorBlock).map factorBlockValue).prod) = 12361995497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_1545249437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 12361995497) ^ 6180997748 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 12361995497) ^ 8 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_14680302479 : Nat.Prime 14680302479 := by
  apply lucas_primality 14680302479 (13 : ZMod 14680302479)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (743, 1), (240953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (743, 1), (240953, 1)] : List FactorBlock).map factorBlockValue).prod) = 14680302479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_41
      · exact prime_oneHundredTwentyEightDV_743
      · exact prime_oneHundredTwentyEightDV_240953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 14680302479) ^ 7340151239 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (13 : ZMod 14680302479) ^ 358056158 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (13 : ZMod 14680302479) ^ 19758146 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (13 : ZMod 14680302479) ^ 60926 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_15980700217 : Nat.Prime 15980700217 := by
  apply lucas_primality 15980700217 (5 : ZMod 15980700217)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (41, 1), (1249273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (41, 1), (1249273, 1)] : List FactorBlock).map factorBlockValue).prod) = 15980700217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_13
      · exact prime_oneHundredTwentyEightDV_41
      · exact prime_oneHundredTwentyEightDV_1249273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 15980700217) ^ 7990350108 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 15980700217) ^ 5326900072 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 15980700217) ^ 1229284632 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 15980700217) ^ 389773176 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 15980700217) ^ 12792 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_16932946997 : Nat.Prime 16932946997 := by
  apply lucas_primality 16932946997 (2 : ZMod 16932946997)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (29, 1), (47, 1), (443689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (29, 1), (47, 1), (443689, 1)] : List FactorBlock).map factorBlockValue).prod) = 16932946997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_7
      · exact prime_oneHundredTwentyEightDV_29
      · exact prime_oneHundredTwentyEightDV_47
      · exact prime_oneHundredTwentyEightDV_443689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16932946997) ^ 8466473498 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 16932946997) ^ 2418992428 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 16932946997) ^ 583894724 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 16932946997) ^ 360275468 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 16932946997) ^ 38164 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_17365302179 : Nat.Prime 17365302179 := by
  apply lucas_primality 17365302179 (6 : ZMod 17365302179)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (31, 1), (5716031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (31, 1), (5716031, 1)] : List FactorBlock).map factorBlockValue).prod) = 17365302179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_7
      · exact prime_oneHundredTwentyEightDV_31
      · exact prime_oneHundredTwentyEightDV_5716031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 17365302179) ^ 8682651089 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 17365302179) ^ 2480757454 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 17365302179) ^ 560171038 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 17365302179) ^ 3038 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_20884988987 : Nat.Prime 20884988987 := by
  apply lucas_primality 20884988987 (2 : ZMod 20884988987)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (1289, 1), (279353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (1289, 1), (279353, 1)] : List FactorBlock).map factorBlockValue).prod) = 20884988987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_29
      · exact prime_oneHundredTwentyEightDV_1289
      · exact prime_oneHundredTwentyEightDV_279353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 20884988987) ^ 10442494493 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 20884988987) ^ 720172034 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 20884988987) ^ 16202474 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 20884988987) ^ 74762 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_29378357623 : Nat.Prime 29378357623 := by
  apply lucas_primality 29378357623 (3 : ZMod 29378357623)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (223, 1), (7318973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (223, 1), (7318973, 1)] : List FactorBlock).map factorBlockValue).prod) = 29378357623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_223
      · exact prime_oneHundredTwentyEightDV_7318973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 29378357623) ^ 14689178811 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 29378357623) ^ 9792785874 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 29378357623) ^ 131741514 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 29378357623) ^ 4014 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_40574108527 : Nat.Prime 40574108527 := by
  apply lucas_primality 40574108527 (10 : ZMod 40574108527)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (701, 1), (1378103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (701, 1), (1378103, 1)] : List FactorBlock).map factorBlockValue).prod) = 40574108527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_7
      · exact prime_oneHundredTwentyEightDV_701
      · exact prime_oneHundredTwentyEightDV_1378103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 40574108527) ^ 20287054263 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (10 : ZMod 40574108527) ^ 13524702842 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (10 : ZMod 40574108527) ^ 5796301218 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (10 : ZMod 40574108527) ^ 57880326 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (10 : ZMod 40574108527) ^ 29442 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_52741006361 : Nat.Prime 52741006361 := by
  apply lucas_primality 52741006361 (6 : ZMod 52741006361)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (19, 1), (9913723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (19, 1), (9913723, 1)] : List FactorBlock).map factorBlockValue).prod) = 52741006361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_7
      · exact prime_oneHundredTwentyEightDV_19
      · exact prime_oneHundredTwentyEightDV_9913723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 52741006361) ^ 26370503180 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 52741006361) ^ 10548201272 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 52741006361) ^ 7534429480 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 52741006361) ^ 2775842440 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 52741006361) ^ 5320 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_52800401701 : Nat.Prime 52800401701 := by
  apply lucas_primality 52800401701 (6 : ZMod 52800401701)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (58667113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (58667113, 1)] : List FactorBlock).map factorBlockValue).prod) = 52800401701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_58667113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 52800401701) ^ 26400200850 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 52800401701) ^ 17600133900 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 52800401701) ^ 10560080340 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 52800401701) ^ 900 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_106526549111 : Nat.Prime 106526549111 := by
  apply lucas_primality 106526549111 (13 : ZMod 106526549111)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (109, 1), (97730779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (109, 1), (97730779, 1)] : List FactorBlock).map factorBlockValue).prod) = 106526549111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_109
      · exact prime_oneHundredTwentyEightDV_97730779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 106526549111) ^ 53263274555 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (13 : ZMod 106526549111) ^ 21305309822 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (13 : ZMod 106526549111) ^ 977307790 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (13 : ZMod 106526549111) ^ 1090 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_153088976401 : Nat.Prime 153088976401 := by
  apply lucas_primality 153088976401 (19 : ZMod 153088976401)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 2), (3221, 1), (39607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 2), (3221, 1), (39607, 1)] : List FactorBlock).map factorBlockValue).prod) = 153088976401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_3221
      · exact prime_oneHundredTwentyEightDV_39607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 153088976401) ^ 76544488200 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (19 : ZMod 153088976401) ^ 51029658800 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (19 : ZMod 153088976401) ^ 30617795280 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (19 : ZMod 153088976401) ^ 47528400 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (19 : ZMod 153088976401) ^ 3865200 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_157823669221 : Nat.Prime 157823669221 := by
  apply lucas_primality 157823669221 (17 : ZMod 157823669221)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (375770641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (375770641, 1)] : List FactorBlock).map factorBlockValue).prod) = 157823669221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_7
      · exact prime_oneHundredTwentyEightDV_375770641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 157823669221) ^ 78911834610 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (17 : ZMod 157823669221) ^ 52607889740 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (17 : ZMod 157823669221) ^ 31564733844 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (17 : ZMod 157823669221) ^ 22546238460 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (17 : ZMod 157823669221) ^ 420 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_162296434109 : Nat.Prime 162296434109 := by
  apply lucas_primality 162296434109 (2 : ZMod 162296434109)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (40574108527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (40574108527, 1)] : List FactorBlock).map factorBlockValue).prod) = 162296434109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_40574108527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 162296434109) ^ 81148217054 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 162296434109) ^ 4 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_215565659143 : Nat.Prime 215565659143 := by
  apply lucas_primality 215565659143 (3 : ZMod 215565659143)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (764417231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (764417231, 1)] : List FactorBlock).map factorBlockValue).prod) = 215565659143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_47
      · exact prime_oneHundredTwentyEightDV_764417231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 215565659143) ^ 107782829571 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 215565659143) ^ 71855219714 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 215565659143) ^ 4586503386 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 215565659143) ^ 282 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_254356807027 : Nat.Prime 254356807027 := by
  apply lucas_primality 254356807027 (3 : ZMod 254356807027)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (37, 1), (43, 1), (47, 1), (80989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (37, 1), (43, 1), (47, 1), (80989, 1)] : List FactorBlock).map factorBlockValue).prod) = 254356807027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_7
      · exact prime_oneHundredTwentyEightDV_37
      · exact prime_oneHundredTwentyEightDV_43
      · exact prime_oneHundredTwentyEightDV_47
      · exact prime_oneHundredTwentyEightDV_80989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 254356807027) ^ 127178403513 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 254356807027) ^ 84785602342 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 254356807027) ^ 36336686718 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 254356807027) ^ 6874508298 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 254356807027) ^ 5915274582 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 254356807027) ^ 5411846958 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 254356807027) ^ 3140634 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_318009598661 : Nat.Prime 318009598661 := by
  apply lucas_primality 318009598661 (2 : ZMod 318009598661)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (17, 1), (71947873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (17, 1), (71947873, 1)] : List FactorBlock).map factorBlockValue).prod) = 318009598661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_13
      · exact prime_oneHundredTwentyEightDV_17
      · exact prime_oneHundredTwentyEightDV_71947873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 318009598661) ^ 159004799330 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 318009598661) ^ 63601919732 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 318009598661) ^ 24462276820 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 318009598661) ^ 18706446980 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 318009598661) ^ 4420 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_324699246947 : Nat.Prime 324699246947 := by
  apply lucas_primality 324699246947 (2 : ZMod 324699246947)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (659, 1), (1289, 1), (191123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (659, 1), (1289, 1), (191123, 1)] : List FactorBlock).map factorBlockValue).prod) = 324699246947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_659
      · exact prime_oneHundredTwentyEightDV_1289
      · exact prime_oneHundredTwentyEightDV_191123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 324699246947) ^ 162349623473 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 324699246947) ^ 492715094 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 324699246947) ^ 251900114 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 324699246947) ^ 1698902 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_325247041321 : Nat.Prime 325247041321 := by
  apply lucas_primality 325247041321 (7 : ZMod 325247041321)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (719, 1), (3769669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (719, 1), (3769669, 1)] : List FactorBlock).map factorBlockValue).prod) = 325247041321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_719
      · exact prime_oneHundredTwentyEightDV_3769669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 325247041321) ^ 162623520660 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 325247041321) ^ 108415680440 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 325247041321) ^ 65049408264 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 325247041321) ^ 452360280 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 325247041321) ^ 86280 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_406155387923 : Nat.Prime 406155387923 := by
  apply lucas_primality 406155387923 (2 : ZMod 406155387923)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (619, 1), (328073819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (619, 1), (328073819, 1)] : List FactorBlock).map factorBlockValue).prod) = 406155387923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_619
      · exact prime_oneHundredTwentyEightDV_328073819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 406155387923) ^ 203077693961 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 406155387923) ^ 656147638 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 406155387923) ^ 1238 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_436648205893 : Nat.Prime 436648205893 := by
  apply lucas_primality 436648205893 (2 : ZMod 436648205893)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (1621, 1), (975977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (1621, 1), (975977, 1)] : List FactorBlock).map factorBlockValue).prod) = 436648205893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_23
      · exact prime_oneHundredTwentyEightDV_1621
      · exact prime_oneHundredTwentyEightDV_975977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 436648205893) ^ 218324102946 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 436648205893) ^ 145549401964 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 436648205893) ^ 18984704604 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 436648205893) ^ 269369652 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 436648205893) ^ 447396 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_481378880701 : Nat.Prime 481378880701 := by
  apply lucas_primality 481378880701 (7 : ZMod 481378880701)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (6353, 1), (84191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (6353, 1), (84191, 1)] : List FactorBlock).map factorBlockValue).prod) = 481378880701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_6353
      · exact prime_oneHundredTwentyEightDV_84191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 481378880701) ^ 240689440350 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 481378880701) ^ 160459626900 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 481378880701) ^ 96275776140 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 481378880701) ^ 75771900 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 481378880701) ^ 5717700 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_484509340493 : Nat.Prime 484509340493 := by
  apply lucas_primality 484509340493 (2 : ZMod 484509340493)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7541, 1), (16062503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7541, 1), (16062503, 1)] : List FactorBlock).map factorBlockValue).prod) = 484509340493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_7541
      · exact prime_oneHundredTwentyEightDV_16062503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 484509340493) ^ 242254670246 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 484509340493) ^ 64250012 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 484509340493) ^ 30164 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_631662907333 : Nat.Prime 631662907333 := by
  apply lucas_primality 631662907333 (6 : ZMod 631662907333)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (25733, 1), (2045567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (25733, 1), (2045567, 1)] : List FactorBlock).map factorBlockValue).prod) = 631662907333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_25733
      · exact prime_oneHundredTwentyEightDV_2045567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 631662907333) ^ 315831453666 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 631662907333) ^ 210554302444 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 631662907333) ^ 24546804 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 631662907333) ^ 308796 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_711802770691 : Nat.Prime 711802770691 := by
  apply lucas_primality 711802770691 (2 : ZMod 711802770691)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (2156978093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (2156978093, 1)] : List FactorBlock).map factorBlockValue).prod) = 711802770691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_11
      · exact prime_oneHundredTwentyEightDV_2156978093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 711802770691) ^ 355901385345 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 711802770691) ^ 237267590230 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 711802770691) ^ 142360554138 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 711802770691) ^ 64709342790 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 711802770691) ^ 330 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_869608720249 : Nat.Prime 869608720249 := by
  apply lucas_primality 869608720249 (14 : ZMod 869608720249)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (809, 1), (44788253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (809, 1), (44788253, 1)] : List FactorBlock).map factorBlockValue).prod) = 869608720249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_809
      · exact prime_oneHundredTwentyEightDV_44788253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 869608720249) ^ 434804360124 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (14 : ZMod 869608720249) ^ 289869573416 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (14 : ZMod 869608720249) ^ 1074918072 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (14 : ZMod 869608720249) ^ 19416 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_1181699726089 : Nat.Prime 1181699726089 := by
  apply lucas_primality 1181699726089 (31 : ZMod 1181699726089)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (101, 1), (167, 1), (417023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (101, 1), (167, 1), (417023, 1)] : List FactorBlock).map factorBlockValue).prod) = 1181699726089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_7
      · exact prime_oneHundredTwentyEightDV_101
      · exact prime_oneHundredTwentyEightDV_167
      · exact prime_oneHundredTwentyEightDV_417023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 1181699726089) ^ 590849863044 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (31 : ZMod 1181699726089) ^ 393899908696 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (31 : ZMod 1181699726089) ^ 168814246584 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (31 : ZMod 1181699726089) ^ 11699997288 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (31 : ZMod 1181699726089) ^ 7076046264 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (31 : ZMod 1181699726089) ^ 2833656 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_1264130673683 : Nat.Prime 1264130673683 := by
  apply lucas_primality 1264130673683 (2 : ZMod 1264130673683)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3709, 1), (170413949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3709, 1), (170413949, 1)] : List FactorBlock).map factorBlockValue).prod) = 1264130673683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3709
      · exact prime_oneHundredTwentyEightDV_170413949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1264130673683) ^ 632065336841 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1264130673683) ^ 340827898 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1264130673683) ^ 7418 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_1298371472873 : Nat.Prime 1298371472873 := by
  apply lucas_primality 1298371472873 (3 : ZMod 1298371472873)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (162296434109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (162296434109, 1)] : List FactorBlock).map factorBlockValue).prod) = 1298371472873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_162296434109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1298371472873) ^ 649185736436 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1298371472873) ^ 8 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_1483998585427 : Nat.Prime 1483998585427 := by
  apply lucas_primality 1483998585427 (3 : ZMod 1483998585427)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (42863, 1), (274777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (42863, 1), (274777, 1)] : List FactorBlock).map factorBlockValue).prod) = 1483998585427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_7
      · exact prime_oneHundredTwentyEightDV_42863
      · exact prime_oneHundredTwentyEightDV_274777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1483998585427) ^ 741999292713 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1483998585427) ^ 494666195142 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1483998585427) ^ 211999797918 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1483998585427) ^ 34621902 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1483998585427) ^ 5400738 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_1985543889911 : Nat.Prime 1985543889911 := by
  apply lucas_primality 1985543889911 (7 : ZMod 1985543889911)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (109, 1), (1013, 1), (256889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (109, 1), (1013, 1), (256889, 1)] : List FactorBlock).map factorBlockValue).prod) = 1985543889911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_7
      · exact prime_oneHundredTwentyEightDV_109
      · exact prime_oneHundredTwentyEightDV_1013
      · exact prime_oneHundredTwentyEightDV_256889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1985543889911) ^ 992771944955 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1985543889911) ^ 397108777982 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1985543889911) ^ 283649127130 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1985543889911) ^ 18215998990 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1985543889911) ^ 1960063070 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1985543889911) ^ 7729190 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_2596742945747 : Nat.Prime 2596742945747 := by
  apply lucas_primality 2596742945747 (2 : ZMod 2596742945747)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1298371472873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1298371472873, 1)] : List FactorBlock).map factorBlockValue).prod) = 2596742945747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_1298371472873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 2596742945747) ^ 1298371472873 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2596742945747) ^ 2 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_3207065946347 : Nat.Prime 3207065946347 := by
  apply lucas_primality 3207065946347 (2 : ZMod 3207065946347)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (521, 1), (3373, 1), (912481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (521, 1), (3373, 1), (912481, 1)] : List FactorBlock).map factorBlockValue).prod) = 3207065946347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_521
      · exact prime_oneHundredTwentyEightDV_3373
      · exact prime_oneHundredTwentyEightDV_912481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3207065946347) ^ 1603532973173 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3207065946347) ^ 6155596826 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3207065946347) ^ 950805202 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3207065946347) ^ 3514666 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_3277333204279 : Nat.Prime 3277333204279 := by
  apply lucas_primality 3277333204279 (6 : ZMod 3277333204279)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (17, 2), (14851, 1), (18181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (17, 2), (14851, 1), (18181, 1)] : List FactorBlock).map factorBlockValue).prod) = 3277333204279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_7
      · exact prime_oneHundredTwentyEightDV_17
      · exact prime_oneHundredTwentyEightDV_14851
      · exact prime_oneHundredTwentyEightDV_18181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3277333204279) ^ 1638666602139 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 3277333204279) ^ 1092444401426 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 3277333204279) ^ 468190457754 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 3277333204279) ^ 192784306134 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 3277333204279) ^ 220680978 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 3277333204279) ^ 180261438 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_3535327911859 : Nat.Prime 3535327911859 := by
  apply lucas_primality 3535327911859 (2 : ZMod 3535327911859)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1627, 1), (12641, 1), (28649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1627, 1), (12641, 1), (28649, 1)] : List FactorBlock).map factorBlockValue).prod) = 3535327911859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_1627
      · exact prime_oneHundredTwentyEightDV_12641
      · exact prime_oneHundredTwentyEightDV_28649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3535327911859) ^ 1767663955929 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3535327911859) ^ 1178442637286 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3535327911859) ^ 2172912054 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3535327911859) ^ 279671538 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3535327911859) ^ 123401442 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_3743896788893 : Nat.Prime 3743896788893 := by
  apply lucas_primality 3743896788893 (2 : ZMod 3743896788893)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (17, 1), (227, 1), (18657169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (17, 1), (227, 1), (18657169, 1)] : List FactorBlock).map factorBlockValue).prod) = 3743896788893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_13
      · exact prime_oneHundredTwentyEightDV_17
      · exact prime_oneHundredTwentyEightDV_227
      · exact prime_oneHundredTwentyEightDV_18657169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3743896788893) ^ 1871948394446 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3743896788893) ^ 287992060684 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3743896788893) ^ 220229222876 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3743896788893) ^ 16492937396 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3743896788893) ^ 200668 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_3965637126181 : Nat.Prime 3965637126181 := by
  apply lucas_primality 3965637126181 (6 : ZMod 3965637126181)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (113, 1), (743, 1), (787217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (113, 1), (743, 1), (787217, 1)] : List FactorBlock).map factorBlockValue).prod) = 3965637126181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_113
      · exact prime_oneHundredTwentyEightDV_743
      · exact prime_oneHundredTwentyEightDV_787217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3965637126181) ^ 1982818563090 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 3965637126181) ^ 1321879042060 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 3965637126181) ^ 793127425236 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 3965637126181) ^ 35094133860 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 3965637126181) ^ 5337331260 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 3965637126181) ^ 5037540 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_4325367059753 : Nat.Prime 4325367059753 := by
  apply lucas_primality 4325367059753 (3 : ZMod 4325367059753)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (3739, 1), (8506063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (3739, 1), (8506063, 1)] : List FactorBlock).map factorBlockValue).prod) = 4325367059753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_17
      · exact prime_oneHundredTwentyEightDV_3739
      · exact prime_oneHundredTwentyEightDV_8506063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4325367059753) ^ 2162683529876 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 4325367059753) ^ 254433356456 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 4325367059753) ^ 1156824568 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 4325367059753) ^ 508504 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_4808394801193 : Nat.Prime 4808394801193 := by
  apply lucas_primality 4808394801193 (5 : ZMod 4808394801193)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (8893, 1), (22528931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (8893, 1), (22528931, 1)] : List FactorBlock).map factorBlockValue).prod) = 4808394801193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_8893
      · exact prime_oneHundredTwentyEightDV_22528931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4808394801193) ^ 2404197400596 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 4808394801193) ^ 1602798267064 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 4808394801193) ^ 540694344 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 4808394801193) ^ 213432 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_6357293089201 : Nat.Prime 6357293089201 := by
  apply lucas_primality 6357293089201 (7 : ZMod 6357293089201)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5, 2), (1553, 1), (379033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5, 2), (1553, 1), (379033, 1)] : List FactorBlock).map factorBlockValue).prod) = 6357293089201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_1553
      · exact prime_oneHundredTwentyEightDV_379033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6357293089201) ^ 3178646544600 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 6357293089201) ^ 2119097696400 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 6357293089201) ^ 1271458617840 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 6357293089201) ^ 4093556400 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 6357293089201) ^ 16772400 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_7764707437133 : Nat.Prime 7764707437133 := by
  apply lucas_primality 7764707437133 (2 : ZMod 7764707437133)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (89, 1), (11027, 1), (1977961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (89, 1), (11027, 1), (1977961, 1)] : List FactorBlock).map factorBlockValue).prod) = 7764707437133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_89
      · exact prime_oneHundredTwentyEightDV_11027
      · exact prime_oneHundredTwentyEightDV_1977961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7764707437133) ^ 3882353718566 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 7764707437133) ^ 87243903788 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 7764707437133) ^ 704154116 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 7764707437133) ^ 3925612 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_9785892628279 : Nat.Prime 9785892628279 := by
  apply lucas_primality 9785892628279 (6 : ZMod 9785892628279)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (13, 1), (229, 1), (20291147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (13, 1), (229, 1), (20291147, 1)] : List FactorBlock).map factorBlockValue).prod) = 9785892628279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_13
      · exact prime_oneHundredTwentyEightDV_229
      · exact prime_oneHundredTwentyEightDV_20291147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 9785892628279) ^ 4892946314139 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 9785892628279) ^ 3261964209426 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 9785892628279) ^ 752760971406 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 9785892628279) ^ 42733155582 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 9785892628279) ^ 482274 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_14286766865669 : Nat.Prime 14286766865669 := by
  apply lucas_primality 14286766865669 (2 : ZMod 14286766865669)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (324699246947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (324699246947, 1)] : List FactorBlock).map factorBlockValue).prod) = 14286766865669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_11
      · exact prime_oneHundredTwentyEightDV_324699246947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 14286766865669) ^ 7143383432834 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 14286766865669) ^ 1298796987788 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 14286766865669) ^ 44 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_15119561361733 : Nat.Prime 15119561361733 := by
  apply lucas_primality 15119561361733 (2 : ZMod 15119561361733)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (163, 1), (7729837097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (163, 1), (7729837097, 1)] : List FactorBlock).map factorBlockValue).prod) = 15119561361733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_163
      · exact prime_oneHundredTwentyEightDV_7729837097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15119561361733) ^ 7559780680866 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 15119561361733) ^ 5039853787244 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 15119561361733) ^ 92758045164 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 15119561361733) ^ 1956 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_18339870561281 : Nat.Prime 18339870561281 := by
  apply lucas_primality 18339870561281 (3 : ZMod 18339870561281)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (5, 1), (26683, 1), (134243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (5, 1), (26683, 1), (134243, 1)] : List FactorBlock).map factorBlockValue).prod) = 18339870561281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_26683
      · exact prime_oneHundredTwentyEightDV_134243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 18339870561281) ^ 9169935280640 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 18339870561281) ^ 3667974112256 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 18339870561281) ^ 687324160 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 18339870561281) ^ 136616960 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_19404345549223 : Nat.Prime 19404345549223 := by
  apply lucas_primality 19404345549223 (5 : ZMod 19404345549223)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (118691, 1), (3027523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (118691, 1), (3027523, 1)] : List FactorBlock).map factorBlockValue).prod) = 19404345549223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_118691
      · exact prime_oneHundredTwentyEightDV_3027523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 19404345549223) ^ 9702172774611 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 19404345549223) ^ 6468115183074 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 19404345549223) ^ 163486242 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 19404345549223) ^ 6409314 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_22501427794609 : Nat.Prime 22501427794609 := by
  apply lucas_primality 22501427794609 (29 : ZMod 22501427794609)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (47, 1), (59, 1), (101, 1), (157, 1), (1523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (47, 1), (59, 1), (101, 1), (157, 1), (1523, 1)] : List FactorBlock).map factorBlockValue).prod) = 22501427794609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_7
      · exact prime_oneHundredTwentyEightDV_47
      · exact prime_oneHundredTwentyEightDV_59
      · exact prime_oneHundredTwentyEightDV_101
      · exact prime_oneHundredTwentyEightDV_157
      · exact prime_oneHundredTwentyEightDV_1523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 22501427794609) ^ 11250713897304 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (29 : ZMod 22501427794609) ^ 7500475931536 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (29 : ZMod 22501427794609) ^ 3214489684944 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (29 : ZMod 22501427794609) ^ 478753782864 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (29 : ZMod 22501427794609) ^ 381380132112 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (29 : ZMod 22501427794609) ^ 222786413808 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (29 : ZMod 22501427794609) ^ 143321196144 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (29 : ZMod 22501427794609) ^ 14774410896 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_31180645690609 : Nat.Prime 31180645690609 := by
  apply lucas_primality 31180645690609 (11 : ZMod 31180645690609)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (113, 1), (5748644117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (113, 1), (5748644117, 1)] : List FactorBlock).map factorBlockValue).prod) = 31180645690609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_113
      · exact prime_oneHundredTwentyEightDV_5748644117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 31180645690609) ^ 15590322845304 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (11 : ZMod 31180645690609) ^ 10393548563536 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (11 : ZMod 31180645690609) ^ 275934917616 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (11 : ZMod 31180645690609) ^ 5424 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_32520964175027 : Nat.Prime 32520964175027 := by
  apply lucas_primality 32520964175027 (2 : ZMod 32520964175027)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (1151, 1), (266552171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (1151, 1), (266552171, 1)] : List FactorBlock).map factorBlockValue).prod) = 32520964175027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_53
      · exact prime_oneHundredTwentyEightDV_1151
      · exact prime_oneHundredTwentyEightDV_266552171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32520964175027) ^ 16260482087513 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 32520964175027) ^ 613603097642 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 32520964175027) ^ 28254530126 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 32520964175027) ^ 122006 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_34128485782277 : Nat.Prime 34128485782277 := by
  apply lucas_primality 34128485782277 (2 : ZMod 34128485782277)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (59, 1), (701, 1), (809, 1), (13421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (59, 1), (701, 1), (809, 1), (13421, 1)] : List FactorBlock).map factorBlockValue).prod) = 34128485782277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_19
      · exact prime_oneHundredTwentyEightDV_59
      · exact prime_oneHundredTwentyEightDV_701
      · exact prime_oneHundredTwentyEightDV_809
      · exact prime_oneHundredTwentyEightDV_13421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 34128485782277) ^ 17064242891138 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 34128485782277) ^ 1796236093804 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 34128485782277) ^ 578448911564 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 34128485782277) ^ 48685429076 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 34128485782277) ^ 42186014564 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 34128485782277) ^ 2542916756 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_38087280527143 : Nat.Prime 38087280527143 := by
  apply lucas_primality 38087280527143 (3 : ZMod 38087280527143)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (743, 1), (1543, 1), (71909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (743, 1), (1543, 1), (71909, 1)] : List FactorBlock).map factorBlockValue).prod) = 38087280527143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_7
      · exact prime_oneHundredTwentyEightDV_11
      · exact prime_oneHundredTwentyEightDV_743
      · exact prime_oneHundredTwentyEightDV_1543
      · exact prime_oneHundredTwentyEightDV_71909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 38087280527143) ^ 19043640263571 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 38087280527143) ^ 12695760175714 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 38087280527143) ^ 5441040075306 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 38087280527143) ^ 3462480047922 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 38087280527143) ^ 51261481194 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 38087280527143) ^ 24683914794 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 38087280527143) ^ 529659438 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_39771564643693 : Nat.Prime 39771564643693 := by
  apply lucas_primality 39771564643693 (2 : ZMod 39771564643693)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (157823669221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (157823669221, 1)] : List FactorBlock).map factorBlockValue).prod) = 39771564643693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_7
      · exact prime_oneHundredTwentyEightDV_157823669221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 39771564643693) ^ 19885782321846 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 39771564643693) ^ 13257188214564 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 39771564643693) ^ 5681652091956 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 39771564643693) ^ 252 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_43909752428719 : Nat.Prime 43909752428719 := by
  apply lucas_primality 43909752428719 (7 : ZMod 43909752428719)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (17, 1), (43, 2), (643, 1), (32917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (17, 1), (43, 2), (643, 1), (32917, 1)] : List FactorBlock).map factorBlockValue).prod) = 43909752428719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_11
      · exact prime_oneHundredTwentyEightDV_17
      · exact prime_oneHundredTwentyEightDV_43
      · exact prime_oneHundredTwentyEightDV_643
      · exact prime_oneHundredTwentyEightDV_32917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 43909752428719) ^ 21954876214359 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 43909752428719) ^ 14636584142906 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 43909752428719) ^ 3991795675338 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 43909752428719) ^ 2582926613454 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 43909752428719) ^ 1021157033226 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 43909752428719) ^ 68288884026 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 43909752428719) ^ 1333953654 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_47733081551131 : Nat.Prime 47733081551131 := by
  apply lucas_primality 47733081551131 (3 : ZMod 47733081551131)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (31, 1), (53, 1), (968413097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (31, 1), (53, 1), (968413097, 1)] : List FactorBlock).map factorBlockValue).prod) = 47733081551131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_31
      · exact prime_oneHundredTwentyEightDV_53
      · exact prime_oneHundredTwentyEightDV_968413097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 47733081551131) ^ 23866540775565 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 47733081551131) ^ 15911027183710 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 47733081551131) ^ 9546616310226 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 47733081551131) ^ 1539776824230 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 47733081551131) ^ 900624180210 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 47733081551131) ^ 49290 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_55117469116147 : Nat.Prime 55117469116147 := by
  apply lucas_primality 55117469116147 (5 : ZMod 55117469116147)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 2), (17365302179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 2), (17365302179, 1)] : List FactorBlock).map factorBlockValue).prod) = 55117469116147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_23
      · exact prime_oneHundredTwentyEightDV_17365302179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 55117469116147) ^ 27558734558073 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 55117469116147) ^ 18372489705382 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 55117469116147) ^ 2396411700702 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 55117469116147) ^ 3174 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_61046709121033 : Nat.Prime 61046709121033 := by
  apply lucas_primality 61046709121033 (5 : ZMod 61046709121033)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (29, 1), (829, 1), (105803123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (29, 1), (829, 1), (105803123, 1)] : List FactorBlock).map factorBlockValue).prod) = 61046709121033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_29
      · exact prime_oneHundredTwentyEightDV_829
      · exact prime_oneHundredTwentyEightDV_105803123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 61046709121033) ^ 30523354560516 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 61046709121033) ^ 20348903040344 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 61046709121033) ^ 2105058935208 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 61046709121033) ^ 73638973608 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 61046709121033) ^ 576984 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_65061963633859 : Nat.Prime 65061963633859 := by
  apply lucas_primality 65061963633859 (2 : ZMod 65061963633859)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (83, 1), (181, 1), (673, 1), (1072517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (83, 1), (181, 1), (673, 1), (1072517, 1)] : List FactorBlock).map factorBlockValue).prod) = 65061963633859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_83
      · exact prime_oneHundredTwentyEightDV_181
      · exact prime_oneHundredTwentyEightDV_673
      · exact prime_oneHundredTwentyEightDV_1072517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 65061963633859) ^ 32530981816929 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 65061963633859) ^ 21687321211286 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 65061963633859) ^ 783879079926 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 65061963633859) ^ 359458362618 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 65061963633859) ^ 96674537346 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 65061963633859) ^ 60662874 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_106000085625457 : Nat.Prime 106000085625457 := by
  apply lucas_primality 106000085625457 (17 : ZMod 106000085625457)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (11, 1), (19, 1), (73, 1), (144742421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (11, 1), (19, 1), (73, 1), (144742421, 1)] : List FactorBlock).map factorBlockValue).prod) = 106000085625457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_11
      · exact prime_oneHundredTwentyEightDV_19
      · exact prime_oneHundredTwentyEightDV_73
      · exact prime_oneHundredTwentyEightDV_144742421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 106000085625457) ^ 53000042812728 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (17 : ZMod 106000085625457) ^ 35333361875152 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (17 : ZMod 106000085625457) ^ 9636371420496 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (17 : ZMod 106000085625457) ^ 5578951875024 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (17 : ZMod 106000085625457) ^ 1452055967472 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (17 : ZMod 106000085625457) ^ 732336 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_130941245272457 : Nat.Prime 130941245272457 := by
  apply lucas_primality 130941245272457 (3 : ZMod 130941245272457)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (550937, 1), (1563619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (550937, 1), (1563619, 1)] : List FactorBlock).map factorBlockValue).prod) = 130941245272457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_19
      · exact prime_oneHundredTwentyEightDV_550937
      · exact prime_oneHundredTwentyEightDV_1563619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 130941245272457) ^ 65470622636228 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 130941245272457) ^ 6891644488024 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 130941245272457) ^ 237670088 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 130941245272457) ^ 83742424 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_134123905279457 : Nat.Prime 134123905279457 := by
  apply lucas_primality 134123905279457 (3 : ZMod 134123905279457)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (119549, 1), (35059867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (119549, 1), (35059867, 1)] : List FactorBlock).map factorBlockValue).prod) = 134123905279457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_119549
      · exact prime_oneHundredTwentyEightDV_35059867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 134123905279457) ^ 67061952639728 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 134123905279457) ^ 1121915744 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 134123905279457) ^ 3825568 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_176285873869097 : Nat.Prime 176285873869097 := by
  apply lucas_primality 176285873869097 (3 : ZMod 176285873869097)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3360223, 1), (6557819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3360223, 1), (6557819, 1)] : List FactorBlock).map factorBlockValue).prod) = 176285873869097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3360223
      · exact prime_oneHundredTwentyEightDV_6557819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 176285873869097) ^ 88142936934548 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 176285873869097) ^ 52462552 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 176285873869097) ^ 26881784 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_243106485607259 : Nat.Prime 243106485607259 := by
  apply lucas_primality 243106485607259 (2 : ZMod 243106485607259)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (179, 1), (23333, 1), (319817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (179, 1), (23333, 1), (319817, 1)] : List FactorBlock).map factorBlockValue).prod) = 243106485607259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_7
      · exact prime_oneHundredTwentyEightDV_13
      · exact prime_oneHundredTwentyEightDV_179
      · exact prime_oneHundredTwentyEightDV_23333
      · exact prime_oneHundredTwentyEightDV_319817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 243106485607259) ^ 121553242803629 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 243106485607259) ^ 34729497943894 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 243106485607259) ^ 18700498892866 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 243106485607259) ^ 1358136791102 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 243106485607259) ^ 10418998226 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 243106485607259) ^ 760142474 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_258862483991359 : Nat.Prime 258862483991359 := by
  apply lucas_primality 258862483991359 (6 : ZMod 258862483991359)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (10789, 1), (102534983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (10789, 1), (102534983, 1)] : List FactorBlock).map factorBlockValue).prod) = 258862483991359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_13
      · exact prime_oneHundredTwentyEightDV_10789
      · exact prime_oneHundredTwentyEightDV_102534983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 258862483991359) ^ 129431241995679 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 86287494663786 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 19912498768566 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 23993186022 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 2524626 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_263376858119281 : Nat.Prime 263376858119281 := by
  apply lucas_primality 263376858119281 (17 : ZMod 263376858119281)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (5231, 1), (209788487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (5231, 1), (209788487, 1)] : List FactorBlock).map factorBlockValue).prod) = 263376858119281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_5231
      · exact prime_oneHundredTwentyEightDV_209788487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 263376858119281) ^ 131688429059640 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (17 : ZMod 263376858119281) ^ 87792286039760 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (17 : ZMod 263376858119281) ^ 52675371623856 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (17 : ZMod 263376858119281) ^ 50349236880 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (17 : ZMod 263376858119281) ^ 1255440 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_294930856273127 : Nat.Prime 294930856273127 := by
  apply lucas_primality 294930856273127 (5 : ZMod 294930856273127)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 2), (37, 1), (1063, 1), (2731, 1), (3803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 2), (37, 1), (1063, 1), (2731, 1), (3803, 1)] : List FactorBlock).map factorBlockValue).prod) = 294930856273127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_19
      · exact prime_oneHundredTwentyEightDV_37
      · exact prime_oneHundredTwentyEightDV_1063
      · exact prime_oneHundredTwentyEightDV_2731
      · exact prime_oneHundredTwentyEightDV_3803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 294930856273127) ^ 147465428136563 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 294930856273127) ^ 15522676645954 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 294930856273127) ^ 7971104223598 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 294930856273127) ^ 277451417002 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 294930856273127) ^ 107993722546 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 294930856273127) ^ 77552157842 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_334989034308223 : Nat.Prime 334989034308223 := by
  apply lucas_primality 334989034308223 (3 : ZMod 334989034308223)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (37, 1), (215565659143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (37, 1), (215565659143, 1)] : List FactorBlock).map factorBlockValue).prod) = 334989034308223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_7
      · exact prime_oneHundredTwentyEightDV_37
      · exact prime_oneHundredTwentyEightDV_215565659143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 334989034308223) ^ 167494517154111 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 334989034308223) ^ 111663011436074 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 334989034308223) ^ 47855576329746 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 334989034308223) ^ 9053757684006 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 334989034308223) ^ 1554 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_337392849068831 : Nat.Prime 337392849068831 := by
  apply lucas_primality 337392849068831 (29 : ZMod 337392849068831)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (167, 1), (1583, 1), (127625803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (167, 1), (1583, 1), (127625803, 1)] : List FactorBlock).map factorBlockValue).prod) = 337392849068831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_167
      · exact prime_oneHundredTwentyEightDV_1583
      · exact prime_oneHundredTwentyEightDV_127625803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 337392849068831) ^ 168696424534415 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (29 : ZMod 337392849068831) ^ 67478569813766 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (29 : ZMod 337392849068831) ^ 2020316461490 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (29 : ZMod 337392849068831) ^ 213135091010 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (29 : ZMod 337392849068831) ^ 2643610 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_595802673036443 : Nat.Prime 595802673036443 := by
  apply lucas_primality 595802673036443 (2 : ZMod 595802673036443)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (241, 1), (16932946997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (241, 1), (16932946997, 1)] : List FactorBlock).map factorBlockValue).prod) = 595802673036443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_73
      · exact prime_oneHundredTwentyEightDV_241
      · exact prime_oneHundredTwentyEightDV_16932946997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 595802673036443) ^ 297901336518221 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 595802673036443) ^ 8161680452554 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 595802673036443) ^ 2472210261562 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 595802673036443) ^ 35186 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_729591008638033 : Nat.Prime 729591008638033 := by
  apply lucas_primality 729591008638033 (5 : ZMod 729591008638033)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (37, 1), (43, 1), (199, 1), (5334239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (37, 1), (43, 1), (199, 1), (5334239, 1)] : List FactorBlock).map factorBlockValue).prod) = 729591008638033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_37
      · exact prime_oneHundredTwentyEightDV_43
      · exact prime_oneHundredTwentyEightDV_199
      · exact prime_oneHundredTwentyEightDV_5334239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 729591008638033) ^ 364795504319016 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 729591008638033) ^ 243197002879344 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 729591008638033) ^ 19718675909136 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 729591008638033) ^ 16967232759024 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 729591008638033) ^ 3666286475568 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 729591008638033) ^ 136775088 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_752898446118509 : Nat.Prime 752898446118509 := by
  apply lucas_primality 752898446118509 (2 : ZMod 752898446118509)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (103, 1), (124067, 1), (866431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (103, 1), (124067, 1), (866431, 1)] : List FactorBlock).map factorBlockValue).prod) = 752898446118509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_17
      · exact prime_oneHundredTwentyEightDV_103
      · exact prime_oneHundredTwentyEightDV_124067
      · exact prime_oneHundredTwentyEightDV_866431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 752898446118509) ^ 376449223059254 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 752898446118509) ^ 44288143889324 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 752898446118509) ^ 7309693651636 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 752898446118509) ^ 6068482724 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 752898446118509) ^ 868965268 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_832463553216367 : Nat.Prime 832463553216367 := by
  apply lucas_primality 832463553216367 (3 : ZMod 832463553216367)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 7), (19, 2), (691, 1), (762959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 7), (19, 2), (691, 1), (762959, 1)] : List FactorBlock).map factorBlockValue).prod) = 832463553216367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_19
      · exact prime_oneHundredTwentyEightDV_691
      · exact prime_oneHundredTwentyEightDV_762959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 832463553216367) ^ 416231776608183 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 832463553216367) ^ 277487851072122 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 832463553216367) ^ 43813871221914 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 832463553216367) ^ 1204722942426 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 832463553216367) ^ 1091098674 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_972840324054971 : Nat.Prime 972840324054971 := by
  apply lucas_primality 972840324054971 (6 : ZMod 972840324054971)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (569, 1), (1009, 1), (3947, 1), (6133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (569, 1), (1009, 1), (3947, 1), (6133, 1)] : List FactorBlock).map factorBlockValue).prod) = 972840324054971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_7
      · exact prime_oneHundredTwentyEightDV_569
      · exact prime_oneHundredTwentyEightDV_1009
      · exact prime_oneHundredTwentyEightDV_3947
      · exact prime_oneHundredTwentyEightDV_6133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 972840324054971) ^ 486420162027485 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 972840324054971) ^ 194568064810994 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 972840324054971) ^ 138977189150710 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 972840324054971) ^ 1709736949130 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 972840324054971) ^ 964162858330 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 972840324054971) ^ 246475886510 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 972840324054971) ^ 158623891090 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_1081354462857307 : Nat.Prime 1081354462857307 := by
  apply lucas_primality 1081354462857307 (2 : ZMod 1081354462857307)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (29, 1), (71, 1), (2652445933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (29, 1), (71, 1), (2652445933, 1)] : List FactorBlock).map factorBlockValue).prod) = 1081354462857307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_11
      · exact prime_oneHundredTwentyEightDV_29
      · exact prime_oneHundredTwentyEightDV_71
      · exact prime_oneHundredTwentyEightDV_2652445933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1081354462857307) ^ 540677231428653 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081354462857307) ^ 360451487619102 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081354462857307) ^ 98304951168846 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081354462857307) ^ 37288084926114 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081354462857307) ^ 15230344547286 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081354462857307) ^ 407682 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_1291737826932829 : Nat.Prime 1291737826932829 := by
  apply lucas_primality 1291737826932829 (2 : ZMod 1291737826932829)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (9785892628279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (9785892628279, 1)] : List FactorBlock).map factorBlockValue).prod) = 1291737826932829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_11
      · exact prime_oneHundredTwentyEightDV_9785892628279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1291737826932829) ^ 645868913466414 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1291737826932829) ^ 430579275644276 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1291737826932829) ^ 117430711539348 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1291737826932829) ^ 132 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_1398602232618869 : Nat.Prime 1398602232618869 := by
  apply lucas_primality 1398602232618869 (2 : ZMod 1398602232618869)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (353, 1), (223547, 1), (4430887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (353, 1), (223547, 1), (4430887, 1)] : List FactorBlock).map factorBlockValue).prod) = 1398602232618869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_353
      · exact prime_oneHundredTwentyEightDV_223547
      · exact prime_oneHundredTwentyEightDV_4430887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1398602232618869) ^ 699301116309434 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1398602232618869) ^ 3962045984756 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1398602232618869) ^ 6256412444 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1398602232618869) ^ 315648364 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_1436748238159427 : Nat.Prime 1436748238159427 := by
  apply lucas_primality 1436748238159427 (2 : ZMod 1436748238159427)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (113, 1), (6357293089201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (113, 1), (6357293089201, 1)] : List FactorBlock).map factorBlockValue).prod) = 1436748238159427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_113
      · exact prime_oneHundredTwentyEightDV_6357293089201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1436748238159427) ^ 718374119079713 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1436748238159427) ^ 12714586178402 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1436748238159427) ^ 226 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_2950552131206951 : Nat.Prime 2950552131206951 := by
  apply lucas_primality 2950552131206951 (13 : ZMod 2950552131206951)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (59, 1), (13411, 1), (74579611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (59, 1), (13411, 1), (74579611, 1)] : List FactorBlock).map factorBlockValue).prod) = 2950552131206951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_59
      · exact prime_oneHundredTwentyEightDV_13411
      · exact prime_oneHundredTwentyEightDV_74579611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 2950552131206951) ^ 1475276065603475 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (13 : ZMod 2950552131206951) ^ 590110426241390 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (13 : ZMod 2950552131206951) ^ 50009358156050 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (13 : ZMod 2950552131206951) ^ 220009852450 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (13 : ZMod 2950552131206951) ^ 39562450 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_4214029729908497 : Nat.Prime 4214029729908497 := by
  apply lucas_primality 4214029729908497 (3 : ZMod 4214029729908497)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (263376858119281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (263376858119281, 1)] : List FactorBlock).map factorBlockValue).prod) = 4214029729908497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_263376858119281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 4214029729908497) ^ 2107014864954248 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 4214029729908497) ^ 16 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_5808790066327169 : Nat.Prime 5808790066327169 := by
  apply lucas_primality 5808790066327169 (3 : ZMod 5808790066327169)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (43, 1), (73, 1), (293, 1), (1277, 1), (38639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (43, 1), (73, 1), (293, 1), (1277, 1), (38639, 1)] : List FactorBlock).map factorBlockValue).prod) = 5808790066327169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_43
      · exact prime_oneHundredTwentyEightDV_73
      · exact prime_oneHundredTwentyEightDV_293
      · exact prime_oneHundredTwentyEightDV_1277
      · exact prime_oneHundredTwentyEightDV_38639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5808790066327169) ^ 2904395033163584 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 5808790066327169) ^ 135088141077376 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 5808790066327169) ^ 79572466662016 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 5808790066327169) ^ 19825222069376 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 5808790066327169) ^ 4548778438784 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 5808790066327169) ^ 150334896512 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_6344888615620271 : Nat.Prime 6344888615620271 := by
  apply lucas_primality 6344888615620271 (13 : ZMod 6344888615620271)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (151, 1), (271, 1), (912071411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (151, 1), (271, 1), (912071411, 1)] : List FactorBlock).map factorBlockValue).prod) = 6344888615620271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_17
      · exact prime_oneHundredTwentyEightDV_151
      · exact prime_oneHundredTwentyEightDV_271
      · exact prime_oneHundredTwentyEightDV_912071411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 6344888615620271) ^ 3172444307810135 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (13 : ZMod 6344888615620271) ^ 1268977723124054 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (13 : ZMod 6344888615620271) ^ 373228742095310 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (13 : ZMod 6344888615620271) ^ 42019129904770 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (13 : ZMod 6344888615620271) ^ 23412873120370 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (13 : ZMod 6344888615620271) ^ 6956570 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_8036856174828427 : Nat.Prime 8036856174828427 := by
  apply lucas_primality 8036856174828427 (5 : ZMod 8036856174828427)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (643691, 1), (189175471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (643691, 1), (189175471, 1)] : List FactorBlock).map factorBlockValue).prod) = 8036856174828427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_11
      · exact prime_oneHundredTwentyEightDV_643691
      · exact prime_oneHundredTwentyEightDV_189175471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 8036856174828427) ^ 4018428087414213 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 8036856174828427) ^ 2678952058276142 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 8036856174828427) ^ 730623288620766 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 8036856174828427) ^ 12485581086 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 8036856174828427) ^ 42483606 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_14584738097576557 : Nat.Prime 14584738097576557 := by
  apply lucas_primality 14584738097576557 (2 : ZMod 14584738097576557)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (13, 1), (1483998585427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (13, 1), (1483998585427, 1)] : List FactorBlock).map factorBlockValue).prod) = 14584738097576557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_7
      · exact prime_oneHundredTwentyEightDV_13
      · exact prime_oneHundredTwentyEightDV_1483998585427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14584738097576557) ^ 7292369048788278 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 14584738097576557) ^ 4861579365858852 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 14584738097576557) ^ 2083534013939508 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 14584738097576557) ^ 1121902930582812 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 14584738097576557) ^ 9828 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_18105475874157703 : Nat.Prime 18105475874157703 := by
  apply lucas_primality 18105475874157703 (3 : ZMod 18105475874157703)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (37, 1), (283, 1), (33941, 1), (2830249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (37, 1), (283, 1), (33941, 1), (2830249, 1)] : List FactorBlock).map factorBlockValue).prod) = 18105475874157703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_37
      · exact prime_oneHundredTwentyEightDV_283
      · exact prime_oneHundredTwentyEightDV_33941
      · exact prime_oneHundredTwentyEightDV_2830249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 18105475874157703) ^ 9052737937078851 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 18105475874157703) ^ 6035158624719234 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 18105475874157703) ^ 489337185788046 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 18105475874157703) ^ 63976946551794 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 18105475874157703) ^ 533439671022 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 18105475874157703) ^ 6397131798 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_37051420944511243 : Nat.Prime 37051420944511243 := by
  apply lucas_primality 37051420944511243 (3 : ZMod 37051420944511243)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (131, 1), (170603, 1), (92103133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (131, 1), (170603, 1), (92103133, 1)] : List FactorBlock).map factorBlockValue).prod) = 37051420944511243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_131
      · exact prime_oneHundredTwentyEightDV_170603
      · exact prime_oneHundredTwentyEightDV_92103133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 37051420944511243) ^ 18525710472255621 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 37051420944511243) ^ 12350473648170414 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 37051420944511243) ^ 282835274385582 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 37051420944511243) ^ 217179187614 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 37051420944511243) ^ 402281874 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_70075919093336591 : Nat.Prime 70075919093336591 := by
  apply lucas_primality 70075919093336591 (14 : ZMod 70075919093336591)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (31, 1), (24841, 1), (1299989947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (31, 1), (24841, 1), (1299989947, 1)] : List FactorBlock).map factorBlockValue).prod) = 70075919093336591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_7
      · exact prime_oneHundredTwentyEightDV_31
      · exact prime_oneHundredTwentyEightDV_24841
      · exact prime_oneHundredTwentyEightDV_1299989947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 70075919093336591) ^ 35037959546668295 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 14015183818667318 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 10010845584762370 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 2260513519139890 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 2820978184990 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 53904970 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_70852498304454511 : Nat.Prime 70852498304454511 := by
  apply lucas_primality 70852498304454511 (7 : ZMod 70852498304454511)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (337392849068831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (337392849068831, 1)] : List FactorBlock).map factorBlockValue).prod) = 70852498304454511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_7
      · exact prime_oneHundredTwentyEightDV_337392849068831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 70852498304454511) ^ 35426249152227255 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 70852498304454511) ^ 23617499434818170 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 70852498304454511) ^ 14170499660890902 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 70852498304454511) ^ 10121785472064930 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 70852498304454511) ^ 210 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_83323535982942023 : Nat.Prime 83323535982942023 := by
  apply lucas_primality 83323535982942023 (5 : ZMod 83323535982942023)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (631, 1), (9511, 1), (147701293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (631, 1), (9511, 1), (147701293, 1)] : List FactorBlock).map factorBlockValue).prod) = 83323535982942023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_47
      · exact prime_oneHundredTwentyEightDV_631
      · exact prime_oneHundredTwentyEightDV_9511
      · exact prime_oneHundredTwentyEightDV_147701293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 83323535982942023) ^ 41661767991471011 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 83323535982942023) ^ 1772841191126426 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 83323535982942023) ^ 132049977785962 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 83323535982942023) ^ 8760754493002 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 83323535982942023) ^ 564135454 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_104997213222150383 : Nat.Prime 104997213222150383 := by
  apply lucas_primality 104997213222150383 (5 : ZMod 104997213222150383)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1545121, 1), (4853859953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1545121, 1), (4853859953, 1)] : List FactorBlock).map factorBlockValue).prod) = 104997213222150383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_7
      · exact prime_oneHundredTwentyEightDV_1545121
      · exact prime_oneHundredTwentyEightDV_4853859953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 104997213222150383) ^ 52498606611075191 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 104997213222150383) ^ 14999601888878626 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 104997213222150383) ^ 67954039342 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 104997213222150383) ^ 21631694 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_121197184259488681 : Nat.Prime 121197184259488681 := by
  apply lucas_primality 121197184259488681 (23 : ZMod 121197184259488681)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (79, 1), (131, 1), (9631, 1), (1447583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (79, 1), (131, 1), (9631, 1), (1447583, 1)] : List FactorBlock).map factorBlockValue).prod) = 121197184259488681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_7
      · exact prime_oneHundredTwentyEightDV_79
      · exact prime_oneHundredTwentyEightDV_131
      · exact prime_oneHundredTwentyEightDV_9631
      · exact prime_oneHundredTwentyEightDV_1447583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 121197184259488681) ^ 60598592129744340 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (23 : ZMod 121197184259488681) ^ 40399061419829560 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (23 : ZMod 121197184259488681) ^ 24239436851897736 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (23 : ZMod 121197184259488681) ^ 17313883465641240 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (23 : ZMod 121197184259488681) ^ 1534141572904920 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (23 : ZMod 121197184259488681) ^ 925169345492280 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (23 : ZMod 121197184259488681) ^ 12584070632280 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (23 : ZMod 121197184259488681) ^ 83723823960 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_156168466237595299 : Nat.Prime 156168466237595299 := by
  apply lucas_primality 156168466237595299 (3 : ZMod 156168466237595299)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (102329, 1), (254356807027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (102329, 1), (254356807027, 1)] : List FactorBlock).map factorBlockValue).prod) = 156168466237595299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_102329
      · exact prime_oneHundredTwentyEightDV_254356807027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 156168466237595299) ^ 78084233118797649 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 156168466237595299) ^ 52056155412531766 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 156168466237595299) ^ 1526140842162 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 156168466237595299) ^ 613974 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_176246916136727123 : Nat.Prime 176246916136727123 := by
  apply lucas_primality 176246916136727123 (2 : ZMod 176246916136727123)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (673, 1), (130941245272457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (673, 1), (130941245272457, 1)] : List FactorBlock).map factorBlockValue).prod) = 176246916136727123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_673
      · exact prime_oneHundredTwentyEightDV_130941245272457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 176246916136727123) ^ 88123458068363561 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 176246916136727123) ^ 261882490544914 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 176246916136727123) ^ 1346 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_229590316476973157 : Nat.Prime 229590316476973157 := by
  apply lucas_primality 229590316476973157 (2 : ZMod 229590316476973157)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (59, 1), (972840324054971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (59, 1), (972840324054971, 1)] : List FactorBlock).map factorBlockValue).prod) = 229590316476973157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_59
      · exact prime_oneHundredTwentyEightDV_972840324054971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 229590316476973157) ^ 114795158238486578 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 229590316476973157) ^ 3891361296219884 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 229590316476973157) ^ 236 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_241466608204721173 : Nat.Prime 241466608204721173 := by
  apply lucas_primality 241466608204721173 (2 : ZMod 241466608204721173)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (13, 2), (23, 1), (25237, 1), (9767969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (13, 2), (23, 1), (25237, 1), (9767969, 1)] : List FactorBlock).map factorBlockValue).prod) = 241466608204721173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_7
      · exact prime_oneHundredTwentyEightDV_13
      · exact prime_oneHundredTwentyEightDV_23
      · exact prime_oneHundredTwentyEightDV_25237
      · exact prime_oneHundredTwentyEightDV_9767969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 241466608204721173) ^ 120733304102360586 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 241466608204721173) ^ 80488869401573724 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 241466608204721173) ^ 34495229743531596 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 241466608204721173) ^ 18574354477286244 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 241466608204721173) ^ 10498548182813964 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 241466608204721173) ^ 9567960066756 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 241466608204721173) ^ 24720247188 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_330159903839178421 : Nat.Prime 330159903839178421 := by
  apply lucas_primality 330159903839178421 (2 : ZMod 330159903839178421)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (12031387, 1), (65337023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (12031387, 1), (65337023, 1)] : List FactorBlock).map factorBlockValue).prod) = 330159903839178421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_7
      · exact prime_oneHundredTwentyEightDV_12031387
      · exact prime_oneHundredTwentyEightDV_65337023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 330159903839178421) ^ 165079951919589210 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 330159903839178421) ^ 110053301279726140 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 330159903839178421) ^ 66031980767835684 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 330159903839178421) ^ 47165700548454060 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 330159903839178421) ^ 27441549660 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 330159903839178421) ^ 5053182540 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_439532865836238407 : Nat.Prime 439532865836238407 := by
  apply lucas_primality 439532865836238407 (5 : ZMod 439532865836238407)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (787903, 1), (14680302479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (787903, 1), (14680302479, 1)] : List FactorBlock).map factorBlockValue).prod) = 439532865836238407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_19
      · exact prime_oneHundredTwentyEightDV_787903
      · exact prime_oneHundredTwentyEightDV_14680302479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 439532865836238407) ^ 219766432918119203 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 439532865836238407) ^ 23133308728223074 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 439532865836238407) ^ 557851494202 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 439532865836238407) ^ 29940314 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_552964022232041863 : Nat.Prime 552964022232041863 := by
  apply lucas_primality 552964022232041863 (3 : ZMod 552964022232041863)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (13, 1), (19, 1), (32327, 1), (1282450937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (13, 1), (19, 1), (32327, 1), (1282450937, 1)] : List FactorBlock).map factorBlockValue).prod) = 552964022232041863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_13
      · exact prime_oneHundredTwentyEightDV_19
      · exact prime_oneHundredTwentyEightDV_32327
      · exact prime_oneHundredTwentyEightDV_1282450937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 552964022232041863) ^ 276482011116020931 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 552964022232041863) ^ 184321340744013954 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 552964022232041863) ^ 42535694017849374 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 552964022232041863) ^ 29103369591160098 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 552964022232041863) ^ 17105330597706 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 552964022232041863) ^ 431177526 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_742993236589365067 : Nat.Prime 742993236589365067 := by
  apply lucas_primality 742993236589365067 (2 : ZMod 742993236589365067)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (6997, 1), (10259, 1), (1725109657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (6997, 1), (10259, 1), (1725109657, 1)] : List FactorBlock).map factorBlockValue).prod) = 742993236589365067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_6997
      · exact prime_oneHundredTwentyEightDV_10259
      · exact prime_oneHundredTwentyEightDV_1725109657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 742993236589365067) ^ 371496618294682533 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 742993236589365067) ^ 247664412196455022 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 742993236589365067) ^ 106187399826978 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 742993236589365067) ^ 72423553620174 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 742993236589365067) ^ 430693338 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_1110545701743020261 : Nat.Prime 1110545701743020261 := by
  apply lucas_primality 1110545701743020261 (2 : ZMod 1110545701743020261)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (449, 1), (5725547, 1), (21599471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (449, 1), (5725547, 1), (21599471, 1)] : List FactorBlock).map factorBlockValue).prod) = 1110545701743020261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_449
      · exact prime_oneHundredTwentyEightDV_5725547
      · exact prime_oneHundredTwentyEightDV_21599471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1110545701743020261) ^ 555272850871510130 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1110545701743020261) ^ 222109140348604052 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1110545701743020261) ^ 2473375727712740 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1110545701743020261) ^ 193963249580 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1110545701743020261) ^ 51415412060 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_1209382014136060249 : Nat.Prime 1209382014136060249 := by
  apply lucas_primality 1209382014136060249 (17 : ZMod 1209382014136060249)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (71, 2), (1009, 1), (900641003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (71, 2), (1009, 1), (900641003, 1)] : List FactorBlock).map factorBlockValue).prod) = 1209382014136060249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_11
      · exact prime_oneHundredTwentyEightDV_71
      · exact prime_oneHundredTwentyEightDV_1009
      · exact prime_oneHundredTwentyEightDV_900641003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 1209382014136060249) ^ 604691007068030124 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (17 : ZMod 1209382014136060249) ^ 403127338045353416 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (17 : ZMod 1209382014136060249) ^ 109943819466914568 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (17 : ZMod 1209382014136060249) ^ 17033549494874088 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (17 : ZMod 1209382014136060249) ^ 1198594662176472 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (17 : ZMod 1209382014136060249) ^ 1342801416 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_1309234191118560457 : Nat.Prime 1309234191118560457 := by
  apply lucas_primality 1309234191118560457 (5 : ZMod 1309234191118560457)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (62731, 1), (869608720249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (62731, 1), (869608720249, 1)] : List FactorBlock).map factorBlockValue).prod) = 1309234191118560457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_62731
      · exact prime_oneHundredTwentyEightDV_869608720249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1309234191118560457) ^ 654617095559280228 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1309234191118560457) ^ 436411397039520152 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1309234191118560457) ^ 20870609285976 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1309234191118560457) ^ 1505544 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_1581298643568549343 : Nat.Prime 1581298643568549343 := by
  apply lucas_primality 1581298643568549343 (3 : ZMod 1581298643568549343)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5701, 1), (3056083, 1), (15126779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5701, 1), (3056083, 1), (15126779, 1)] : List FactorBlock).map factorBlockValue).prod) = 1581298643568549343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_5701
      · exact prime_oneHundredTwentyEightDV_3056083
      · exact prime_oneHundredTwentyEightDV_15126779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1581298643568549343) ^ 790649321784274671 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1581298643568549343) ^ 527099547856183114 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1581298643568549343) ^ 277372152879942 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1581298643568549343) ^ 517426602474 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1581298643568549343) ^ 104536375098 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_1889507103043784753 : Nat.Prime 1889507103043784753 := by
  apply lucas_primality 1889507103043784753 (3 : ZMod 1889507103043784753)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (5407, 1), (1985543889911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (5407, 1), (1985543889911, 1)] : List FactorBlock).map factorBlockValue).prod) = 1889507103043784753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_11
      · exact prime_oneHundredTwentyEightDV_5407
      · exact prime_oneHundredTwentyEightDV_1985543889911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1889507103043784753) ^ 944753551521892376 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1889507103043784753) ^ 171773373003980432 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1889507103043784753) ^ 349455724624336 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1889507103043784753) ^ 951632 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_1892132026399887439 : Nat.Prime 1892132026399887439 := by
  apply lucas_primality 1892132026399887439 (6 : ZMod 1892132026399887439)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (131, 1), (65061963633859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (131, 1), (65061963633859, 1)] : List FactorBlock).map factorBlockValue).prod) = 1892132026399887439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_37
      · exact prime_oneHundredTwentyEightDV_131
      · exact prime_oneHundredTwentyEightDV_65061963633859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1892132026399887439) ^ 946066013199943719 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 1892132026399887439) ^ 630710675466629146 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 1892132026399887439) ^ 51138703416213174 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 1892132026399887439) ^ 14443755926716698 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 1892132026399887439) ^ 29082 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_2220502305087140441 : Nat.Prime 2220502305087140441 := by
  apply lucas_primality 2220502305087140441 (3 : ZMod 2220502305087140441)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2220502305087140441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_101
      · exact prime_oneHundredTwentyEightDV_191
      · exact prime_oneHundredTwentyEightDV_48017
      · exact prime_oneHundredTwentyEightDV_59929613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2220502305087140441) ^ 1110251152543570220 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 444100461017428088 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 21985171337496440 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 11625666518780840 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 46244086575320 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 37051837880 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_3503795954666829551 : Nat.Prime 3503795954666829551 := by
  apply lucas_primality 3503795954666829551 (13 : ZMod 3503795954666829551)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (70075919093336591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (70075919093336591, 1)] : List FactorBlock).map factorBlockValue).prod) = 3503795954666829551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_70075919093336591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 3503795954666829551) ^ 1751897977333414775 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (13 : ZMod 3503795954666829551) ^ 700759190933365910 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (13 : ZMod 3503795954666829551) ^ 50 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_3779014206087569507 : Nat.Prime 3779014206087569507 := by
  apply lucas_primality 3779014206087569507 (2 : ZMod 3779014206087569507)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1889507103043784753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1889507103043784753, 1)] : List FactorBlock).map factorBlockValue).prod) = 3779014206087569507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_1889507103043784753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 3779014206087569507) ^ 1889507103043784753 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3779014206087569507) ^ 2 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_4456208132610353279 : Nat.Prime 4456208132610353279 := by
  apply lucas_primality 4456208132610353279 (23 : ZMod 4456208132610353279)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83207, 1), (1551167, 1), (17263031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83207, 1), (1551167, 1), (17263031, 1)] : List FactorBlock).map factorBlockValue).prod) = 4456208132610353279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_83207
      · exact prime_oneHundredTwentyEightDV_1551167
      · exact prime_oneHundredTwentyEightDV_17263031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 4456208132610353279) ^ 2228104066305176639 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (23 : ZMod 4456208132610353279) ^ 53555688014354 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (23 : ZMod 4456208132610353279) ^ 2872810040834 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (23 : ZMod 4456208132610353279) ^ 258135905138 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_4555660527163322963 : Nat.Prime 4555660527163322963 := by
  apply lucas_primality 4555660527163322963 (2 : ZMod 4555660527163322963)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (1613, 1), (18339870561281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (1613, 1), (18339870561281, 1)] : List FactorBlock).map factorBlockValue).prod) = 4555660527163322963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_7
      · exact prime_oneHundredTwentyEightDV_11
      · exact prime_oneHundredTwentyEightDV_1613
      · exact prime_oneHundredTwentyEightDV_18339870561281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4555660527163322963) ^ 2277830263581661481 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 4555660527163322963) ^ 650808646737617566 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 4555660527163322963) ^ 414150957014847542 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 4555660527163322963) ^ 2824340066437274 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 4555660527163322963) ^ 248402 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_5733332631309718217 : Nat.Prime 5733332631309718217 := by
  apply lucas_primality 5733332631309718217 (3 : ZMod 5733332631309718217)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (6761, 1), (106000085625457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (6761, 1), (106000085625457, 1)] : List FactorBlock).map factorBlockValue).prod) = 5733332631309718217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_6761
      · exact prime_oneHundredTwentyEightDV_106000085625457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5733332631309718217) ^ 2866666315654859108 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 5733332631309718217) ^ 848000685003656 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 5733332631309718217) ^ 54088 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_6383178439405208663 : Nat.Prime 6383178439405208663 := by
  apply lucas_primality 6383178439405208663 (5 : ZMod 6383178439405208663)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (109, 1), (241, 1), (257, 1), (281, 1), (7481, 1), (17299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (109, 1), (241, 1), (257, 1), (281, 1), (7481, 1), (17299, 1)] : List FactorBlock).map factorBlockValue).prod) = 6383178439405208663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_13
      · exact prime_oneHundredTwentyEightDV_109
      · exact prime_oneHundredTwentyEightDV_241
      · exact prime_oneHundredTwentyEightDV_257
      · exact prime_oneHundredTwentyEightDV_281
      · exact prime_oneHundredTwentyEightDV_7481
      · exact prime_oneHundredTwentyEightDV_17299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6383178439405208663) ^ 3191589219702604331 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 6383178439405208663) ^ 491013726108092974 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 6383178439405208663) ^ 58561270086286318 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 6383178439405208663) ^ 26486217590892982 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 6383178439405208663) ^ 24837270192238166 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 6383178439405208663) ^ 22715937506780102 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 6383178439405208663) ^ 853252030397702 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 6383178439405208663) ^ 368991180958738 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_10488366250609367641 : Nat.Prime 10488366250609367641 := by
  apply lucas_primality 10488366250609367641 (7 : ZMod 10488366250609367641)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (13, 1), (197, 1), (34128485782277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (13, 1), (197, 1), (34128485782277, 1)] : List FactorBlock).map factorBlockValue).prod) = 10488366250609367641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_13
      · exact prime_oneHundredTwentyEightDV_197
      · exact prime_oneHundredTwentyEightDV_34128485782277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 10488366250609367641) ^ 5244183125304683820 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 10488366250609367641) ^ 3496122083536455880 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 10488366250609367641) ^ 2097673250121873528 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 10488366250609367641) ^ 806797403893028280 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 10488366250609367641) ^ 53240437820352120 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 10488366250609367641) ^ 307320 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_12736538957398727773 : Nat.Prime 12736538957398727773 := by
  apply lucas_primality 12736538957398727773 (5 : ZMod 12736538957398727773)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (1327, 1), (38087280527143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (1327, 1), (38087280527143, 1)] : List FactorBlock).map factorBlockValue).prod) = 12736538957398727773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_7
      · exact prime_oneHundredTwentyEightDV_1327
      · exact prime_oneHundredTwentyEightDV_38087280527143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 12736538957398727773) ^ 6368269478699363886 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 12736538957398727773) ^ 4245512985799575924 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 12736538957398727773) ^ 1819505565342675396 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 12736538957398727773) ^ 9597994692840036 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 12736538957398727773) ^ 334404 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_15386829756014469757 : Nat.Prime 15386829756014469757 := by
  apply lucas_primality 15386829756014469757 (2 : ZMod 15386829756014469757)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (24311933, 1), (52741006361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (24311933, 1), (52741006361, 1)] : List FactorBlock).map factorBlockValue).prod) = 15386829756014469757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_24311933
      · exact prime_oneHundredTwentyEightDV_52741006361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15386829756014469757) ^ 7693414878007234878 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 15386829756014469757) ^ 5128943252004823252 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 15386829756014469757) ^ 632892076332 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 15386829756014469757) ^ 291743196 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_18938912446419637103 : Nat.Prime 18938912446419637103 := by
  apply lucas_primality 18938912446419637103 (5 : ZMod 18938912446419637103)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (179, 1), (197, 1), (205663, 1), (1305718679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (179, 1), (197, 1), (205663, 1), (1305718679, 1)] : List FactorBlock).map factorBlockValue).prod) = 18938912446419637103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_179
      · exact prime_oneHundredTwentyEightDV_197
      · exact prime_oneHundredTwentyEightDV_205663
      · exact prime_oneHundredTwentyEightDV_1305718679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 18938912446419637103) ^ 9469456223209818551 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 18938912446419637103) ^ 105803980147595738 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 18938912446419637103) ^ 96136611403145366 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 18938912446419637103) ^ 92087115555154 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 18938912446419637103) ^ 14504588738 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_23386076191946293627 : Nat.Prime 23386076191946293627 := by
  apply lucas_primality 23386076191946293627 (7 : ZMod 23386076191946293627)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1321, 1), (2950552131206951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1321, 1), (2950552131206951, 1)] : List FactorBlock).map factorBlockValue).prod) = 23386076191946293627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_1321
      · exact prime_oneHundredTwentyEightDV_2950552131206951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 23386076191946293627) ^ 11693038095973146813 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 23386076191946293627) ^ 7795358730648764542 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 23386076191946293627) ^ 17703312787241706 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 23386076191946293627) ^ 7926 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_25181285446128187351 : Nat.Prime 25181285446128187351 := by
  apply lucas_primality 25181285446128187351 (3 : ZMod 25181285446128187351)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (13, 1), (767681, 1), (5607137911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (13, 1), (767681, 1), (5607137911, 1)] : List FactorBlock).map factorBlockValue).prod) = 25181285446128187351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_13
      · exact prime_oneHundredTwentyEightDV_767681
      · exact prime_oneHundredTwentyEightDV_5607137911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 25181285446128187351) ^ 12590642723064093675 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 25181285446128187351) ^ 8393761815376062450 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 25181285446128187351) ^ 5036257089225637470 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 25181285446128187351) ^ 1937021957394475950 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 25181285446128187351) ^ 32801756779350 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 25181285446128187351) ^ 4490933850 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_30229108622289402877 : Nat.Prime 30229108622289402877 := by
  apply lucas_primality 30229108622289402877 (2 : ZMod 30229108622289402877)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (103, 1), (131, 1), (7297, 1), (8528447371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (103, 1), (131, 1), (7297, 1), (8528447371, 1)] : List FactorBlock).map factorBlockValue).prod) = 30229108622289402877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_103
      · exact prime_oneHundredTwentyEightDV_131
      · exact prime_oneHundredTwentyEightDV_7297
      · exact prime_oneHundredTwentyEightDV_8528447371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30229108622289402877) ^ 15114554311144701438 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 30229108622289402877) ^ 10076369540763134292 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 30229108622289402877) ^ 293486491478537892 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 30229108622289402877) ^ 230756554368621396 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 30229108622289402877) ^ 4142676253568508 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 30229108622289402877) ^ 3544503156 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_34058376475197973903 : Nat.Prime 34058376475197973903 := by
  apply lucas_primality 34058376475197973903 (5 : ZMod 34058376475197973903)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1892132026399887439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1892132026399887439, 1)] : List FactorBlock).map factorBlockValue).prod) = 34058376475197973903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_1892132026399887439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 34058376475197973903) ^ 17029188237598986951 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 34058376475197973903) ^ 11352792158399324634 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 34058376475197973903) ^ 18 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_91444985862979344527 : Nat.Prime 91444985862979344527 := by
  apply lucas_primality 91444985862979344527 (7 : ZMod 91444985862979344527)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (577, 1), (595802673036443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (577, 1), (595802673036443, 1)] : List FactorBlock).map factorBlockValue).prod) = 91444985862979344527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_7
      · exact prime_oneHundredTwentyEightDV_19
      · exact prime_oneHundredTwentyEightDV_577
      · exact prime_oneHundredTwentyEightDV_595802673036443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 91444985862979344527) ^ 45722492931489672263 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 91444985862979344527) ^ 13063569408997049218 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 91444985862979344527) ^ 4812893992788386554 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 91444985862979344527) ^ 158483511027693838 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 91444985862979344527) ^ 153482 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_142316877921169440871 : Nat.Prime 142316877921169440871 := by
  apply lucas_primality 142316877921169440871 (7 : ZMod 142316877921169440871)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (1581298643568549343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (1581298643568549343, 1)] : List FactorBlock).map factorBlockValue).prod) = 142316877921169440871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_1581298643568549343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 142316877921169440871) ^ 71158438960584720435 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 142316877921169440871) ^ 47438959307056480290 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 142316877921169440871) ^ 28463375584233888174 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (7 : ZMod 142316877921169440871) ^ 90 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_148091301913139975563 : Nat.Prime 148091301913139975563 := by
  apply lucas_primality 148091301913139975563 (2 : ZMod 148091301913139975563)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (953, 1), (1151, 1), (22501427794609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (953, 1), (1151, 1), (22501427794609, 1)] : List FactorBlock).map factorBlockValue).prod) = 148091301913139975563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_953
      · exact prime_oneHundredTwentyEightDV_1151
      · exact prime_oneHundredTwentyEightDV_22501427794609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 148091301913139975563) ^ 74045650956569987781 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 148091301913139975563) ^ 49363767304379991854 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 148091301913139975563) ^ 155394860349569754 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 148091301913139975563) ^ 128663164129574262 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 148091301913139975563) ^ 6581418 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_368274038806539880759 : Nat.Prime 368274038806539880759 := by
  apply lucas_primality 368274038806539880759 (6 : ZMod 368274038806539880759)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (37, 1), (552964022232041863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (37, 1), (552964022232041863, 1)] : List FactorBlock).map factorBlockValue).prod) = 368274038806539880759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_37
      · exact prime_oneHundredTwentyEightDV_552964022232041863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 368274038806539880759) ^ 184137019403269940379 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 368274038806539880759) ^ 122758012935513293586 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 368274038806539880759) ^ 9953352400176753534 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 368274038806539880759) ^ 666 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_961549878014322831691 : Nat.Prime 961549878014322831691 := by
  apply lucas_primality 961549878014322831691 (10 : ZMod 961549878014322831691)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (197, 1), (223, 1), (729591008638033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (197, 1), (223, 1), (729591008638033, 1)] : List FactorBlock).map factorBlockValue).prod) = 961549878014322831691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_197
      · exact prime_oneHundredTwentyEightDV_223
      · exact prime_oneHundredTwentyEightDV_729591008638033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 961549878014322831691) ^ 480774939007161415845 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (10 : ZMod 961549878014322831691) ^ 320516626004774277230 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (10 : ZMod 961549878014322831691) ^ 192309975602864566338 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (10 : ZMod 961549878014322831691) ^ 4880963847788440770 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (10 : ZMod 961549878014322831691) ^ 4311882861050775030 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (10 : ZMod 961549878014322831691) ^ 1317930 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_963242918308120711067 : Nat.Prime 963242918308120711067 := by
  apply lucas_primality 963242918308120711067 (2 : ZMod 963242918308120711067)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (1181, 1), (44071, 1), (711802770691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (1181, 1), (44071, 1), (711802770691, 1)] : List FactorBlock).map factorBlockValue).prod) = 963242918308120711067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_13
      · exact prime_oneHundredTwentyEightDV_1181
      · exact prime_oneHundredTwentyEightDV_44071
      · exact prime_oneHundredTwentyEightDV_711802770691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 963242918308120711067) ^ 481621459154060355533 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 963242918308120711067) ^ 74095609100624670082 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 963242918308120711067) ^ 815616357585199586 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 963242918308120711067) ^ 21856615876837846 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 963242918308120711067) ^ 1353244126 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_1007002028163415651429 : Nat.Prime 1007002028163415651429 := by
  apply lucas_primality 1007002028163415651429 (2 : ZMod 1007002028163415651429)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (476027, 1), (176285873869097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (476027, 1), (176285873869097, 1)] : List FactorBlock).map factorBlockValue).prod) = 1007002028163415651429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_476027
      · exact prime_oneHundredTwentyEightDV_176285873869097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1007002028163415651429) ^ 503501014081707825714 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1007002028163415651429) ^ 335667342721138550476 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1007002028163415651429) ^ 2115430486429164 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1007002028163415651429) ^ 5712324 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_1160425589371126917677 : Nat.Prime 1160425589371126917677 := by
  apply lucas_primality 1160425589371126917677 (2 : ZMod 1160425589371126917677)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (36097, 1), (8036856174828427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (36097, 1), (8036856174828427, 1)] : List FactorBlock).map factorBlockValue).prod) = 1160425589371126917677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_36097
      · exact prime_oneHundredTwentyEightDV_8036856174828427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1160425589371126917677) ^ 580212794685563458838 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1160425589371126917677) ^ 32147424699313708 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1160425589371126917677) ^ 144388 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_5331286868873039120269 : Nat.Prime 5331286868873039120269 := by
  apply lucas_primality 5331286868873039120269 (2 : ZMod 5331286868873039120269)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (148091301913139975563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (148091301913139975563, 1)] : List FactorBlock).map factorBlockValue).prod) = 5331286868873039120269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_148091301913139975563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5331286868873039120269) ^ 2665643434436519560134 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 5331286868873039120269) ^ 1777095622957679706756 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 5331286868873039120269) ^ 36 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_7367988655907616666421 : Nat.Prime 7367988655907616666421 := by
  apply lucas_primality 7367988655907616666421 (6 : ZMod 7367988655907616666421)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (3253, 1), (3361, 1), (3743896788893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (3253, 1), (3361, 1), (3743896788893, 1)] : List FactorBlock).map factorBlockValue).prod) = 7367988655907616666421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_3253
      · exact prime_oneHundredTwentyEightDV_3361
      · exact prime_oneHundredTwentyEightDV_3743896788893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 7367988655907616666421) ^ 3683994327953808333210 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 7367988655907616666421) ^ 2455996218635872222140 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 7367988655907616666421) ^ 1473597731181523333284 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 7367988655907616666421) ^ 2264982679344487140 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 7367988655907616666421) ^ 2192201325768407220 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 7367988655907616666421) ^ 1967999940 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_15590118387641784184433 : Nat.Prime 15590118387641784184433 := by
  apply lucas_primality 15590118387641784184433 (3 : ZMod 15590118387641784184433)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (53591, 1), (1398602232618869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (53591, 1), (1398602232618869, 1)] : List FactorBlock).map factorBlockValue).prod) = 15590118387641784184433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_13
      · exact prime_oneHundredTwentyEightDV_53591
      · exact prime_oneHundredTwentyEightDV_1398602232618869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 15590118387641784184433) ^ 7795059193820892092216 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 15590118387641784184433) ^ 1199239875972444937264 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 15590118387641784184433) ^ 290909264384724752 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 15590118387641784184433) ^ 11146928 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_21529275638762282183509 : Nat.Prime 21529275638762282183509 := by
  apply lucas_primality 21529275638762282183509 (6 : ZMod 21529275638762282183509)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2155177, 1), (832463553216367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2155177, 1), (832463553216367, 1)] : List FactorBlock).map factorBlockValue).prod) = 21529275638762282183509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_2155177
      · exact prime_oneHundredTwentyEightDV_832463553216367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 21529275638762282183509) ^ 10764637819381141091754 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 21529275638762282183509) ^ 7176425212920760727836 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 21529275638762282183509) ^ 9989562638596404 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (6 : ZMod 21529275638762282183509) ^ 25862124 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_22432835891841214695553 : Nat.Prime 22432835891841214695553 := by
  apply lucas_primality 22432835891841214695553 (5 : ZMod 22432835891841214695553)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (487, 1), (3361, 1), (3965637126181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (487, 1), (3361, 1), (3965637126181, 1)] : List FactorBlock).map factorBlockValue).prod) = 22432835891841214695553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_487
      · exact prime_oneHundredTwentyEightDV_3361
      · exact prime_oneHundredTwentyEightDV_3965637126181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 22432835891841214695553) ^ 11216417945920607347776 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 22432835891841214695553) ^ 7477611963947071565184 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 22432835891841214695553) ^ 46063318053062042496 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 22432835891841214695553) ^ 6674452809235708032 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 22432835891841214695553) ^ 5656804992 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_24209773418193237512047 : Nat.Prime 24209773418193237512047 := by
  apply lucas_primality 24209773418193237512047 (3 : ZMod 24209773418193237512047)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (61, 1), (283, 1), (37534067, 1), (2075756107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (61, 1), (283, 1), (37534067, 1), (2075756107, 1)] : List FactorBlock).map factorBlockValue).prod) = 24209773418193237512047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_61
      · exact prime_oneHundredTwentyEightDV_283
      · exact prime_oneHundredTwentyEightDV_37534067
      · exact prime_oneHundredTwentyEightDV_2075756107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 24209773418193237512047) ^ 12104886709096618756023 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 24209773418193237512047) ^ 8069924472731079170682 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 24209773418193237512047) ^ 396881531445790778886 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 24209773418193237512047) ^ 85546902537785291562 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 24209773418193237512047) ^ 645007998152538 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 24209773418193237512047) ^ 11663110775178 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_145258640509159425072283 : Nat.Prime 145258640509159425072283 := by
  apply lucas_primality 145258640509159425072283 (2 : ZMod 145258640509159425072283)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (24209773418193237512047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (24209773418193237512047, 1)] : List FactorBlock).map factorBlockValue).prod) = 145258640509159425072283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_24209773418193237512047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 145258640509159425072283) ^ 72629320254579712536141 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 145258640509159425072283) ^ 48419546836386475024094 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 145258640509159425072283) ^ 6 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_363690497301491172040717 : Nat.Prime 363690497301491172040717 := by
  apply lucas_primality 363690497301491172040717 (2 : ZMod 363690497301491172040717)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (157, 1), (13511921, 1), (14286766865669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (157, 1), (13511921, 1), (14286766865669, 1)] : List FactorBlock).map factorBlockValue).prod) = 363690497301491172040717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_157
      · exact prime_oneHundredTwentyEightDV_13511921
      · exact prime_oneHundredTwentyEightDV_14286766865669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 363690497301491172040717) ^ 181845248650745586020358 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 363690497301491172040717) ^ 121230165767163724013572 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 363690497301491172040717) ^ 2316499982812045681788 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 363690497301491172040717) ^ 26916268774920396 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 363690497301491172040717) ^ 25456459164 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_448290027505721063125657 : Nat.Prime 448290027505721063125657 := by
  apply lucas_primality 448290027505721063125657 (5 : ZMod 448290027505721063125657)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (17, 1), (21017, 1), (5808790066327169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (17, 1), (21017, 1), (5808790066327169, 1)] : List FactorBlock).map factorBlockValue).prod) = 448290027505721063125657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_17
      · exact prime_oneHundredTwentyEightDV_21017
      · exact prime_oneHundredTwentyEightDV_5808790066327169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 448290027505721063125657) ^ 224145013752860531562828 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 448290027505721063125657) ^ 149430009168573687708552 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 448290027505721063125657) ^ 26370001617983591948568 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 448290027505721063125657) ^ 21329877123553364568 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (5 : ZMod 448290027505721063125657) ^ 77174424 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_1226050289357940765310051 : Nat.Prime 1226050289357940765310051 := by
  apply lucas_primality 1226050289357940765310051 (3 : ZMod 1226050289357940765310051)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (19, 1), (193, 1), (742993236589365067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (19, 1), (193, 1), (742993236589365067, 1)] : List FactorBlock).map factorBlockValue).prod) = 1226050289357940765310051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_19
      · exact prime_oneHundredTwentyEightDV_193
      · exact prime_oneHundredTwentyEightDV_742993236589365067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1226050289357940765310051) ^ 613025144678970382655025 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1226050289357940765310051) ^ 408683429785980255103350 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1226050289357940765310051) ^ 245210057871588153062010 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1226050289357940765310051) ^ 64528962597786356068950 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1226050289357940765310051) ^ 6352592172839071322850 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1226050289357940765310051) ^ 1650150 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_1454761989205964688162869 : Nat.Prime 1454761989205964688162869 := by
  apply lucas_primality 1454761989205964688162869 (2 : ZMod 1454761989205964688162869)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (363690497301491172040717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (363690497301491172040717, 1)] : List FactorBlock).map factorBlockValue).prod) = 1454761989205964688162869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_363690497301491172040717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1454761989205964688162869) ^ 727380994602982344081434 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1454761989205964688162869) ^ 4 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_3649235842802123772491603 : Nat.Prime 3649235842802123772491603 := by
  apply lucas_primality 3649235842802123772491603 (2 : ZMod 3649235842802123772491603)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (29, 1), (409, 1), (3484759, 1), (2596742945747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (29, 1), (409, 1), (3484759, 1), (2596742945747, 1)] : List FactorBlock).map factorBlockValue).prod) = 3649235842802123772491603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_17
      · exact prime_oneHundredTwentyEightDV_29
      · exact prime_oneHundredTwentyEightDV_409
      · exact prime_oneHundredTwentyEightDV_3484759
      · exact prime_oneHundredTwentyEightDV_2596742945747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3649235842802123772491603) ^ 1824617921401061886245801 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3649235842802123772491603) ^ 214660931929536692499506 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3649235842802123772491603) ^ 125835718717314612844538 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3649235842802123772491603) ^ 8922337023966072793378 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3649235842802123772491603) ^ 1047198914703175678 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3649235842802123772491603) ^ 1405312700966 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_3741628413034028204263921 : Nat.Prime 3741628413034028204263921 := by
  apply lucas_primality 3741628413034028204263921 (13 : ZMod 3741628413034028204263921)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (15590118387641784184433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (15590118387641784184433, 1)] : List FactorBlock).map factorBlockValue).prod) = 3741628413034028204263921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_15590118387641784184433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 3741628413034028204263921) ^ 1870814206517014102131960 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (13 : ZMod 3741628413034028204263921) ^ 1247209471011342734754640 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (13 : ZMod 3741628413034028204263921) ^ 748325682606805640852784 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (13 : ZMod 3741628413034028204263921) ^ 240 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_4118275762400295834143969 : Nat.Prime 4118275762400295834143969 := by
  apply lucas_primality 4118275762400295834143969 (3 : ZMod 4118275762400295834143969)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (22447, 1), (5733332631309718217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (22447, 1), (5733332631309718217, 1)] : List FactorBlock).map factorBlockValue).prod) = 4118275762400295834143969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_22447
      · exact prime_oneHundredTwentyEightDV_5733332631309718217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4118275762400295834143969) ^ 2059137881200147917071984 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 4118275762400295834143969) ^ 183466644201910982944 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 4118275762400295834143969) ^ 718304 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_4560472566228528786470611 : Nat.Prime 4560472566228528786470611 := by
  apply lucas_primality 4560472566228528786470611 (10 : ZMod 4560472566228528786470611)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (131, 1), (1160425589371126917677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (131, 1), (1160425589371126917677, 1)] : List FactorBlock).map factorBlockValue).prod) = 4560472566228528786470611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_131
      · exact prime_oneHundredTwentyEightDV_1160425589371126917677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 4560472566228528786470611) ^ 2280236283114264393235305 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (10 : ZMod 4560472566228528786470611) ^ 1520157522076176262156870 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (10 : ZMod 4560472566228528786470611) ^ 912094513245705757294122 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (10 : ZMod 4560472566228528786470611) ^ 34812767681133807530310 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (10 : ZMod 4560472566228528786470611) ^ 3930 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_277670020486534441690741807 : Nat.Prime 277670020486534441690741807 := by
  apply lucas_primality 277670020486534441690741807 (3 : ZMod 277670020486534441690741807)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (571, 1), (7367988655907616666421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (571, 1), (7367988655907616666421, 1)] : List FactorBlock).map factorBlockValue).prod) = 277670020486534441690741807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_11
      · exact prime_oneHundredTwentyEightDV_571
      · exact prime_oneHundredTwentyEightDV_7367988655907616666421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 277670020486534441690741807) ^ 138835010243267220845370903 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 277670020486534441690741807) ^ 92556673495511480563580602 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 277670020486534441690741807) ^ 25242729135139494699158346 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 277670020486534441690741807) ^ 486287251289902699983786 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 277670020486534441690741807) ^ 37686 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_504433870550537569071514283 : Nat.Prime 504433870550537569071514283 := by
  apply lucas_primality 504433870550537569071514283 (2 : ZMod 504433870550537569071514283)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (23, 1), (20884988987, 1), (47733081551131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (23, 1), (20884988987, 1), (47733081551131, 1)] : List FactorBlock).map factorBlockValue).prod) = 504433870550537569071514283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_11
      · exact prime_oneHundredTwentyEightDV_23
      · exact prime_oneHundredTwentyEightDV_20884988987
      · exact prime_oneHundredTwentyEightDV_47733081551131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 504433870550537569071514283) ^ 252216935275268784535757141 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 504433870550537569071514283) ^ 45857624595503415370137662 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 504433870550537569071514283) ^ 21931907415240763872674534 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 504433870550537569071514283) ^ 24152939264872286 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 504433870550537569071514283) ^ 10567804427422 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_928405896718780801972112177 : Nat.Prime 928405896718780801972112177 := by
  apply lucas_primality 928405896718780801972112177 (3 : ZMod 928405896718780801972112177)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (13, 1), (17351, 1), (23386076191946293627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (13, 1), (17351, 1), (23386076191946293627, 1)] : List FactorBlock).map factorBlockValue).prod) = 928405896718780801972112177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_11
      · exact prime_oneHundredTwentyEightDV_13
      · exact prime_oneHundredTwentyEightDV_17351
      · exact prime_oneHundredTwentyEightDV_23386076191946293627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 928405896718780801972112177) ^ 464202948359390400986056088 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 928405896718780801972112177) ^ 84400536065343709270192016 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 928405896718780801972112177) ^ 71415838209136984767085552 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 928405896718780801972112177) ^ 53507342327173119818576 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 928405896718780801972112177) ^ 39699088 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_3362892470336917127143428553 : Nat.Prime 3362892470336917127143428553 := by
  apply lucas_primality 3362892470336917127143428553 (10 : ZMod 3362892470336917127143428553)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (1277, 1), (38153, 1), (45994279, 1), (2977549837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (1277, 1), (38153, 1), (45994279, 1), (2977549837, 1)] : List FactorBlock).map factorBlockValue).prod) = 3362892470336917127143428553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_7
      · exact prime_oneHundredTwentyEightDV_1277
      · exact prime_oneHundredTwentyEightDV_38153
      · exact prime_oneHundredTwentyEightDV_45994279
      · exact prime_oneHundredTwentyEightDV_2977549837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 3362892470336917127143428553) ^ 1681446235168458563571714276 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (10 : ZMod 3362892470336917127143428553) ^ 1120964156778972375714476184 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (10 : ZMod 3362892470336917127143428553) ^ 480413210048131018163346936 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (10 : ZMod 3362892470336917127143428553) ^ 2633431848345275745609576 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (10 : ZMod 3362892470336917127143428553) ^ 88142281611850106862984 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (10 : ZMod 3362892470336917127143428553) ^ 73115451387702308088 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (10 : ZMod 3362892470336917127143428553) ^ 1129416014653566696 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_6579572224572229161802360213 : Nat.Prime 6579572224572229161802360213 := by
  apply lucas_primality 6579572224572229161802360213 (2 : ZMod 6579572224572229161802360213)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (796052281, 1), (229590316476973157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (796052281, 1), (229590316476973157, 1)] : List FactorBlock).map factorBlockValue).prod) = 6579572224572229161802360213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_796052281
      · exact prime_oneHundredTwentyEightDV_229590316476973157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6579572224572229161802360213) ^ 3289786112286114580901180106 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 6579572224572229161802360213) ^ 2193190741524076387267453404 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 6579572224572229161802360213) ^ 8265251393171033652 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 6579572224572229161802360213) ^ 28657882116 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_7566508058258063536072714243 : Nat.Prime 7566508058258063536072714243 := by
  apply lucas_primality 7566508058258063536072714243 (3 : ZMod 7566508058258063536072714243)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (7, 1), (1277, 1), (38153, 1), (45994279, 1), (2977549837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (7, 1), (1277, 1), (38153, 1), (45994279, 1), (2977549837, 1)] : List FactorBlock).map factorBlockValue).prod) = 7566508058258063536072714243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_7
      · exact prime_oneHundredTwentyEightDV_1277
      · exact prime_oneHundredTwentyEightDV_38153
      · exact prime_oneHundredTwentyEightDV_45994279
      · exact prime_oneHundredTwentyEightDV_2977549837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7566508058258063536072714243) ^ 3783254029129031768036357121 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 7566508058258063536072714243) ^ 2522169352752687845357571414 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 7566508058258063536072714243) ^ 1080929722608294790867530606 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 7566508058258063536072714243) ^ 5925221658776870427621546 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 7566508058258063536072714243) ^ 198320133626662740441714 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 7566508058258063536072714243) ^ 164509765622330193198 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (3 : ZMod 7566508058258063536072714243) ^ 2541186032970525066 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_12610846763763439226787857069 : Nat.Prime 12610846763763439226787857069 := by
  apply lucas_primality 12610846763763439226787857069 (2 : ZMod 12610846763763439226787857069)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (89, 1), (347, 1), (2755243, 1), (37051420944511243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (89, 1), (347, 1), (2755243, 1), (37051420944511243, 1)] : List FactorBlock).map factorBlockValue).prod) = 12610846763763439226787857069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_89
      · exact prime_oneHundredTwentyEightDV_347
      · exact prime_oneHundredTwentyEightDV_2755243
      · exact prime_oneHundredTwentyEightDV_37051420944511243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12610846763763439226787857069) ^ 6305423381881719613393928534 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 12610846763763439226787857069) ^ 141694907458016171087504012 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 12610846763763439226787857069) ^ 36342497878280804688149444 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 12610846763763439226787857069) ^ 4577036132117362870276 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 12610846763763439226787857069) ^ 340360678276 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_30266032233032254144290856973 : Nat.Prime 30266032233032254144290856973 := by
  apply lucas_primality 30266032233032254144290856973 (2 : ZMod 30266032233032254144290856973)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7566508058258063536072714243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7566508058258063536072714243, 1)] : List FactorBlock).map factorBlockValue).prod) = 30266032233032254144290856973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_7566508058258063536072714243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 30266032233032254144290856973) ^ 15133016116516127072145428486 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 30266032233032254144290856973) ^ 4 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_151330161165161270721454284803 : Nat.Prime 151330161165161270721454284803 := by
  apply lucas_primality 151330161165161270721454284803 (2 : ZMod 151330161165161270721454284803)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (911, 1), (631662907333, 1), (3207065946347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (911, 1), (631662907333, 1), (3207065946347, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_41
      · exact prime_oneHundredTwentyEightDV_911
      · exact prime_oneHundredTwentyEightDV_631662907333
      · exact prime_oneHundredTwentyEightDV_3207065946347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 151330161165161270721454284803) ^ 75665080582580635360727142401 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 151330161165161270721454284803) ^ 3690979540613689529791567922 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 151330161165161270721454284803) ^ 166114337173612810890729182 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 151330161165161270721454284803) ^ 239574240324013594 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 151330161165161270721454284803) ^ 47186482503589766 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_151330161165161270721454284811 : Nat.Prime 151330161165161270721454284811 := by
  apply lucas_primality 151330161165161270721454284811 (10 : ZMod 151330161165161270721454284811)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (113, 1), (269, 1), (1991617, 1), (83323535982942023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (113, 1), (269, 1), (1991617, 1), (83323535982942023, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_3
      · exact prime_oneHundredTwentyEightDV_5
      · exact prime_oneHundredTwentyEightDV_113
      · exact prime_oneHundredTwentyEightDV_269
      · exact prime_oneHundredTwentyEightDV_1991617
      · exact prime_oneHundredTwentyEightDV_83323535982942023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 151330161165161270721454284811) ^ 75665080582580635360727142405 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (10 : ZMod 151330161165161270721454284811) ^ 50443387055053756907151428270 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (10 : ZMod 151330161165161270721454284811) ^ 30266032233032254144290856962 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (10 : ZMod 151330161165161270721454284811) ^ 1339204966063374077181011370 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (10 : ZMod 151330161165161270721454284811) ^ 562565654889075355841837490 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (10 : ZMod 151330161165161270721454284811) ^ 75983565698204660193930 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (10 : ZMod 151330161165161270721454284811) ^ 1816175458470 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyEightDV_151330161165161270721454284827 : Nat.Prime 151330161165161270721454284827 := by
  apply lucas_primality 151330161165161270721454284827 (2 : ZMod 151330161165161270721454284827)
  · rw [← oneHundredTwentyEightDVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (1603111, 1), (963242918308120711067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (1603111, 1), (963242918308120711067, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyEightDV_2
      · exact prime_oneHundredTwentyEightDV_7
      · exact prime_oneHundredTwentyEightDV_1603111
      · exact prime_oneHundredTwentyEightDV_963242918308120711067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 151330161165161270721454284827) ^ 75665080582580635360727142413 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 151330161165161270721454284827) ^ 21618594452165895817350612118 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 151330161165161270721454284827) ^ 94397805994195829684566 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide
    · change (2 : ZMod 151330161165161270721454284827) ^ 157104878 ≠ 1
      rw [← oneHundredTwentyEightDVFastPow_eq_pow]
      decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284800 : Nat.totient 151330161165161270721454284800 = 60531711210754398962122752000 := by
  rw [← show ((([(2, 13), (5, 2), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284800 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_5, prime_oneHundredTwentyEightDV_171401, prime_oneHundredTwentyEightDV_714027719, prime_oneHundredTwentyEightDV_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284801 : Nat.totient 151330161165161270721454284801 = 93614873709854819489109626880 := by
  rw [← show ((([(3, 1), (17, 1), (71, 1), (3281297, 1), (12736538957398727773, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284801 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_3, prime_oneHundredTwentyEightDV_17, prime_oneHundredTwentyEightDV_71, prime_oneHundredTwentyEightDV_3281297, prime_oneHundredTwentyEightDV_12736538957398727773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284802 : Nat.totient 151330161165161270721454284802 = 73738559428146932665122940800 := by
  rw [← show ((([(2, 1), (41, 1), (911, 1), (631662907333, 1), (3207065946347, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284802 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_41, prime_oneHundredTwentyEightDV_911, prime_oneHundredTwentyEightDV_631662907333, prime_oneHundredTwentyEightDV_3207065946347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284803 : Nat.totient 151330161165161270721454284803 = 151330161165161270721454284802 := by
  rw [← show ((([(151330161165161270721454284803, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284803 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_151330161165161270721454284803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284804 : Nat.totient 151330161165161270721454284804 = 50438007574723688254393807872 := by
  rw [← show ((([(2, 2), (3, 2), (9377, 1), (448290027505721063125657, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284804 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_3, prime_oneHundredTwentyEightDV_9377, prime_oneHundredTwentyEightDV_448290027505721063125657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284805 : Nat.totient 151330161165161270721454284805 = 94629722820341768799495874560 := by
  rw [← show ((([(5, 1), (7, 1), (13, 2), (83, 1), (29389, 1), (10488366250609367641, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284805 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_5, prime_oneHundredTwentyEightDV_7, prime_oneHundredTwentyEightDV_13, prime_oneHundredTwentyEightDV_83, prime_oneHundredTwentyEightDV_29389, prime_oneHundredTwentyEightDV_10488366250609367641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284806 : Nat.totient 151330161165161270721454284806 = 75182142815549178039538718976 := by
  rw [← show ((([(2, 1), (199, 1), (733, 1), (37669439, 1), (78605887, 1), (175183913, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284806 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_199, prime_oneHundredTwentyEightDV_733, prime_oneHundredTwentyEightDV_37669439, prime_oneHundredTwentyEightDV_78605887, prime_oneHundredTwentyEightDV_175183913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284807 : Nat.totient 151330161165161270721454284807 = 96339826249976067593778292800 := by
  rw [← show ((([(3, 1), (23, 1), (601, 1), (3649235842802123772491603, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284807 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_3, prime_oneHundredTwentyEightDV_23, prime_oneHundredTwentyEightDV_601, prime_oneHundredTwentyEightDV_3649235842802123772491603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284808 : Nat.totient 151330161165161270721454284808 = 72982664068293201345537722112 := by
  rw [← show ((([(2, 3), (29, 1), (997, 1), (1953042799, 1), (334989034308223, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284808 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_29, prime_oneHundredTwentyEightDV_997, prime_oneHundredTwentyEightDV_1953042799, prime_oneHundredTwentyEightDV_334989034308223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284809 : Nat.totient 151330161165161270721454284809 = 136581813942739663710875346000 := by
  rw [← show ((([(11, 1), (139, 1), (102931, 1), (961549878014322831691, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284809 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_11, prime_oneHundredTwentyEightDV_139, prime_oneHundredTwentyEightDV_102931, prime_oneHundredTwentyEightDV_961549878014322831691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284810 : Nat.totient 151330161165161270721454284810 = 39848878392041079932447686656 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (113, 1), (269, 1), (1991617, 1), (83323535982942023, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284810 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_3, prime_oneHundredTwentyEightDV_5, prime_oneHundredTwentyEightDV_113, prime_oneHundredTwentyEightDV_269, prime_oneHundredTwentyEightDV_1991617, prime_oneHundredTwentyEightDV_83323535982942023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284811 : Nat.totient 151330161165161270721454284811 = 151330161165161270721454284810 := by
  rw [← show ((([(151330161165161270721454284811, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284811 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_151330161165161270721454284811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284812 : Nat.totient 151330161165161270721454284812 = 63756531879906322800903100032 := by
  rw [← show ((([(2, 2), (7, 1), (59, 1), (69967783, 1), (1309234191118560457, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284812 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_7, prime_oneHundredTwentyEightDV_59, prime_oneHundredTwentyEightDV_69967783, prime_oneHundredTwentyEightDV_1309234191118560457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284813 : Nat.totient 151330161165161270721454284813 = 100804685603915400296146363440 := by
  rw [← show ((([(3, 3), (1229, 1), (4560472566228528786470611, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284813 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_3, prime_oneHundredTwentyEightDV_1229, prime_oneHundredTwentyEightDV_4560472566228528786470611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284814 : Nat.totient 151330161165161270721454284814 = 75665080582424466409980206616 := by
  rw [← show ((([(2, 1), (484509340493, 1), (156168466237595299, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284814 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_484509340493, prime_oneHundredTwentyEightDV_156168466237595299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284815 : Nat.totient 151330161165161270721454284815 = 119953448850182878810400460192 := by
  rw [← show ((([(5, 1), (109, 1), (277670020486534441690741807, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284815 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_5, prime_oneHundredTwentyEightDV_109, prime_oneHundredTwentyEightDV_277670020486534441690741807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284816 : Nat.totient 151330161165161270721454284816 = 49732852754133087653981002752 := by
  rw [← show ((([(2, 4), (3, 1), (89, 1), (347, 1), (2755243, 1), (37051420944511243, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284816 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_3, prime_oneHundredTwentyEightDV_89, prime_oneHundredTwentyEightDV_347, prime_oneHundredTwentyEightDV_2755243, prime_oneHundredTwentyEightDV_37051420944511243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284817 : Nat.totient 151330161165161270721454284817 = 142616496755667731662101353472 := by
  rw [← show ((([(19, 1), (233, 1), (1069, 1), (1766153, 1), (18105475874157703, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284817 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_19, prime_oneHundredTwentyEightDV_233, prime_oneHundredTwentyEightDV_1069, prime_oneHundredTwentyEightDV_1766153, prime_oneHundredTwentyEightDV_18105475874157703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284818 : Nat.totient 151330161165161270721454284818 = 63090542801509065350114181120 := by
  rw [← show ((([(2, 1), (13, 1), (17, 1), (37, 1), (97, 1), (599, 1), (631, 1), (16693, 1), (15119561361733, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284818 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_13, prime_oneHundredTwentyEightDV_17, prime_oneHundredTwentyEightDV_37, prime_oneHundredTwentyEightDV_97, prime_oneHundredTwentyEightDV_599, prime_oneHundredTwentyEightDV_631, prime_oneHundredTwentyEightDV_16693, prime_oneHundredTwentyEightDV_15119561361733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284819 : Nat.totient 151330161165161270721454284819 = 86474365724639245308328758240 := by
  rw [← show ((([(3, 1), (7, 1), (7156091, 1), (1007002028163415651429, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284819 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_3, prime_oneHundredTwentyEightDV_7, prime_oneHundredTwentyEightDV_7156091, prime_oneHundredTwentyEightDV_1007002028163415651429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284820 : Nat.totient 151330161165161270721454284820 = 53990799371370877173709824000 := by
  rw [← show ((([(2, 2), (5, 1), (11, 1), (53, 1), (846733, 1), (100123619, 1), (153088976401, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284820 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_5, prime_oneHundredTwentyEightDV_11, prime_oneHundredTwentyEightDV_53, prime_oneHundredTwentyEightDV_846733, prime_oneHundredTwentyEightDV_100123619, prime_oneHundredTwentyEightDV_153088976401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284821 : Nat.totient 151330161165161270721454284821 = 146448470386613047378081028400 := by
  rw [← show ((([(31, 1), (3545263, 1), (4668691, 1), (294930856273127, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284821 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_31, prime_oneHundredTwentyEightDV_3545263, prime_oneHundredTwentyEightDV_4668691, prime_oneHundredTwentyEightDV_294930856273127]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284822 : Nat.totient 151330161165161270721454284822 = 50443386903966044228379094800 := by
  rw [← show ((([(2, 1), (3, 2), (333868229, 1), (25181285446128187351, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284822 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_3, prime_oneHundredTwentyEightDV_333868229, prime_oneHundredTwentyEightDV_25181285446128187351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284823 : Nat.totient 151330161165161270721454284823 = 151329974495518498537443585600 := by
  rw [← show ((([(810697, 1), (52800401701, 1), (3535327911859, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284823 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_810697, prime_oneHundredTwentyEightDV_52800401701, prime_oneHundredTwentyEightDV_3535327911859]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284824 : Nat.totient 151330161165161270721454284824 = 72969856641700927479509964480 := by
  rw [← show ((([(2, 3), (43, 2), (79, 1), (1233371, 1), (104997213222150383, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284824 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_43, prime_oneHundredTwentyEightDV_79, prime_oneHundredTwentyEightDV_1233371, prime_oneHundredTwentyEightDV_104997213222150383]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284825 : Nat.totient 151330161165161270721454284825 = 80709419287832202786433528000 := by
  rw [← show ((([(3, 1), (5, 2), (318009598661, 1), (6344888615620271, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284825 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_3, prime_oneHundredTwentyEightDV_5, prime_oneHundredTwentyEightDV_318009598661, prime_oneHundredTwentyEightDV_6344888615620271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284826 : Nat.totient 151330161165161270721454284826 = 64855742900295118510914640920 := by
  rw [← show ((([(2, 1), (7, 2), (1603111, 1), (963242918308120711067, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284826 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_7, prime_oneHundredTwentyEightDV_1603111, prime_oneHundredTwentyEightDV_963242918308120711067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284827 : Nat.totient 151330161165161270721454284827 = 151330161165161270721454284826 := by
  rw [← show ((([(151330161165161270721454284827, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284827 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_151330161165161270721454284827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284828 : Nat.totient 151330161165161270721454284828 = 50443387055053756907151428272 := by
  rw [← show ((([(2, 2), (3, 1), (12610846763763439226787857069, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284828 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_3, prime_oneHundredTwentyEightDV_12610846763763439226787857069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284829 : Nat.totient 151330161165161270721454284829 = 151098259531274608787367192000 := by
  rw [← show ((([(653, 1), (972991, 1), (494784923, 1), (481378880701, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284829 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_653, prime_oneHundredTwentyEightDV_972991, prime_oneHundredTwentyEightDV_494784923, prime_oneHundredTwentyEightDV_481378880701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284830 : Nat.totient 151330161165161270721454284830 = 57490538482545589629229621248 := by
  rw [← show ((([(2, 1), (5, 1), (23, 1), (293, 1), (367, 1), (1049, 1), (473425327, 1), (12320745817, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284830 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_5, prime_oneHundredTwentyEightDV_23, prime_oneHundredTwentyEightDV_293, prime_oneHundredTwentyEightDV_367, prime_oneHundredTwentyEightDV_1049, prime_oneHundredTwentyEightDV_473425327, prime_oneHundredTwentyEightDV_12320745817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284831 : Nat.totient 151330161165161270721454284831 = 84625949952585887342112000000 := by
  rw [← show ((([(3, 2), (11, 1), (13, 1), (4001, 1), (6451, 1), (4555660527163322963, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284831 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_3, prime_oneHundredTwentyEightDV_11, prime_oneHundredTwentyEightDV_13, prime_oneHundredTwentyEightDV_4001, prime_oneHundredTwentyEightDV_6451, prime_oneHundredTwentyEightDV_4555660527163322963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284832 : Nat.totient 151330161165161270721454284832 = 75655073266440591946121648640 := by
  rw [← show ((([(2, 5), (7561, 1), (2416168199, 1), (258862483991359, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284832 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_7561, prime_oneHundredTwentyEightDV_2416168199, prime_oneHundredTwentyEightDV_258862483991359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284833 : Nat.totient 151330161165161270721454284833 = 129711563447951271830642726400 := by
  rw [← show ((([(7, 1), (40985101, 1), (1298701153, 1), (406155387923, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284833 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_7, prime_oneHundredTwentyEightDV_40985101, prime_oneHundredTwentyEightDV_1298701153, prime_oneHundredTwentyEightDV_406155387923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284834 : Nat.totient 151330161165161270721454284834 = 50201386159965497304980659200 := by
  rw [← show ((([(2, 1), (3, 1), (401, 1), (433, 1), (145258640509159425072283, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284834 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_3, prime_oneHundredTwentyEightDV_401, prime_oneHundredTwentyEightDV_433, prime_oneHundredTwentyEightDV_145258640509159425072283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284835 : Nat.totient 151330161165161270721454284835 = 113828576165204080132453662720 := by
  rw [← show ((([(5, 1), (17, 2), (1181, 1), (6449, 1), (468045269, 1), (29378357623, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284835 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_5, prime_oneHundredTwentyEightDV_17, prime_oneHundredTwentyEightDV_1181, prime_oneHundredTwentyEightDV_6449, prime_oneHundredTwentyEightDV_468045269, prime_oneHundredTwentyEightDV_29378357623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284836 : Nat.totient 151330161165161270721454284836 = 71529207521699558704203448704 := by
  rw [← show ((([(2, 2), (19, 1), (467, 1), (19156283, 1), (158554247, 1), (1403802133, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284836 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_19, prime_oneHundredTwentyEightDV_467, prime_oneHundredTwentyEightDV_19156283, prime_oneHundredTwentyEightDV_158554247, prime_oneHundredTwentyEightDV_1403802133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284837 : Nat.totient 151330161165161270721454284837 = 95466983729729049531420687360 := by
  rw [← show ((([(3, 1), (29, 1), (67, 1), (197, 1), (19359973, 1), (19705843, 1), (345434291, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284837 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_3, prime_oneHundredTwentyEightDV_29, prime_oneHundredTwentyEightDV_67, prime_oneHundredTwentyEightDV_197, prime_oneHundredTwentyEightDV_19359973, prime_oneHundredTwentyEightDV_19705843, prime_oneHundredTwentyEightDV_345434291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284838 : Nat.totient 151330161165161270721454284838 = 75665080552351526735934685896 := by
  rw [← show ((([(2, 1), (2503053647, 1), (30229108622289402877, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284838 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_2503053647, prime_oneHundredTwentyEightDV_30229108622289402877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284839 : Nat.totient 151330161165161270721454284839 = 150130501239118919984626291200 := by
  rw [← show ((([(127, 1), (21767, 1), (126601, 1), (649537433, 1), (665705087, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284839 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_127, prime_oneHundredTwentyEightDV_21767, prime_oneHundredTwentyEightDV_126601, prime_oneHundredTwentyEightDV_649537433, prime_oneHundredTwentyEightDV_665705087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284840 : Nat.totient 151330161165161270721454284840 = 34561757736463959222976364544 := by
  rw [← show ((([(2, 3), (3, 4), (5, 1), (7, 1), (1277, 1), (38153, 1), (45994279, 1), (2977549837, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284840 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_3, prime_oneHundredTwentyEightDV_5, prime_oneHundredTwentyEightDV_7, prime_oneHundredTwentyEightDV_1277, prime_oneHundredTwentyEightDV_38153, prime_oneHundredTwentyEightDV_45994279, prime_oneHundredTwentyEightDV_2977549837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284841 : Nat.totient 151330161165161270721454284841 = 151065134613174116007530238240 := by
  rw [← show ((([(571, 1), (4808394801193, 1), (55117469116147, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284841 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_571, prime_oneHundredTwentyEightDV_4808394801193, prime_oneHundredTwentyEightDV_55117469116147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284842 : Nat.totient 151330161165161270721454284842 = 68710709353282738661888640000 := by
  rw [← show ((([(2, 1), (11, 1), (1901, 1), (3253, 1), (4003, 1), (71341, 1), (252827, 1), (15405947, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284842 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_11, prime_oneHundredTwentyEightDV_1901, prime_oneHundredTwentyEightDV_3253, prime_oneHundredTwentyEightDV_4003, prime_oneHundredTwentyEightDV_71341, prime_oneHundredTwentyEightDV_252827, prime_oneHundredTwentyEightDV_15405947]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284843 : Nat.totient 151330161165161270721454284843 = 98417045795545500728080259840 := by
  rw [← show ((([(3, 1), (41, 1), (10847, 1), (78945989, 1), (1436748238159427, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284843 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_3, prime_oneHundredTwentyEightDV_41, prime_oneHundredTwentyEightDV_10847, prime_oneHundredTwentyEightDV_78945989, prime_oneHundredTwentyEightDV_1436748238159427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284844 : Nat.totient 151330161165161270721454284844 = 68260190257851264320576624640 := by
  rw [← show ((([(2, 2), (13, 1), (47, 1), (827, 1), (4327, 1), (14642821, 1), (1181699726089, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284844 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_13, prime_oneHundredTwentyEightDV_47, prime_oneHundredTwentyEightDV_827, prime_oneHundredTwentyEightDV_4327, prime_oneHundredTwentyEightDV_14642821, prime_oneHundredTwentyEightDV_1181699726089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284845 : Nat.totient 151330161165161270721454284845 = 121049162418476880464346339840 := by
  rw [← show ((([(5, 1), (8089, 1), (3741628413034028204263921, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284845 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_5, prime_oneHundredTwentyEightDV_8089, prime_oneHundredTwentyEightDV_3741628413034028204263921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284846 : Nat.totient 151330161165161270721454284846 = 50332216346184895790636666880 := by
  rw [← show ((([(2, 1), (3, 1), (677, 1), (2129, 1), (4099, 1), (69931, 1), (61046709121033, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284846 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_3, prime_oneHundredTwentyEightDV_677, prime_oneHundredTwentyEightDV_2129, prime_oneHundredTwentyEightDV_4099, prime_oneHundredTwentyEightDV_69931, prime_oneHundredTwentyEightDV_61046709121033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284847 : Nat.totient 151330161165161270721454284847 = 129695402692122779772541638720 := by
  rw [← show ((([(7, 1), (8537, 1), (133711, 1), (18938912446419637103, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284847 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_7, prime_oneHundredTwentyEightDV_8537, prime_oneHundredTwentyEightDV_133711, prime_oneHundredTwentyEightDV_18938912446419637103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284848 : Nat.totient 151330161165161270721454284848 = 75564307122278168809074600000 := by
  rw [← show ((([(2, 4), (751, 1), (3594403, 1), (3503795954666829551, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284848 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_751, prime_oneHundredTwentyEightDV_3594403, prime_oneHundredTwentyEightDV_3503795954666829551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284849 : Nat.totient 151330161165161270721454284849 = 100883521054048144696692056352 := by
  rw [← show ((([(3, 2), (31013, 1), (12347476763, 1), (43909752428719, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284849 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_3, prime_oneHundredTwentyEightDV_31013, prime_oneHundredTwentyEightDV_12347476763, prime_oneHundredTwentyEightDV_43909752428719]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284850 : Nat.totient 151330161165161270721454284850 = 60490399289721878539018186560 := by
  rw [← show ((([(2, 1), (5, 2), (1453, 1), (11818663, 1), (176246916136727123, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284850 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_5, prime_oneHundredTwentyEightDV_1453, prime_oneHundredTwentyEightDV_11818663, prime_oneHundredTwentyEightDV_176246916136727123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284851 : Nat.totient 151330161165161270721454284851 = 150401755268442489919482172512 := by
  rw [← show ((([(163, 1), (928405896718780801972112177, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284851 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_163, prime_oneHundredTwentyEightDV_928405896718780801972112177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284852 : Nat.totient 151330161165161270721454284852 = 45942181400061232509017733120 := by
  rw [← show ((([(2, 2), (3, 1), (17, 1), (31, 1), (26947, 1), (60887, 1), (14584738097576557, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284852 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_3, prime_oneHundredTwentyEightDV_17, prime_oneHundredTwentyEightDV_31, prime_oneHundredTwentyEightDV_26947, prime_oneHundredTwentyEightDV_60887, prime_oneHundredTwentyEightDV_14584738097576557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284853 : Nat.totient 151330161165161270721454284853 = 131591443087145326546285950640 := by
  rw [← show ((([(11, 1), (23, 1), (93706127, 1), (6383178439405208663, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284853 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_11, prime_oneHundredTwentyEightDV_23, prime_oneHundredTwentyEightDV_93706127, prime_oneHundredTwentyEightDV_6383178439405208663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284854 : Nat.totient 151330161165161270721454284854 = 64855783152147428598959739432 := by
  rw [← show ((([(2, 1), (7, 1), (317375587, 1), (34058376475197973903, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284854 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_7, prime_oneHundredTwentyEightDV_317375587, prime_oneHundredTwentyEightDV_34058376475197973903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284855 : Nat.totient 151330161165161270721454284855 = 74395025346643553912732176896 := by
  rw [← show ((([(3, 1), (5, 1), (19, 1), (37, 1), (59432203, 1), (241466608204721173, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284855 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_3, prime_oneHundredTwentyEightDV_5, prime_oneHundredTwentyEightDV_19, prime_oneHundredTwentyEightDV_37, prime_oneHundredTwentyEightDV_59432203, prime_oneHundredTwentyEightDV_241466608204721173]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284856 : Nat.totient 151330161165161270721454284856 = 75659261534623811501974438944 := by
  rw [← show ((([(2, 3), (13003, 1), (1454761989205964688162869, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284856 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_13003, prime_oneHundredTwentyEightDV_1454761989205964688162869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284857 : Nat.totient 151330161165161270721454284857 = 139620718653081485573826768384 := by
  rw [← show ((([(13, 1), (2777, 1), (7607, 1), (70968847, 1), (7764707437133, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284857 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_13, prime_oneHundredTwentyEightDV_2777, prime_oneHundredTwentyEightDV_7607, prime_oneHundredTwentyEightDV_70968847, prime_oneHundredTwentyEightDV_7764707437133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284858 : Nat.totient 151330161165161270721454284858 = 50382538578353141836031278080 := by
  rw [← show ((([(2, 1), (3, 2), (829, 1), (325247041321, 1), (31180645690609, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284858 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_3, prime_oneHundredTwentyEightDV_829, prime_oneHundredTwentyEightDV_325247041321, prime_oneHundredTwentyEightDV_31180645690609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284859 : Nat.totient 151330161165161270721454284859 = 147995838333164792531358720000 := by
  rw [← show ((([(61, 1), (191, 1), (3041, 1), (5807, 1), (46025471, 1), (15980700217, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284859 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_61, prime_oneHundredTwentyEightDV_191, prime_oneHundredTwentyEightDV_3041, prime_oneHundredTwentyEightDV_5807, prime_oneHundredTwentyEightDV_46025471, prime_oneHundredTwentyEightDV_15980700217]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284860 : Nat.totient 151330161165161270721454284860 = 60532064466064508288581713936 := by
  rw [← show ((([(2, 2), (5, 1), (7566508058258063536072714243, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284860 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_5, prime_oneHundredTwentyEightDV_7566508058258063536072714243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284861 : Nat.totient 151330161165161270721454284861 = 86334674423387262659432450496 := by
  rw [← show ((([(3, 1), (7, 1), (619, 1), (26486477, 1), (439532865836238407, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284861 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_3, prime_oneHundredTwentyEightDV_7, prime_oneHundredTwentyEightDV_619, prime_oneHundredTwentyEightDV_26486477, prime_oneHundredTwentyEightDV_439532865836238407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284862 : Nat.totient 151330161165161270721454284862 = 75260318174766680301108820224 := by
  rw [← show ((([(2, 1), (229, 1), (1063, 1), (21787, 1), (3298423, 1), (4325367059753, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284862 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_229, prime_oneHundredTwentyEightDV_1063, prime_oneHundredTwentyEightDV_21787, prime_oneHundredTwentyEightDV_3298423, prime_oneHundredTwentyEightDV_4325367059753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284863 : Nat.totient 151330161165161270721454284863 = 151015819493036626348028852736 := by
  rw [← show ((([(613, 1), (2297, 1), (88867, 1), (1209382014136060249, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284863 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_613, prime_oneHundredTwentyEightDV_2297, prime_oneHundredTwentyEightDV_88867, prime_oneHundredTwentyEightDV_1209382014136060249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284864 : Nat.totient 151330161165161270721454284864 = 45757496639721319570937856000 := by
  rw [← show ((([(2, 6), (3, 1), (11, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284864 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_3, prime_oneHundredTwentyEightDV_11, prime_oneHundredTwentyEightDV_461, prime_oneHundredTwentyEightDV_69997, prime_oneHundredTwentyEightDV_2220502305087140441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284865 : Nat.totient 151330161165161270721454284865 = 121064128932129016577163427888 := by
  rw [← show ((([(5, 1), (30266032233032254144290856973, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284865 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_5, prime_oneHundredTwentyEightDV_30266032233032254144290856973]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284866 : Nat.totient 151330161165161270721454284866 = 72306593422705411585008592896 := by
  rw [← show ((([(2, 1), (29, 1), (107, 1), (1087, 1), (22432835891841214695553, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284866 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_29, prime_oneHundredTwentyEightDV_107, prime_oneHundredTwentyEightDV_1087, prime_oneHundredTwentyEightDV_22432835891841214695553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284867 : Nat.totient 151330161165161270721454284867 = 98540570061002701084406468256 := by
  rw [← show ((([(3, 3), (43, 1), (3277333204279, 1), (39771564643693, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284867 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_3, prime_oneHundredTwentyEightDV_43, prime_oneHundredTwentyEightDV_3277333204279, prime_oneHundredTwentyEightDV_39771564643693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284868 : Nat.totient 151330161165161270721454284868 = 64722608556541216145327070720 := by
  rw [← show ((([(2, 2), (7, 1), (487, 1), (91568473, 1), (121197184259488681, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284868 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_7, prime_oneHundredTwentyEightDV_487, prime_oneHundredTwentyEightDV_91568473, prime_oneHundredTwentyEightDV_121197184259488681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284869 : Nat.totient 151330161165161270721454284869 = 141865870065085732711294955520 := by
  rw [← show ((([(17, 1), (313, 1), (1321, 1), (21529275638762282183509, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284869 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_17, prime_oneHundredTwentyEightDV_313, prime_oneHundredTwentyEightDV_1321, prime_oneHundredTwentyEightDV_21529275638762282183509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284870 : Nat.totient 151330161165161270721454284870 = 37227547957376249903176243200 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (13, 1), (2707, 1), (4051, 1), (81036133, 1), (436648205893, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284870 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_3, prime_oneHundredTwentyEightDV_5, prime_oneHundredTwentyEightDV_13, prime_oneHundredTwentyEightDV_2707, prime_oneHundredTwentyEightDV_4051, prime_oneHundredTwentyEightDV_81036133, prime_oneHundredTwentyEightDV_436648205893]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284871 : Nat.totient 151330161165161270721454284871 = 146716610631854665804287621120 := by
  rw [← show ((([(59, 1), (73, 1), (16963, 1), (71933, 1), (2329331, 1), (12361995497, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284871 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_59, prime_oneHundredTwentyEightDV_73, prime_oneHundredTwentyEightDV_16963, prime_oneHundredTwentyEightDV_71933, prime_oneHundredTwentyEightDV_2329331, prime_oneHundredTwentyEightDV_12361995497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284872 : Nat.totient 151330161165161270721454284872 = 74283865382498544278615800320 := by
  rw [← show ((([(2, 3), (71, 1), (239, 1), (22307, 1), (1536649, 1), (32520964175027, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284872 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_71, prime_oneHundredTwentyEightDV_239, prime_oneHundredTwentyEightDV_22307, prime_oneHundredTwentyEightDV_1536649, prime_oneHundredTwentyEightDV_32520964175027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284873 : Nat.totient 151330161165161270721454284873 = 98983250070215731589065471424 := by
  rw [← show ((([(3, 1), (53, 1), (1264130673683, 1), (752898446118509, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284873 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_3, prime_oneHundredTwentyEightDV_53, prime_oneHundredTwentyEightDV_1264130673683, prime_oneHundredTwentyEightDV_752898446118509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284874 : Nat.totient 151330161165161270721454284874 = 71608578956616343964095315584 := by
  rw [← show ((([(2, 1), (19, 1), (967, 1), (4118275762400295834143969, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284874 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_19, prime_oneHundredTwentyEightDV_967, prime_oneHundredTwentyEightDV_4118275762400295834143969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284875 : Nat.totient 151330161165161270721454284875 = 93894957933140897981134848000 := by
  rw [← show ((([(5, 3), (7, 2), (11, 1), (283, 1), (887, 1), (66713, 1), (134123905279457, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284875 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_5, prime_oneHundredTwentyEightDV_7, prime_oneHundredTwentyEightDV_11, prime_oneHundredTwentyEightDV_283, prime_oneHundredTwentyEightDV_887, prime_oneHundredTwentyEightDV_66713, prime_oneHundredTwentyEightDV_134123905279457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284876 : Nat.totient 151330161165161270721454284876 = 48250196252917836759805259520 := by
  rw [← show ((([(2, 2), (3, 2), (23, 1), (796052281, 1), (229590316476973157, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284876 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_3, prime_oneHundredTwentyEightDV_23, prime_oneHundredTwentyEightDV_796052281, prime_oneHundredTwentyEightDV_229590316476973157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284877 : Nat.totient 151330161165161270721454284877 = 150365140987964021019149154048 := by
  rw [← show ((([(157, 1), (135347, 1), (6585809, 1), (1081354462857307, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284877 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_157, prime_oneHundredTwentyEightDV_135347, prime_oneHundredTwentyEightDV_6585809, prime_oneHundredTwentyEightDV_1081354462857307]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284878 : Nat.totient 151330161165161270721454284878 = 75585532178168812167259287552 := by
  rw [← show ((([(2, 1), (2237, 1), (2909, 1), (3833, 1), (486329783, 1), (6237579697, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284878 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_2237, prime_oneHundredTwentyEightDV_2909, prime_oneHundredTwentyEightDV_3833, prime_oneHundredTwentyEightDV_486329783, prime_oneHundredTwentyEightDV_6237579697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284879 : Nat.totient 151330161165161270721454284879 = 100884322009528797932772154200 := by
  rw [← show ((([(3, 1), (41143, 1), (1226050289357940765310051, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284879 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_3, prime_oneHundredTwentyEightDV_41143, prime_oneHundredTwentyEightDV_1226050289357940765310051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284880 : Nat.totient 151330161165161270721454284880 = 60259130126364902783838289920 := by
  rw [← show ((([(2, 4), (5, 1), (271, 1), (1217, 1), (4440187, 1), (1291737826932829, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284880 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_5, prime_oneHundredTwentyEightDV_271, prime_oneHundredTwentyEightDV_1217, prime_oneHundredTwentyEightDV_4440187, prime_oneHundredTwentyEightDV_1291737826932829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284881 : Nat.totient 151330161165161270721454284881 = 151282914769786812260021442880 := by
  rw [← show ((([(3203, 1), (11211686891, 1), (4214029729908497, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284881 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_3203, prime_oneHundredTwentyEightDV_11211686891, prime_oneHundredTwentyEightDV_4214029729908497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284882 : Nat.totient 151330161165161270721454284882 = 43237188891005243174851699200 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (3244440161, 1), (1110545701743020261, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284882 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_3, prime_oneHundredTwentyEightDV_7, prime_oneHundredTwentyEightDV_3244440161, prime_oneHundredTwentyEightDV_1110545701743020261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284883 : Nat.totient 151330161165161270721454284883 = 134731430441037270090517639680 := by
  rw [← show ((([(13, 1), (31, 1), (317, 1), (5309, 1), (11498719, 1), (19404345549223, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284883 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_13, prime_oneHundredTwentyEightDV_31, prime_oneHundredTwentyEightDV_317, prime_oneHundredTwentyEightDV_5309, prime_oneHundredTwentyEightDV_11498719, prime_oneHundredTwentyEightDV_19404345549223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284884 : Nat.totient 151330161165161270721454284884 = 73090919109040885323590860800 := by
  rw [← show ((([(2, 2), (41, 1), (167, 1), (257, 1), (65119, 1), (330159903839178421, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284884 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_41, prime_oneHundredTwentyEightDV_167, prime_oneHundredTwentyEightDV_257, prime_oneHundredTwentyEightDV_65119, prime_oneHundredTwentyEightDV_330159903839178421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284885 : Nat.totient 151330161165161270721454284885 = 80709419288086011051442285248 := by
  rw [← show ((([(3, 2), (5, 1), (3362892470336917127143428553, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284885 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_3, prime_oneHundredTwentyEightDV_5, prime_oneHundredTwentyEightDV_3362892470336917127143428553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284886 : Nat.totient 151330161165161270721454284886 = 64678897266555029380221911040 := by
  rw [← show ((([(2, 1), (11, 1), (17, 1), (1487, 1), (4129, 1), (31643, 1), (2293919, 1), (907908979, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284886 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_11, prime_oneHundredTwentyEightDV_17, prime_oneHundredTwentyEightDV_1487, prime_oneHundredTwentyEightDV_4129, prime_oneHundredTwentyEightDV_31643, prime_oneHundredTwentyEightDV_2293919, prime_oneHundredTwentyEightDV_907908979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284887 : Nat.totient 151330161165161270721454284887 = 151330161022844392799221511520 := by
  rw [← show ((([(1063332497, 1), (142316877921169440871, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284887 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_1063332497, prime_oneHundredTwentyEightDV_142316877921169440871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284888 : Nat.totient 151330161165161270721454284888 = 49831887044864562336247578624 := by
  rw [← show ((([(2, 3), (3, 1), (83, 1), (13627, 1), (560969, 1), (21727217, 1), (457396609, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284888 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_3, prime_oneHundredTwentyEightDV_83, prime_oneHundredTwentyEightDV_13627, prime_oneHundredTwentyEightDV_560969, prime_oneHundredTwentyEightDV_21727217, prime_oneHundredTwentyEightDV_457396609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284889 : Nat.totient 151330161165161270721454284889 = 129711566620674396359586815760 := by
  rw [← show ((([(7, 1), (1405006411, 1), (15386829756014469757, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284889 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_7, prime_oneHundredTwentyEightDV_1405006411, prime_oneHundredTwentyEightDV_15386829756014469757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284890 : Nat.totient 151330161165161270721454284890 = 60531617896344154659421603008 := by
  rw [← show ((([(2, 1), (5, 1), (135589, 1), (459097039, 1), (243106485607259, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284890 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_5, prime_oneHundredTwentyEightDV_135589, prime_oneHundredTwentyEightDV_459097039, prime_oneHundredTwentyEightDV_243106485607259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284891 : Nat.totient 151330161165161270721454284891 = 98295597952302745678686633120 := by
  rw [← show ((([(3, 1), (47, 1), (223, 1), (52631, 1), (91444985862979344527, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284891 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_3, prime_oneHundredTwentyEightDV_47, prime_oneHundredTwentyEightDV_223, prime_oneHundredTwentyEightDV_52631, prime_oneHundredTwentyEightDV_91444985862979344527]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284892 : Nat.totient 151330161165161270721454284892 = 73620078132584027763461734272 := by
  rw [← show ((([(2, 2), (37, 1), (270573497, 1), (3779014206087569507, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284892 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_37, prime_oneHundredTwentyEightDV_270573497, prime_oneHundredTwentyEightDV_3779014206087569507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284893 : Nat.totient 151330161165161270721454284893 = 143365319877515458863488792688 := by
  rw [← show ((([(19, 1), (1493963, 1), (5331286868873039120269, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284893 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_19, prime_oneHundredTwentyEightDV_1493963, prime_oneHundredTwentyEightDV_5331286868873039120269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284894 : Nat.totient 151330161165161270721454284894 = 50103859751168377916268663840 := by
  rw [← show ((([(2, 1), (3, 3), (149, 1), (51071, 1), (368274038806539880759, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284894 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_3, prime_oneHundredTwentyEightDV_149, prime_oneHundredTwentyEightDV_51071, prime_oneHundredTwentyEightDV_368274038806539880759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284895 : Nat.totient 151330161165161270721454284895 = 116869653278739829909828899456 := by
  rw [← show ((([(5, 1), (29, 1), (7187, 1), (32587, 1), (4456208132610353279, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284895 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_5, prime_oneHundredTwentyEightDV_29, prime_oneHundredTwentyEightDV_7187, prime_oneHundredTwentyEightDV_32587, prime_oneHundredTwentyEightDV_4456208132610353279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284896 : Nat.totient 151330161165161270721454284896 = 58625950564158746679558144000 := by
  rw [← show ((([(2, 5), (7, 1), (13, 1), (101, 1), (103, 1), (1163, 1), (3221, 1), (20357, 1), (53279, 1), (1229519, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284896 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_7, prime_oneHundredTwentyEightDV_13, prime_oneHundredTwentyEightDV_101, prime_oneHundredTwentyEightDV_103, prime_oneHundredTwentyEightDV_1163, prime_oneHundredTwentyEightDV_3221, prime_oneHundredTwentyEightDV_20357, prime_oneHundredTwentyEightDV_53279, prime_oneHundredTwentyEightDV_1229519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284897 : Nat.totient 151330161165161270721454284897 = 91687111099955048192933088000 := by
  rw [← show ((([(3, 1), (11, 2), (3343, 1), (132361, 1), (8844323, 1), (106526549111, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284897 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_3, prime_oneHundredTwentyEightDV_11, prime_oneHundredTwentyEightDV_3343, prime_oneHundredTwentyEightDV_132361, prime_oneHundredTwentyEightDV_8844323, prime_oneHundredTwentyEightDV_106526549111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284898 : Nat.totient 151330161165161270721454284898 = 75643809867683072974617120000 := by
  rw [← show ((([(2, 1), (3559, 1), (7388921, 1), (288995191, 1), (9956251801, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284898 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_3559, prime_oneHundredTwentyEightDV_7388921, prime_oneHundredTwentyEightDV_288995191, prime_oneHundredTwentyEightDV_9956251801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284899 : Nat.totient 151330161165161270721454284899 = 144750588940589041559651924664 := by
  rw [← show ((([(23, 1), (6579572224572229161802360213, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284899 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_23, prime_oneHundredTwentyEightDV_6579572224572229161802360213]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284900 : Nat.totient 151330161165161270721454284900 = 40354709644043005525721142560 := by
  rw [← show ((([(2, 2), (3, 1), (5, 2), (504433870550537569071514283, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284900 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_2, prime_oneHundredTwentyEightDV_3, prime_oneHundredTwentyEightDV_5, prime_oneHundredTwentyEightDV_504433870550537569071514283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyEightDV_151330161165161270721454284901 : Nat.totient 151330161165161270721454284901 = 151243239639715278647523750000 := by
  rw [← show ((([(1741, 1), (1226793751, 1), (70852498304454511, 1)] : List FactorBlock).map factorBlockValue).prod) = 151330161165161270721454284901 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyEightDV_1741, prime_oneHundredTwentyEightDV_1226793751, prime_oneHundredTwentyEightDV_70852498304454511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredTwentyEightDV : certifiedKill 1 151330161165161270721454284799 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredTwentyEightDV_151330161165161270721454284800, phi_oneHundredTwentyEightDV_151330161165161270721454284801, phi_oneHundredTwentyEightDV_151330161165161270721454284802,
    phi_oneHundredTwentyEightDV_151330161165161270721454284803, phi_oneHundredTwentyEightDV_151330161165161270721454284804, phi_oneHundredTwentyEightDV_151330161165161270721454284805,
    phi_oneHundredTwentyEightDV_151330161165161270721454284806, phi_oneHundredTwentyEightDV_151330161165161270721454284807, phi_oneHundredTwentyEightDV_151330161165161270721454284808,
    phi_oneHundredTwentyEightDV_151330161165161270721454284809, phi_oneHundredTwentyEightDV_151330161165161270721454284810, phi_oneHundredTwentyEightDV_151330161165161270721454284811,
    phi_oneHundredTwentyEightDV_151330161165161270721454284812, phi_oneHundredTwentyEightDV_151330161165161270721454284813, phi_oneHundredTwentyEightDV_151330161165161270721454284814,
    phi_oneHundredTwentyEightDV_151330161165161270721454284815, phi_oneHundredTwentyEightDV_151330161165161270721454284816, phi_oneHundredTwentyEightDV_151330161165161270721454284817,
    phi_oneHundredTwentyEightDV_151330161165161270721454284818, phi_oneHundredTwentyEightDV_151330161165161270721454284819, phi_oneHundredTwentyEightDV_151330161165161270721454284820,
    phi_oneHundredTwentyEightDV_151330161165161270721454284821, phi_oneHundredTwentyEightDV_151330161165161270721454284822, phi_oneHundredTwentyEightDV_151330161165161270721454284823,
    phi_oneHundredTwentyEightDV_151330161165161270721454284824, phi_oneHundredTwentyEightDV_151330161165161270721454284825, phi_oneHundredTwentyEightDV_151330161165161270721454284826,
    phi_oneHundredTwentyEightDV_151330161165161270721454284827, phi_oneHundredTwentyEightDV_151330161165161270721454284828, phi_oneHundredTwentyEightDV_151330161165161270721454284829,
    phi_oneHundredTwentyEightDV_151330161165161270721454284830, phi_oneHundredTwentyEightDV_151330161165161270721454284831, phi_oneHundredTwentyEightDV_151330161165161270721454284832,
    phi_oneHundredTwentyEightDV_151330161165161270721454284833, phi_oneHundredTwentyEightDV_151330161165161270721454284834, phi_oneHundredTwentyEightDV_151330161165161270721454284835,
    phi_oneHundredTwentyEightDV_151330161165161270721454284836, phi_oneHundredTwentyEightDV_151330161165161270721454284837, phi_oneHundredTwentyEightDV_151330161165161270721454284838,
    phi_oneHundredTwentyEightDV_151330161165161270721454284839, phi_oneHundredTwentyEightDV_151330161165161270721454284840, phi_oneHundredTwentyEightDV_151330161165161270721454284841,
    phi_oneHundredTwentyEightDV_151330161165161270721454284842, phi_oneHundredTwentyEightDV_151330161165161270721454284843, phi_oneHundredTwentyEightDV_151330161165161270721454284844,
    phi_oneHundredTwentyEightDV_151330161165161270721454284845, phi_oneHundredTwentyEightDV_151330161165161270721454284846, phi_oneHundredTwentyEightDV_151330161165161270721454284847,
    phi_oneHundredTwentyEightDV_151330161165161270721454284848, phi_oneHundredTwentyEightDV_151330161165161270721454284849, phi_oneHundredTwentyEightDV_151330161165161270721454284850,
    phi_oneHundredTwentyEightDV_151330161165161270721454284851, phi_oneHundredTwentyEightDV_151330161165161270721454284852, phi_oneHundredTwentyEightDV_151330161165161270721454284853,
    phi_oneHundredTwentyEightDV_151330161165161270721454284854, phi_oneHundredTwentyEightDV_151330161165161270721454284855, phi_oneHundredTwentyEightDV_151330161165161270721454284856,
    phi_oneHundredTwentyEightDV_151330161165161270721454284857, phi_oneHundredTwentyEightDV_151330161165161270721454284858, phi_oneHundredTwentyEightDV_151330161165161270721454284859,
    phi_oneHundredTwentyEightDV_151330161165161270721454284860, phi_oneHundredTwentyEightDV_151330161165161270721454284861, phi_oneHundredTwentyEightDV_151330161165161270721454284862,
    phi_oneHundredTwentyEightDV_151330161165161270721454284863, phi_oneHundredTwentyEightDV_151330161165161270721454284864, phi_oneHundredTwentyEightDV_151330161165161270721454284865,
    phi_oneHundredTwentyEightDV_151330161165161270721454284866, phi_oneHundredTwentyEightDV_151330161165161270721454284867, phi_oneHundredTwentyEightDV_151330161165161270721454284868,
    phi_oneHundredTwentyEightDV_151330161165161270721454284869, phi_oneHundredTwentyEightDV_151330161165161270721454284870, phi_oneHundredTwentyEightDV_151330161165161270721454284871,
    phi_oneHundredTwentyEightDV_151330161165161270721454284872, phi_oneHundredTwentyEightDV_151330161165161270721454284873, phi_oneHundredTwentyEightDV_151330161165161270721454284874,
    phi_oneHundredTwentyEightDV_151330161165161270721454284875, phi_oneHundredTwentyEightDV_151330161165161270721454284876, phi_oneHundredTwentyEightDV_151330161165161270721454284877,
    phi_oneHundredTwentyEightDV_151330161165161270721454284878, phi_oneHundredTwentyEightDV_151330161165161270721454284879, phi_oneHundredTwentyEightDV_151330161165161270721454284880,
    phi_oneHundredTwentyEightDV_151330161165161270721454284881, phi_oneHundredTwentyEightDV_151330161165161270721454284882, phi_oneHundredTwentyEightDV_151330161165161270721454284883,
    phi_oneHundredTwentyEightDV_151330161165161270721454284884, phi_oneHundredTwentyEightDV_151330161165161270721454284885, phi_oneHundredTwentyEightDV_151330161165161270721454284886,
    phi_oneHundredTwentyEightDV_151330161165161270721454284887, phi_oneHundredTwentyEightDV_151330161165161270721454284888, phi_oneHundredTwentyEightDV_151330161165161270721454284889,
    phi_oneHundredTwentyEightDV_151330161165161270721454284890, phi_oneHundredTwentyEightDV_151330161165161270721454284891, phi_oneHundredTwentyEightDV_151330161165161270721454284892,
    phi_oneHundredTwentyEightDV_151330161165161270721454284893, phi_oneHundredTwentyEightDV_151330161165161270721454284894, phi_oneHundredTwentyEightDV_151330161165161270721454284895,
    phi_oneHundredTwentyEightDV_151330161165161270721454284896, phi_oneHundredTwentyEightDV_151330161165161270721454284897, phi_oneHundredTwentyEightDV_151330161165161270721454284898,
    phi_oneHundredTwentyEightDV_151330161165161270721454284899, phi_oneHundredTwentyEightDV_151330161165161270721454284900, phi_oneHundredTwentyEightDV_151330161165161270721454284901]

end TotientTailPeriodKiller
end Erdos249257
