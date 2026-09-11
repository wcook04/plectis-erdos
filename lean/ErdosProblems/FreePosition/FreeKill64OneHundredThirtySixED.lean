import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredThirtySixEDFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredThirtySixEDFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredThirtySixEDFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredThirtySixEDFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredThirtySixEDFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredThirtySixEDFastPow a n * oneHundredThirtySixEDFastPow a n * a else oneHundredThirtySixEDFastPow a n * oneHundredThirtySixEDFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredThirtySixED_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredThirtySixED_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredThirtySixED_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredThirtySixED_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredThirtySixED_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredThirtySixED_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredThirtySixED_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredThirtySixED_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredThirtySixED_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredThirtySixED_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredThirtySixED_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredThirtySixED_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredThirtySixED_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredThirtySixED_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredThirtySixED_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredThirtySixED_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredThirtySixED_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredThirtySixED_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredThirtySixED_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredThirtySixED_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredThirtySixED_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredThirtySixED_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredThirtySixED_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredThirtySixED_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredThirtySixED_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredThirtySixED_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredThirtySixED_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredThirtySixED_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredThirtySixED_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredThirtySixED_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredThirtySixED_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredThirtySixED_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredThirtySixED_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredThirtySixED_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredThirtySixED_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredThirtySixED_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredThirtySixED_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredThirtySixED_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredThirtySixED_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredThirtySixED_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredThirtySixED_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredThirtySixED_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredThirtySixED_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredThirtySixED_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredThirtySixED_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredThirtySixED_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredThirtySixED_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredThirtySixED_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredThirtySixED_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredThirtySixED_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredThirtySixED_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredThirtySixED_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredThirtySixED_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredThirtySixED_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredThirtySixED_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredThirtySixED_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredThirtySixED_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredThirtySixED_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredThirtySixED_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredThirtySixED_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredThirtySixED_331 : Nat.Prime 331 := by norm_num

private theorem prime_oneHundredThirtySixED_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredThirtySixED_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredThirtySixED_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredThirtySixED_359 : Nat.Prime 359 := by norm_num

private theorem prime_oneHundredThirtySixED_373 : Nat.Prime 373 := by norm_num

private theorem prime_oneHundredThirtySixED_379 : Nat.Prime 379 := by norm_num

private theorem prime_oneHundredThirtySixED_389 : Nat.Prime 389 := by norm_num

private theorem prime_oneHundredThirtySixED_397 : Nat.Prime 397 := by norm_num

private theorem prime_oneHundredThirtySixED_419 : Nat.Prime 419 := by norm_num

private theorem prime_oneHundredThirtySixED_457 : Nat.Prime 457 := by norm_num

private theorem prime_oneHundredThirtySixED_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredThirtySixED_463 : Nat.Prime 463 := by norm_num

private theorem prime_oneHundredThirtySixED_467 : Nat.Prime 467 := by norm_num

private theorem prime_oneHundredThirtySixED_479 : Nat.Prime 479 := by norm_num

private theorem prime_oneHundredThirtySixED_509 : Nat.Prime 509 := by norm_num

private theorem prime_oneHundredThirtySixED_541 : Nat.Prime 541 := by norm_num

private theorem prime_oneHundredThirtySixED_547 : Nat.Prime 547 := by norm_num

private theorem prime_oneHundredThirtySixED_557 : Nat.Prime 557 := by norm_num

private theorem prime_oneHundredThirtySixED_569 : Nat.Prime 569 := by norm_num

private theorem prime_oneHundredThirtySixED_577 : Nat.Prime 577 := by norm_num

private theorem prime_oneHundredThirtySixED_587 : Nat.Prime 587 := by norm_num

private theorem prime_oneHundredThirtySixED_593 : Nat.Prime 593 := by norm_num

private theorem prime_oneHundredThirtySixED_599 : Nat.Prime 599 := by norm_num

private theorem prime_oneHundredThirtySixED_601 : Nat.Prime 601 := by norm_num

private theorem prime_oneHundredThirtySixED_613 : Nat.Prime 613 := by norm_num

private theorem prime_oneHundredThirtySixED_631 : Nat.Prime 631 := by norm_num

private theorem prime_oneHundredThirtySixED_673 : Nat.Prime 673 := by norm_num

private theorem prime_oneHundredThirtySixED_683 : Nat.Prime 683 := by norm_num

private theorem prime_oneHundredThirtySixED_727 : Nat.Prime 727 := by norm_num

private theorem prime_oneHundredThirtySixED_733 : Nat.Prime 733 := by norm_num

private theorem prime_oneHundredThirtySixED_751 : Nat.Prime 751 := by norm_num

private theorem prime_oneHundredThirtySixED_853 : Nat.Prime 853 := by norm_num

private theorem prime_oneHundredThirtySixED_857 : Nat.Prime 857 := by norm_num

private theorem prime_oneHundredThirtySixED_919 : Nat.Prime 919 := by norm_num

private theorem prime_oneHundredThirtySixED_929 : Nat.Prime 929 := by norm_num

private theorem prime_oneHundredThirtySixED_937 : Nat.Prime 937 := by norm_num

private theorem prime_oneHundredThirtySixED_941 : Nat.Prime 941 := by norm_num

private theorem prime_oneHundredThirtySixED_947 : Nat.Prime 947 := by norm_num

private theorem prime_oneHundredThirtySixED_971 : Nat.Prime 971 := by norm_num

private theorem prime_oneHundredThirtySixED_1009 : Nat.Prime 1009 := by norm_num

private theorem prime_oneHundredThirtySixED_1031 : Nat.Prime 1031 := by norm_num

private theorem prime_oneHundredThirtySixED_1063 : Nat.Prime 1063 := by norm_num

private theorem prime_oneHundredThirtySixED_1091 : Nat.Prime 1091 := by norm_num

private theorem prime_oneHundredThirtySixED_1117 : Nat.Prime 1117 := by norm_num

private theorem prime_oneHundredThirtySixED_1129 : Nat.Prime 1129 := by norm_num

private theorem prime_oneHundredThirtySixED_1153 : Nat.Prime 1153 := by norm_num

private theorem prime_oneHundredThirtySixED_1217 : Nat.Prime 1217 := by norm_num

private theorem prime_oneHundredThirtySixED_1289 : Nat.Prime 1289 := by norm_num

private theorem prime_oneHundredThirtySixED_1301 : Nat.Prime 1301 := by norm_num

private theorem prime_oneHundredThirtySixED_1319 : Nat.Prime 1319 := by norm_num

private theorem prime_oneHundredThirtySixED_1367 : Nat.Prime 1367 := by norm_num

private theorem prime_oneHundredThirtySixED_1373 : Nat.Prime 1373 := by norm_num

private theorem prime_oneHundredThirtySixED_1409 : Nat.Prime 1409 := by norm_num

private theorem prime_oneHundredThirtySixED_1427 : Nat.Prime 1427 := by norm_num

private theorem prime_oneHundredThirtySixED_1447 : Nat.Prime 1447 := by norm_num

private theorem prime_oneHundredThirtySixED_1451 : Nat.Prime 1451 := by norm_num

private theorem prime_oneHundredThirtySixED_1459 : Nat.Prime 1459 := by norm_num

private theorem prime_oneHundredThirtySixED_1471 : Nat.Prime 1471 := by norm_num

private theorem prime_oneHundredThirtySixED_1481 : Nat.Prime 1481 := by norm_num

private theorem prime_oneHundredThirtySixED_1531 : Nat.Prime 1531 := by norm_num

private theorem prime_oneHundredThirtySixED_1571 : Nat.Prime 1571 := by norm_num

private theorem prime_oneHundredThirtySixED_1607 : Nat.Prime 1607 := by norm_num

private theorem prime_oneHundredThirtySixED_1613 : Nat.Prime 1613 := by norm_num

private theorem prime_oneHundredThirtySixED_1621 : Nat.Prime 1621 := by norm_num

private theorem prime_oneHundredThirtySixED_1667 : Nat.Prime 1667 := by norm_num

private theorem prime_oneHundredThirtySixED_1669 : Nat.Prime 1669 := by norm_num

private theorem prime_oneHundredThirtySixED_1693 : Nat.Prime 1693 := by norm_num

private theorem prime_oneHundredThirtySixED_1733 : Nat.Prime 1733 := by norm_num

private theorem prime_oneHundredThirtySixED_1741 : Nat.Prime 1741 := by norm_num

private theorem prime_oneHundredThirtySixED_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_oneHundredThirtySixED_1823 : Nat.Prime 1823 := by norm_num

private theorem prime_oneHundredThirtySixED_1831 : Nat.Prime 1831 := by norm_num

private theorem prime_oneHundredThirtySixED_1847 : Nat.Prime 1847 := by norm_num

private theorem prime_oneHundredThirtySixED_1867 : Nat.Prime 1867 := by norm_num

private theorem prime_oneHundredThirtySixED_1877 : Nat.Prime 1877 := by norm_num

private theorem prime_oneHundredThirtySixED_1933 : Nat.Prime 1933 := by norm_num

private theorem prime_oneHundredThirtySixED_1993 : Nat.Prime 1993 := by norm_num

private theorem prime_oneHundredThirtySixED_2063 : Nat.Prime 2063 := by norm_num

private theorem prime_oneHundredThirtySixED_2143 : Nat.Prime 2143 := by norm_num

private theorem prime_oneHundredThirtySixED_2203 : Nat.Prime 2203 := by norm_num

private theorem prime_oneHundredThirtySixED_2237 : Nat.Prime 2237 := by norm_num

private theorem prime_oneHundredThirtySixED_2297 : Nat.Prime 2297 := by norm_num

private theorem prime_oneHundredThirtySixED_2311 : Nat.Prime 2311 := by norm_num

private theorem prime_oneHundredThirtySixED_2351 : Nat.Prime 2351 := by norm_num

private theorem prime_oneHundredThirtySixED_2437 : Nat.Prime 2437 := by norm_num

private theorem prime_oneHundredThirtySixED_2441 : Nat.Prime 2441 := by norm_num

private theorem prime_oneHundredThirtySixED_2447 : Nat.Prime 2447 := by norm_num

private theorem prime_oneHundredThirtySixED_2647 : Nat.Prime 2647 := by norm_num

private theorem prime_oneHundredThirtySixED_2741 : Nat.Prime 2741 := by norm_num

private theorem prime_oneHundredThirtySixED_2819 : Nat.Prime 2819 := by norm_num

private theorem prime_oneHundredThirtySixED_2857 : Nat.Prime 2857 := by norm_num

private theorem prime_oneHundredThirtySixED_2903 : Nat.Prime 2903 := by norm_num

private theorem prime_oneHundredThirtySixED_3049 : Nat.Prime 3049 := by norm_num

private theorem prime_oneHundredThirtySixED_3079 : Nat.Prime 3079 := by norm_num

private theorem prime_oneHundredThirtySixED_3089 : Nat.Prime 3089 := by norm_num

private theorem prime_oneHundredThirtySixED_3229 : Nat.Prime 3229 := by norm_num

private theorem prime_oneHundredThirtySixED_3253 : Nat.Prime 3253 := by norm_num

private theorem prime_oneHundredThirtySixED_3323 : Nat.Prime 3323 := by norm_num

private theorem prime_oneHundredThirtySixED_3391 : Nat.Prime 3391 := by norm_num

private theorem prime_oneHundredThirtySixED_3581 : Nat.Prime 3581 := by norm_num

private theorem prime_oneHundredThirtySixED_3607 : Nat.Prime 3607 := by norm_num

private theorem prime_oneHundredThirtySixED_3691 : Nat.Prime 3691 := by norm_num

private theorem prime_oneHundredThirtySixED_3727 : Nat.Prime 3727 := by norm_num

private theorem prime_oneHundredThirtySixED_3847 : Nat.Prime 3847 := by norm_num

private theorem prime_oneHundredThirtySixED_3923 : Nat.Prime 3923 := by norm_num

private theorem prime_oneHundredThirtySixED_4093 : Nat.Prime 4093 := by norm_num

private theorem prime_oneHundredThirtySixED_4177 : Nat.Prime 4177 := by norm_num

private theorem prime_oneHundredThirtySixED_4217 : Nat.Prime 4217 := by norm_num

private theorem prime_oneHundredThirtySixED_4423 : Nat.Prime 4423 := by norm_num

private theorem prime_oneHundredThirtySixED_4493 : Nat.Prime 4493 := by norm_num

private theorem prime_oneHundredThirtySixED_4507 : Nat.Prime 4507 := by norm_num

private theorem prime_oneHundredThirtySixED_4597 : Nat.Prime 4597 := by norm_num

private theorem prime_oneHundredThirtySixED_4603 : Nat.Prime 4603 := by norm_num

private theorem prime_oneHundredThirtySixED_4637 : Nat.Prime 4637 := by norm_num

private theorem prime_oneHundredThirtySixED_4871 : Nat.Prime 4871 := by norm_num

private theorem prime_oneHundredThirtySixED_5023 : Nat.Prime 5023 := by norm_num

private theorem prime_oneHundredThirtySixED_5153 : Nat.Prime 5153 := by norm_num

private theorem prime_oneHundredThirtySixED_5651 : Nat.Prime 5651 := by norm_num

private theorem prime_oneHundredThirtySixED_5693 : Nat.Prime 5693 := by norm_num

private theorem prime_oneHundredThirtySixED_5827 : Nat.Prime 5827 := by norm_num

private theorem prime_oneHundredThirtySixED_6143 : Nat.Prime 6143 := by norm_num

private theorem prime_oneHundredThirtySixED_6521 : Nat.Prime 6521 := by norm_num

private theorem prime_oneHundredThirtySixED_6689 : Nat.Prime 6689 := by norm_num

private theorem prime_oneHundredThirtySixED_6793 : Nat.Prime 6793 := by norm_num

private theorem prime_oneHundredThirtySixED_6803 : Nat.Prime 6803 := by norm_num

private theorem prime_oneHundredThirtySixED_6959 : Nat.Prime 6959 := by norm_num

private theorem prime_oneHundredThirtySixED_7211 : Nat.Prime 7211 := by norm_num

private theorem prime_oneHundredThirtySixED_7213 : Nat.Prime 7213 := by norm_num

private theorem prime_oneHundredThirtySixED_7477 : Nat.Prime 7477 := by norm_num

private theorem prime_oneHundredThirtySixED_7559 : Nat.Prime 7559 := by norm_num

private theorem prime_oneHundredThirtySixED_7561 : Nat.Prime 7561 := by norm_num

private theorem prime_oneHundredThirtySixED_7727 : Nat.Prime 7727 := by norm_num

private theorem prime_oneHundredThirtySixED_7867 : Nat.Prime 7867 := by norm_num

private theorem prime_oneHundredThirtySixED_7949 : Nat.Prime 7949 := by norm_num

private theorem prime_oneHundredThirtySixED_7993 : Nat.Prime 7993 := by norm_num

private theorem prime_oneHundredThirtySixED_8191 : Nat.Prime 8191 := by norm_num

private theorem prime_oneHundredThirtySixED_8273 : Nat.Prime 8273 := by norm_num

private theorem prime_oneHundredThirtySixED_8423 : Nat.Prime 8423 := by norm_num

private theorem prime_oneHundredThirtySixED_8431 : Nat.Prime 8431 := by norm_num

private theorem prime_oneHundredThirtySixED_8761 : Nat.Prime 8761 := by norm_num

private theorem prime_oneHundredThirtySixED_8779 : Nat.Prime 8779 := by norm_num

private theorem prime_oneHundredThirtySixED_9491 : Nat.Prime 9491 := by norm_num

private theorem prime_oneHundredThirtySixED_9833 : Nat.Prime 9833 := by norm_num

private theorem prime_oneHundredThirtySixED_10321 : Nat.Prime 10321 := by norm_num

private theorem prime_oneHundredThirtySixED_10559 : Nat.Prime 10559 := by norm_num

private theorem prime_oneHundredThirtySixED_10613 : Nat.Prime 10613 := by norm_num

private theorem prime_oneHundredThirtySixED_10789 : Nat.Prime 10789 := by norm_num

private theorem prime_oneHundredThirtySixED_10853 : Nat.Prime 10853 := by norm_num

private theorem prime_oneHundredThirtySixED_11113 : Nat.Prime 11113 := by norm_num

private theorem prime_oneHundredThirtySixED_11399 : Nat.Prime 11399 := by norm_num

private theorem prime_oneHundredThirtySixED_11551 : Nat.Prime 11551 := by norm_num

private theorem prime_oneHundredThirtySixED_11701 : Nat.Prime 11701 := by norm_num

private theorem prime_oneHundredThirtySixED_11821 : Nat.Prime 11821 := by norm_num

private theorem prime_oneHundredThirtySixED_11903 : Nat.Prime 11903 := by norm_num

private theorem prime_oneHundredThirtySixED_12251 : Nat.Prime 12251 := by norm_num

private theorem prime_oneHundredThirtySixED_12577 : Nat.Prime 12577 := by norm_num

private theorem prime_oneHundredThirtySixED_12583 : Nat.Prime 12583 := by norm_num

private theorem prime_oneHundredThirtySixED_12889 : Nat.Prime 12889 := by norm_num

private theorem prime_oneHundredThirtySixED_12899 : Nat.Prime 12899 := by norm_num

private theorem prime_oneHundredThirtySixED_12959 : Nat.Prime 12959 := by norm_num

private theorem prime_oneHundredThirtySixED_13099 : Nat.Prime 13099 := by norm_num

private theorem prime_oneHundredThirtySixED_13619 : Nat.Prime 13619 := by norm_num

private theorem prime_oneHundredThirtySixED_13997 : Nat.Prime 13997 := by norm_num

private theorem prime_oneHundredThirtySixED_14221 : Nat.Prime 14221 := by norm_num

private theorem prime_oneHundredThirtySixED_14437 : Nat.Prime 14437 := by norm_num

private theorem prime_oneHundredThirtySixED_15319 : Nat.Prime 15319 := by norm_num

private theorem prime_oneHundredThirtySixED_15739 : Nat.Prime 15739 := by norm_num

private theorem prime_oneHundredThirtySixED_15773 : Nat.Prime 15773 := by norm_num

private theorem prime_oneHundredThirtySixED_15803 : Nat.Prime 15803 := by norm_num

private theorem prime_oneHundredThirtySixED_15887 : Nat.Prime 15887 := by norm_num

private theorem prime_oneHundredThirtySixED_16493 : Nat.Prime 16493 := by norm_num

private theorem prime_oneHundredThirtySixED_16981 : Nat.Prime 16981 := by norm_num

private theorem prime_oneHundredThirtySixED_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredThirtySixED_18371 : Nat.Prime 18371 := by norm_num

private theorem prime_oneHundredThirtySixED_19219 : Nat.Prime 19219 := by norm_num

private theorem prime_oneHundredThirtySixED_19387 : Nat.Prime 19387 := by norm_num

private theorem prime_oneHundredThirtySixED_19927 : Nat.Prime 19927 := by norm_num

private theorem prime_oneHundredThirtySixED_20107 : Nat.Prime 20107 := by norm_num

private theorem prime_oneHundredThirtySixED_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredThirtySixED_20771 : Nat.Prime 20771 := by norm_num

private theorem prime_oneHundredThirtySixED_21067 : Nat.Prime 21067 := by norm_num

private theorem prime_oneHundredThirtySixED_21377 : Nat.Prime 21377 := by norm_num

private theorem prime_oneHundredThirtySixED_21911 : Nat.Prime 21911 := by norm_num

private theorem prime_oneHundredThirtySixED_23063 : Nat.Prime 23063 := by norm_num

private theorem prime_oneHundredThirtySixED_23269 : Nat.Prime 23269 := by norm_num

private theorem prime_oneHundredThirtySixED_24239 : Nat.Prime 24239 := by norm_num

private theorem prime_oneHundredThirtySixED_24551 : Nat.Prime 24551 := by norm_num

private theorem prime_oneHundredThirtySixED_24709 : Nat.Prime 24709 := by norm_num

private theorem prime_oneHundredThirtySixED_24841 : Nat.Prime 24841 := by norm_num

private theorem prime_oneHundredThirtySixED_24877 : Nat.Prime 24877 := by norm_num

private theorem prime_oneHundredThirtySixED_25603 : Nat.Prime 25603 := by norm_num

private theorem prime_oneHundredThirtySixED_28393 : Nat.Prime 28393 := by norm_num

private theorem prime_oneHundredThirtySixED_28591 : Nat.Prime 28591 := by norm_num

private theorem prime_oneHundredThirtySixED_28607 : Nat.Prime 28607 := by norm_num

private theorem prime_oneHundredThirtySixED_28807 : Nat.Prime 28807 := by norm_num

private theorem prime_oneHundredThirtySixED_29123 : Nat.Prime 29123 := by norm_num

private theorem prime_oneHundredThirtySixED_30013 : Nat.Prime 30013 := by norm_num

private theorem prime_oneHundredThirtySixED_30557 : Nat.Prime 30557 := by norm_num

private theorem prime_oneHundredThirtySixED_32233 : Nat.Prime 32233 := by norm_num

private theorem prime_oneHundredThirtySixED_32303 : Nat.Prime 32303 := by norm_num

private theorem prime_oneHundredThirtySixED_33289 : Nat.Prime 33289 := by norm_num

private theorem prime_oneHundredThirtySixED_33941 : Nat.Prime 33941 := by norm_num

private theorem prime_oneHundredThirtySixED_37201 : Nat.Prime 37201 := by norm_num

private theorem prime_oneHundredThirtySixED_38393 : Nat.Prime 38393 := by norm_num

private theorem prime_oneHundredThirtySixED_40433 : Nat.Prime 40433 := by norm_num

private theorem prime_oneHundredThirtySixED_41269 : Nat.Prime 41269 := by norm_num

private theorem prime_oneHundredThirtySixED_41467 : Nat.Prime 41467 := by norm_num

private theorem prime_oneHundredThirtySixED_41999 : Nat.Prime 41999 := by norm_num

private theorem prime_oneHundredThirtySixED_42043 : Nat.Prime 42043 := by norm_num

private theorem prime_oneHundredThirtySixED_42323 : Nat.Prime 42323 := by norm_num

private theorem prime_oneHundredThirtySixED_44221 : Nat.Prime 44221 := by norm_num

private theorem prime_oneHundredThirtySixED_46727 : Nat.Prime 46727 := by norm_num

private theorem prime_oneHundredThirtySixED_46817 : Nat.Prime 46817 := by norm_num

private theorem prime_oneHundredThirtySixED_47317 : Nat.Prime 47317 := by norm_num

private theorem prime_oneHundredThirtySixED_47701 : Nat.Prime 47701 := by norm_num

private theorem prime_oneHundredThirtySixED_48017 : Nat.Prime 48017 := by norm_num

private theorem prime_oneHundredThirtySixED_48953 : Nat.Prime 48953 := by norm_num

private theorem prime_oneHundredThirtySixED_49139 : Nat.Prime 49139 := by norm_num

private theorem prime_oneHundredThirtySixED_50387 : Nat.Prime 50387 := by norm_num

private theorem prime_oneHundredThirtySixED_52363 : Nat.Prime 52363 := by norm_num

private theorem prime_oneHundredThirtySixED_57251 : Nat.Prime 57251 := by norm_num

private theorem prime_oneHundredThirtySixED_65731 : Nat.Prime 65731 := by norm_num

private theorem prime_oneHundredThirtySixED_65831 : Nat.Prime 65831 := by norm_num

private theorem prime_oneHundredThirtySixED_68903 : Nat.Prime 68903 := by norm_num

private theorem prime_oneHundredThirtySixED_69997 : Nat.Prime 69997 := by norm_num

private theorem prime_oneHundredThirtySixED_72797 : Nat.Prime 72797 := by norm_num

private theorem prime_oneHundredThirtySixED_73607 : Nat.Prime 73607 := by norm_num

private theorem prime_oneHundredThirtySixED_74219 : Nat.Prime 74219 := by norm_num

private theorem prime_oneHundredThirtySixED_77269 : Nat.Prime 77269 := by norm_num

private theorem prime_oneHundredThirtySixED_83537 : Nat.Prime 83537 := by norm_num

private theorem prime_oneHundredThirtySixED_88463 : Nat.Prime 88463 := by norm_num

private theorem prime_oneHundredThirtySixED_89597 : Nat.Prime 89597 := by norm_num

private theorem prime_oneHundredThirtySixED_89753 : Nat.Prime 89753 := by norm_num

private theorem prime_oneHundredThirtySixED_89983 : Nat.Prime 89983 := by norm_num

private theorem prime_oneHundredThirtySixED_92179 : Nat.Prime 92179 := by norm_num

private theorem prime_oneHundredThirtySixED_93089 : Nat.Prime 93089 := by norm_num

private theorem prime_oneHundredThirtySixED_104161 : Nat.Prime 104161 := by norm_num

private theorem prime_oneHundredThirtySixED_105613 : Nat.Prime 105613 := by norm_num

private theorem prime_oneHundredThirtySixED_107269 : Nat.Prime 107269 := by norm_num

private theorem prime_oneHundredThirtySixED_109987 : Nat.Prime 109987 := by norm_num

private theorem prime_oneHundredThirtySixED_115963 : Nat.Prime 115963 := by norm_num

private theorem prime_oneHundredThirtySixED_116741 : Nat.Prime 116741 := by norm_num

private theorem prime_oneHundredThirtySixED_132173 : Nat.Prime 132173 := by norm_num

private theorem prime_oneHundredThirtySixED_145969 : Nat.Prime 145969 := by norm_num

private theorem prime_oneHundredThirtySixED_147299 : Nat.Prime 147299 := by norm_num

private theorem prime_oneHundredThirtySixED_157243 : Nat.Prime 157243 := by norm_num

private theorem prime_oneHundredThirtySixED_164987 : Nat.Prime 164987 := by norm_num

private theorem prime_oneHundredThirtySixED_169733 : Nat.Prime 169733 := by norm_num

private theorem prime_oneHundredThirtySixED_170603 : Nat.Prime 170603 := by norm_num

private theorem prime_oneHundredThirtySixED_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredThirtySixED_183299 : Nat.Prime 183299 := by norm_num

private theorem prime_oneHundredThirtySixED_189257 : Nat.Prime 189257 := by norm_num

private theorem prime_oneHundredThirtySixED_192887 : Nat.Prime 192887 := by norm_num

private theorem prime_oneHundredThirtySixED_198073 : Nat.Prime 198073 := by norm_num

private theorem prime_oneHundredThirtySixED_199151 : Nat.Prime 199151 := by norm_num

private theorem prime_oneHundredThirtySixED_202121 : Nat.Prime 202121 := by norm_num

private theorem prime_oneHundredThirtySixED_226001 : Nat.Prime 226001 := by norm_num

private theorem prime_oneHundredThirtySixED_227081 : Nat.Prime 227081 := by norm_num

private theorem prime_oneHundredThirtySixED_244603 : Nat.Prime 244603 := by norm_num

private theorem prime_oneHundredThirtySixED_245299 : Nat.Prime 245299 := by norm_num

private theorem prime_oneHundredThirtySixED_254729 : Nat.Prime 254729 := by norm_num

private theorem prime_oneHundredThirtySixED_276917 : Nat.Prime 276917 := by norm_num

private theorem prime_oneHundredThirtySixED_297263 : Nat.Prime 297263 := by norm_num

private theorem prime_oneHundredThirtySixED_307969 : Nat.Prime 307969 := by norm_num

private theorem prime_oneHundredThirtySixED_328519 : Nat.Prime 328519 := by norm_num

private theorem prime_oneHundredThirtySixED_362027 : Nat.Prime 362027 := by norm_num

private theorem prime_oneHundredThirtySixED_389797 : Nat.Prime 389797 := by norm_num

private theorem prime_oneHundredThirtySixED_423209 : Nat.Prime 423209 := by norm_num

private theorem prime_oneHundredThirtySixED_425489 : Nat.Prime 425489 := by norm_num

private theorem prime_oneHundredThirtySixED_450301 : Nat.Prime 450301 := by norm_num

private theorem prime_oneHundredThirtySixED_482323 : Nat.Prime 482323 := by norm_num

private theorem prime_oneHundredThirtySixED_486329 : Nat.Prime 486329 := by norm_num

private theorem prime_oneHundredThirtySixED_529003 : Nat.Prime 529003 := by norm_num

private theorem prime_oneHundredThirtySixED_538553 : Nat.Prime 538553 := by norm_num

private theorem prime_oneHundredThirtySixED_546151 : Nat.Prime 546151 := by norm_num

private theorem prime_oneHundredThirtySixED_549019 : Nat.Prime 549019 := by norm_num

private theorem prime_oneHundredThirtySixED_591131 : Nat.Prime 591131 := by norm_num

private theorem prime_oneHundredThirtySixED_610553 : Nat.Prime 610553 := by norm_num

private theorem prime_oneHundredThirtySixED_613297 : Nat.Prime 613297 := by norm_num

private theorem prime_oneHundredThirtySixED_614279 : Nat.Prime 614279 := by norm_num

private theorem prime_oneHundredThirtySixED_646157 : Nat.Prime 646157 := by norm_num

private theorem prime_oneHundredThirtySixED_647477 : Nat.Prime 647477 := by norm_num

private theorem prime_oneHundredThirtySixED_649217 : Nat.Prime 649217 := by norm_num

private theorem prime_oneHundredThirtySixED_657491 : Nat.Prime 657491 := by norm_num

private theorem prime_oneHundredThirtySixED_659609 : Nat.Prime 659609 := by norm_num

private theorem prime_oneHundredThirtySixED_669679 : Nat.Prime 669679 := by norm_num

private theorem prime_oneHundredThirtySixED_698249 : Nat.Prime 698249 := by norm_num

private theorem prime_oneHundredThirtySixED_705461 : Nat.Prime 705461 := by norm_num

private theorem prime_oneHundredThirtySixED_723413 : Nat.Prime 723413 := by norm_num

private theorem prime_oneHundredThirtySixED_743143 : Nat.Prime 743143 := by norm_num

private theorem prime_oneHundredThirtySixED_813677 : Nat.Prime 813677 := by norm_num

private theorem prime_oneHundredThirtySixED_879169 : Nat.Prime 879169 := by norm_num

private theorem prime_oneHundredThirtySixED_920783 : Nat.Prime 920783 := by norm_num

private theorem prime_oneHundredThirtySixED_1094963 : Nat.Prime 1094963 := by norm_num

private theorem prime_oneHundredThirtySixED_1131479 : Nat.Prime 1131479 := by norm_num

private theorem prime_oneHundredThirtySixED_1222693 : Nat.Prime 1222693 := by norm_num

private theorem prime_oneHundredThirtySixED_1232083 : Nat.Prime 1232083 := by norm_num

private theorem prime_oneHundredThirtySixED_1237619 : Nat.Prime 1237619 := by norm_num

private theorem prime_oneHundredThirtySixED_1252439 : Nat.Prime 1252439 := by norm_num

private theorem prime_oneHundredThirtySixED_1264873 : Nat.Prime 1264873 := by norm_num

private theorem prime_oneHundredThirtySixED_1295717 : Nat.Prime 1295717 := by norm_num

private theorem prime_oneHundredThirtySixED_1360213 : Nat.Prime 1360213 := by norm_num

private theorem prime_oneHundredThirtySixED_1418689 : Nat.Prime 1418689 := by norm_num

private theorem prime_oneHundredThirtySixED_1457389 : Nat.Prime 1457389 := by norm_num

private theorem prime_oneHundredThirtySixED_1509407 : Nat.Prime 1509407 := by norm_num

private theorem prime_oneHundredThirtySixED_1521103 : Nat.Prime 1521103 := by norm_num

private theorem prime_oneHundredThirtySixED_1537099 : Nat.Prime 1537099 := by norm_num

private theorem prime_oneHundredThirtySixED_1542239 : Nat.Prime 1542239 := by norm_num

private theorem prime_oneHundredThirtySixED_1616609 : Nat.Prime 1616609 := by norm_num

private theorem prime_oneHundredThirtySixED_1633067 : Nat.Prime 1633067 := by norm_num

private theorem prime_oneHundredThirtySixED_1681639 : Nat.Prime 1681639 := by norm_num

private theorem prime_oneHundredThirtySixED_1693987 : Nat.Prime 1693987 := by norm_num

private theorem prime_oneHundredThirtySixED_1705861 : Nat.Prime 1705861 := by norm_num

private theorem prime_oneHundredThirtySixED_1707067 : Nat.Prime 1707067 := by norm_num

private theorem prime_oneHundredThirtySixED_1736981 : Nat.Prime 1736981 := by norm_num

private theorem prime_oneHundredThirtySixED_1851541 : Nat.Prime 1851541 := by norm_num

private theorem prime_oneHundredThirtySixED_1882147 : Nat.Prime 1882147 := by norm_num

private theorem prime_oneHundredThirtySixED_1904681 : Nat.Prime 1904681 := by norm_num

private theorem prime_oneHundredThirtySixED_1918991 : Nat.Prime 1918991 := by norm_num

private theorem prime_oneHundredThirtySixED_2341567 : Nat.Prime 2341567 := by norm_num

private theorem prime_oneHundredThirtySixED_2341907 : Nat.Prime 2341907 := by norm_num

private theorem prime_oneHundredThirtySixED_2608211 : Nat.Prime 2608211 := by norm_num

private theorem prime_oneHundredThirtySixED_2717291 : Nat.Prime 2717291 := by norm_num

private theorem prime_oneHundredThirtySixED_2755243 : Nat.Prime 2755243 := by norm_num

private theorem prime_oneHundredThirtySixED_2837017 : Nat.Prime 2837017 := by norm_num

private theorem prime_oneHundredThirtySixED_2888569 : Nat.Prime 2888569 := by norm_num

private theorem prime_oneHundredThirtySixED_2905783 : Nat.Prime 2905783 := by norm_num

private theorem prime_oneHundredThirtySixED_3043321 : Nat.Prime 3043321 := by norm_num

private theorem prime_oneHundredThirtySixED_3150547 : Nat.Prime 3150547 := by norm_num

private theorem prime_oneHundredThirtySixED_3162499 : Nat.Prime 3162499 := by norm_num

private theorem prime_oneHundredThirtySixED_3304607 : Nat.Prime 3304607 := by norm_num

private theorem prime_oneHundredThirtySixED_3578837 : Nat.Prime 3578837 := by norm_num

private theorem prime_oneHundredThirtySixED_3594403 : Nat.Prime 3594403 := by norm_num

private theorem prime_oneHundredThirtySixED_3677579 : Nat.Prime 3677579 := by norm_num

private theorem prime_oneHundredThirtySixED_3683179 : Nat.Prime 3683179 := by norm_num

private theorem prime_oneHundredThirtySixED_3857267 : Nat.Prime 3857267 := by norm_num

private theorem prime_oneHundredThirtySixED_3932503 : Nat.Prime 3932503 := by norm_num

private theorem prime_oneHundredThirtySixED_4176307 : Nat.Prime 4176307 := by norm_num

private theorem prime_oneHundredThirtySixED_4293637 : Nat.Prime 4293637 := by norm_num

private theorem prime_oneHundredThirtySixED_4440187 : Nat.Prime 4440187 := by norm_num

private theorem prime_oneHundredThirtySixED_4556173 : Nat.Prime 4556173 := by norm_num

private theorem prime_oneHundredThirtySixED_4597027 : Nat.Prime 4597027 := by norm_num

private theorem prime_oneHundredThirtySixED_5034721 : Nat.Prime 5034721 := by norm_num

private theorem prime_oneHundredThirtySixED_5066881 : Nat.Prime 5066881 := by norm_num

private theorem prime_oneHundredThirtySixED_5225309 : Nat.Prime 5225309 := by norm_num

private theorem prime_oneHundredThirtySixED_5463023 : Nat.Prime 5463023 := by norm_num

private theorem prime_oneHundredThirtySixED_5491039 : Nat.Prime 5491039 := by norm_num

private theorem prime_oneHundredThirtySixED_5776831 : Nat.Prime 5776831 := by norm_num

private theorem prime_oneHundredThirtySixED_5990311 : Nat.Prime 5990311 := by norm_num

private theorem prime_oneHundredThirtySixED_6202103 : Nat.Prime 6202103 := by norm_num

private theorem prime_oneHundredThirtySixED_6631661 : Nat.Prime 6631661 := by norm_num

private theorem prime_oneHundredThirtySixED_6997457 : Nat.Prime 6997457 := by norm_num

private theorem prime_oneHundredThirtySixED_7176047 : Nat.Prime 7176047 := by norm_num

private theorem prime_oneHundredThirtySixED_7226909 : Nat.Prime 7226909 := by norm_num

private theorem prime_oneHundredThirtySixED_7333591 : Nat.Prime 7333591 := by norm_num

private theorem prime_oneHundredThirtySixED_7756669 : Nat.Prime 7756669 := by norm_num

private theorem prime_oneHundredThirtySixED_8165867 : Nat.Prime 8165867 := by norm_num

private theorem prime_oneHundredThirtySixED_8508553 : Nat.Prime 8508553 := by norm_num

private theorem prime_oneHundredThirtySixED_8590501 : Nat.Prime 8590501 := by norm_num

private theorem prime_oneHundredThirtySixED_8919023 : Nat.Prime 8919023 := by norm_num

private theorem prime_oneHundredThirtySixED_9046459 : Nat.Prime 9046459 := by norm_num

private theorem prime_oneHundredThirtySixED_9392827 : Nat.Prime 9392827 := by norm_num

private theorem prime_oneHundredThirtySixED_9704423 : Nat.Prime 9704423 := by norm_num

private theorem prime_oneHundredThirtySixED_10003657 : Nat.Prime 10003657 := by norm_num

private theorem prime_oneHundredThirtySixED_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredThirtySixED_10978711 : Nat.Prime 10978711 := by norm_num

private theorem prime_oneHundredThirtySixED_11297551 : Nat.Prime 11297551 := by norm_num

private theorem prime_oneHundredThirtySixED_11530921 : Nat.Prime 11530921 := by norm_num

private theorem prime_oneHundredThirtySixED_15266233 : Nat.Prime 15266233 := by norm_num

private theorem prime_oneHundredThirtySixED_15842081 : Nat.Prime 15842081 := by norm_num

private theorem prime_oneHundredThirtySixED_17939899 : Nat.Prime 17939899 := by norm_num

private theorem prime_oneHundredThirtySixED_18072797 : Nat.Prime 18072797 := by norm_num

private theorem prime_oneHundredThirtySixED_18725587 : Nat.Prime 18725587 := by norm_num

private theorem prime_oneHundredThirtySixED_18777053 : Nat.Prime 18777053 := by norm_num

private theorem prime_oneHundredThirtySixED_18852443 : Nat.Prime 18852443 := by norm_num

private theorem prime_oneHundredThirtySixED_19626767 : Nat.Prime 19626767 := by norm_num

private theorem prime_oneHundredThirtySixED_19820621 : Nat.Prime 19820621 := by norm_num

private theorem prime_oneHundredThirtySixED_20291147 : Nat.Prime 20291147 := by norm_num

private theorem prime_oneHundredThirtySixED_20700347 : Nat.Prime 20700347 := by norm_num

private theorem prime_oneHundredThirtySixED_21101293 : Nat.Prime 21101293 := by norm_num

private theorem prime_oneHundredThirtySixED_21748999 : Nat.Prime 21748999 := by norm_num

private theorem prime_oneHundredThirtySixED_22580969 : Nat.Prime 22580969 := by norm_num

private theorem prime_oneHundredThirtySixED_28392269 : Nat.Prime 28392269 := by norm_num

private theorem prime_oneHundredThirtySixED_30404323 : Nat.Prime 30404323 := by
  apply lucas_primality 30404323 (2 : ZMod 30404323)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (13, 1), (14437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (13, 1), (14437, 1)] : List FactorBlock).map factorBlockValue).prod) = 30404323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_13
      · exact prime_oneHundredThirtySixED_14437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 30404323) ^ 15202161 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 30404323) ^ 10134774 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 30404323) ^ 2338794 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 30404323) ^ 2106 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_32661341 : Nat.Prime 32661341 := by
  apply lucas_primality 32661341 (2 : ZMod 32661341)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1633067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1633067, 1)] : List FactorBlock).map factorBlockValue).prod) = 32661341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_1633067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 32661341) ^ 16330670 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 32661341) ^ 6532268 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 32661341) ^ 20 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_36456613 : Nat.Prime 36456613 := by
  apply lucas_primality 36456613 (6 : ZMod 36456613)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (107, 1), (28393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (107, 1), (28393, 1)] : List FactorBlock).map factorBlockValue).prod) = 36456613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_107
      · exact prime_oneHundredThirtySixED_28393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 36456613) ^ 18228306 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 36456613) ^ 12152204 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 36456613) ^ 340716 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 36456613) ^ 1284 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_36925099 : Nat.Prime 36925099 := by
  apply lucas_primality 36925099 (2 : ZMod 36925099)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (879169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (879169, 1)] : List FactorBlock).map factorBlockValue).prod) = 36925099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_879169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 36925099) ^ 18462549 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 36925099) ^ 12308366 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 36925099) ^ 5275014 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 36925099) ^ 42 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_38930813 : Nat.Prime 38930813 := by
  apply lucas_primality 38930813 (2 : ZMod 38930813)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (41, 1), (10321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (41, 1), (10321, 1)] : List FactorBlock).map factorBlockValue).prod) = 38930813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_23
      · exact prime_oneHundredThirtySixED_41
      · exact prime_oneHundredThirtySixED_10321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 38930813) ^ 19465406 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 38930813) ^ 1692644 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 38930813) ^ 949532 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 38930813) ^ 3772 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_40897789 : Nat.Prime 40897789 := by
  apply lucas_primality 40897789 (6 : ZMod 40897789)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (137, 1), (24877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (137, 1), (24877, 1)] : List FactorBlock).map factorBlockValue).prod) = 40897789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_137
      · exact prime_oneHundredThirtySixED_24877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 40897789) ^ 20448894 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 40897789) ^ 13632596 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 40897789) ^ 298524 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 40897789) ^ 1644 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_41482451 : Nat.Prime 41482451 := by
  apply lucas_primality 41482451 (2 : ZMod 41482451)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (359, 1), (2311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (359, 1), (2311, 1)] : List FactorBlock).map factorBlockValue).prod) = 41482451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_359
      · exact prime_oneHundredThirtySixED_2311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 41482451) ^ 20741225 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 41482451) ^ 8296490 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 41482451) ^ 115550 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 41482451) ^ 17950 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_42048707 : Nat.Prime 42048707 := by
  apply lucas_primality 42048707 (2 : ZMod 42048707)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (283, 1), (10613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (283, 1), (10613, 1)] : List FactorBlock).map factorBlockValue).prod) = 42048707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_283
      · exact prime_oneHundredThirtySixED_10613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 42048707) ^ 21024353 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 42048707) ^ 6006958 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 42048707) ^ 148582 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 42048707) ^ 3962 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_44413003 : Nat.Prime 44413003 := by
  apply lucas_primality 44413003 (2 : ZMod 44413003)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (61, 1), (97, 1), (139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (61, 1), (97, 1), (139, 1)] : List FactorBlock).map factorBlockValue).prod) = 44413003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_61
      · exact prime_oneHundredThirtySixED_97
      · exact prime_oneHundredThirtySixED_139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 44413003) ^ 22206501 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 44413003) ^ 14804334 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 44413003) ^ 728082 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 44413003) ^ 457866 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 44413003) ^ 319518 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_47582281 : Nat.Prime 47582281 := by
  apply lucas_primality 47582281 (7 : ZMod 47582281)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (132173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (132173, 1)] : List FactorBlock).map factorBlockValue).prod) = 47582281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_132173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 47582281) ^ 23791140 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 47582281) ^ 15860760 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 47582281) ^ 9516456 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 47582281) ^ 360 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_56747897 : Nat.Prime 56747897 := by
  apply lucas_primality 56747897 (3 : ZMod 56747897)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (244603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (244603, 1)] : List FactorBlock).map factorBlockValue).prod) = 56747897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_29
      · exact prime_oneHundredThirtySixED_244603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 56747897) ^ 28373948 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 56747897) ^ 1956824 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 56747897) ^ 232 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_57030289 : Nat.Prime 57030289 := by
  apply lucas_primality 57030289 (19 : ZMod 57030289)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (169733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (169733, 1)] : List FactorBlock).map factorBlockValue).prod) = 57030289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_169733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 57030289) ^ 28515144 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (19 : ZMod 57030289) ^ 19010096 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (19 : ZMod 57030289) ^ 8147184 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (19 : ZMod 57030289) ^ 336 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_59929613 : Nat.Prime 59929613 := by
  apply lucas_primality 59929613 (2 : ZMod 59929613)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) = 59929613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_1811
      · exact prime_oneHundredThirtySixED_8273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59929613) ^ 29964806 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 33092 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 7244 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_61239001 : Nat.Prime 61239001 := by
  apply lucas_primality 61239001 (17 : ZMod 61239001)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 3), (137, 1), (149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 3), (137, 1), (149, 1)] : List FactorBlock).map factorBlockValue).prod) = 61239001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_137
      · exact prime_oneHundredThirtySixED_149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 61239001) ^ 30619500 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (17 : ZMod 61239001) ^ 20413000 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (17 : ZMod 61239001) ^ 12247800 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (17 : ZMod 61239001) ^ 447000 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (17 : ZMod 61239001) ^ 411000 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_66413909 : Nat.Prime 66413909 := by
  apply lucas_primality 66413909 (2 : ZMod 66413909)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (1509407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (1509407, 1)] : List FactorBlock).map factorBlockValue).prod) = 66413909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_11
      · exact prime_oneHundredThirtySixED_1509407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 66413909) ^ 33206954 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 66413909) ^ 6037628 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 66413909) ^ 44 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_72865747 : Nat.Prime 72865747 := by
  apply lucas_primality 72865747 (3 : ZMod 72865747)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (139, 1), (29123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (139, 1), (29123, 1)] : List FactorBlock).map factorBlockValue).prod) = 72865747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_139
      · exact prime_oneHundredThirtySixED_29123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 72865747) ^ 36432873 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 72865747) ^ 24288582 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 72865747) ^ 524214 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 72865747) ^ 2502 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_79110191 : Nat.Prime 79110191 := by
  apply lucas_primality 79110191 (17 : ZMod 79110191)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (397, 1), (19927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (397, 1), (19927, 1)] : List FactorBlock).map factorBlockValue).prod) = 79110191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_397
      · exact prime_oneHundredThirtySixED_19927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 79110191) ^ 39555095 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (17 : ZMod 79110191) ^ 15822038 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (17 : ZMod 79110191) ^ 199270 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (17 : ZMod 79110191) ^ 3970 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_80242691 : Nat.Prime 80242691 := by
  apply lucas_primality 80242691 (2 : ZMod 80242691)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (419, 1), (1741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (419, 1), (1741, 1)] : List FactorBlock).map factorBlockValue).prod) = 80242691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_11
      · exact prime_oneHundredThirtySixED_419
      · exact prime_oneHundredThirtySixED_1741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 80242691) ^ 40121345 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 80242691) ^ 16048538 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 80242691) ^ 7294790 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 80242691) ^ 191510 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 80242691) ^ 46090 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_90624979 : Nat.Prime 90624979 := by
  apply lucas_primality 90624979 (2 : ZMod 90624979)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5034721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5034721, 1)] : List FactorBlock).map factorBlockValue).prod) = 90624979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_5034721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 90624979) ^ 45312489 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 90624979) ^ 30208326 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 90624979) ^ 18 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_92103133 : Nat.Prime 92103133 := by
  apply lucas_primality 92103133 (5 : ZMod 92103133)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (23, 2), (1319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (23, 2), (1319, 1)] : List FactorBlock).map factorBlockValue).prod) = 92103133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_11
      · exact prime_oneHundredThirtySixED_23
      · exact prime_oneHundredThirtySixED_1319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 92103133) ^ 46051566 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 92103133) ^ 30701044 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 92103133) ^ 8373012 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 92103133) ^ 4004484 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 92103133) ^ 69828 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_102534983 : Nat.Prime 102534983 := by
  apply lucas_primality 102534983 (5 : ZMod 102534983)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (245299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (245299, 1)] : List FactorBlock).map factorBlockValue).prod) = 102534983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_11
      · exact prime_oneHundredThirtySixED_19
      · exact prime_oneHundredThirtySixED_245299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 102534983) ^ 51267491 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 9321362 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 5396578 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 418 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_107999813 : Nat.Prime 107999813 := by
  apply lucas_primality 107999813 (2 : ZMod 107999813)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (241, 1), (4871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (241, 1), (4871, 1)] : List FactorBlock).map factorBlockValue).prod) = 107999813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_23
      · exact prime_oneHundredThirtySixED_241
      · exact prime_oneHundredThirtySixED_4871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 107999813) ^ 53999906 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 107999813) ^ 4695644 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 107999813) ^ 448132 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 107999813) ^ 22172 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_126982981 : Nat.Prime 126982981 := by
  apply lucas_primality 126982981 (2 : ZMod 126982981)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (705461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (705461, 1)] : List FactorBlock).map factorBlockValue).prod) = 126982981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_705461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 126982981) ^ 63491490 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 126982981) ^ 42327660 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 126982981) ^ 25396596 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 126982981) ^ 180 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_140647657 : Nat.Prime 140647657 := by
  apply lucas_primality 140647657 (5 : ZMod 140647657)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (37, 1), (149, 1), (1063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (37, 1), (149, 1), (1063, 1)] : List FactorBlock).map factorBlockValue).prod) = 140647657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_37
      · exact prime_oneHundredThirtySixED_149
      · exact prime_oneHundredThirtySixED_1063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 140647657) ^ 70323828 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 140647657) ^ 46882552 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 140647657) ^ 3801288 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 140647657) ^ 943944 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 140647657) ^ 132312 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_156759271 : Nat.Prime 156759271 := by
  apply lucas_primality 156759271 (6 : ZMod 156759271)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (5225309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (5225309, 1)] : List FactorBlock).map factorBlockValue).prod) = 156759271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_5225309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 156759271) ^ 78379635 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 156759271) ^ 52253090 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 156759271) ^ 31351854 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 156759271) ^ 30 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_172423187 : Nat.Prime 172423187 := by
  apply lucas_primality 172423187 (2 : ZMod 172423187)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (6631661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (6631661, 1)] : List FactorBlock).map factorBlockValue).prod) = 172423187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_13
      · exact prime_oneHundredThirtySixED_6631661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 172423187) ^ 86211593 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 172423187) ^ 13263322 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 172423187) ^ 26 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_184753553 : Nat.Prime 184753553 := by
  apply lucas_primality 184753553 (3 : ZMod 184753553)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (17, 1), (31, 1), (21911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (17, 1), (31, 1), (21911, 1)] : List FactorBlock).map factorBlockValue).prod) = 184753553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_17
      · exact prime_oneHundredThirtySixED_31
      · exact prime_oneHundredThirtySixED_21911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 184753553) ^ 92376776 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 184753553) ^ 10867856 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 184753553) ^ 5959792 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 184753553) ^ 8432 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_202274063 : Nat.Prime 202274063 := by
  apply lucas_primality 202274063 (5 : ZMod 202274063)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (613, 1), (164987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (613, 1), (164987, 1)] : List FactorBlock).map factorBlockValue).prod) = 202274063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_613
      · exact prime_oneHundredThirtySixED_164987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 202274063) ^ 101137031 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 202274063) ^ 329974 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 202274063) ^ 1226 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_212514941 : Nat.Prime 212514941 := by
  apply lucas_primality 212514941 (2 : ZMod 212514941)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (23, 1), (41999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (23, 1), (41999, 1)] : List FactorBlock).map factorBlockValue).prod) = 212514941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_11
      · exact prime_oneHundredThirtySixED_23
      · exact prime_oneHundredThirtySixED_41999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 212514941) ^ 106257470 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 212514941) ^ 42502988 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 212514941) ^ 19319540 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 212514941) ^ 9239780 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 212514941) ^ 5060 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_215578301 : Nat.Prime 215578301 := by
  apply lucas_primality 215578301 (2 : ZMod 215578301)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 1), (307969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 1), (307969, 1)] : List FactorBlock).map factorBlockValue).prod) = 215578301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_307969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 215578301) ^ 107789150 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 215578301) ^ 43115660 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 215578301) ^ 30796900 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 215578301) ^ 700 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_218739679 : Nat.Prime 218739679 := by
  apply lucas_primality 218739679 (6 : ZMod 218739679)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (36456613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (36456613, 1)] : List FactorBlock).map factorBlockValue).prod) = 218739679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_36456613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 218739679) ^ 109369839 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 218739679) ^ 72913226 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 218739679) ^ 6 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_238937473 : Nat.Prime 238937473 := by
  apply lucas_primality 238937473 (7 : ZMod 238937473)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (47, 1), (1471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (47, 1), (1471, 1)] : List FactorBlock).map factorBlockValue).prod) = 238937473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_47
      · exact prime_oneHundredThirtySixED_1471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 238937473) ^ 119468736 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 238937473) ^ 79645824 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 238937473) ^ 5083776 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 238937473) ^ 162432 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_247246991 : Nat.Prime 247246991 := by
  apply lucas_primality 247246991 (17 : ZMod 247246991)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (43, 1), (101, 1), (5693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (43, 1), (101, 1), (5693, 1)] : List FactorBlock).map factorBlockValue).prod) = 247246991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_43
      · exact prime_oneHundredThirtySixED_101
      · exact prime_oneHundredThirtySixED_5693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 247246991) ^ 123623495 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (17 : ZMod 247246991) ^ 49449398 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (17 : ZMod 247246991) ^ 5749930 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (17 : ZMod 247246991) ^ 2447990 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (17 : ZMod 247246991) ^ 43430 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_249258847 : Nat.Prime 249258847 := by
  apply lucas_primality 249258847 (3 : ZMod 249258847)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3391, 1), (12251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3391, 1), (12251, 1)] : List FactorBlock).map factorBlockValue).prod) = 249258847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_3391
      · exact prime_oneHundredThirtySixED_12251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 249258847) ^ 124629423 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 249258847) ^ 83086282 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 249258847) ^ 73506 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 249258847) ^ 20346 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_273126599 : Nat.Prime 273126599 := by
  apply lucas_primality 273126599 (7 : ZMod 273126599)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (10853, 1), (12583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (10853, 1), (12583, 1)] : List FactorBlock).map factorBlockValue).prod) = 273126599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_10853
      · exact prime_oneHundredThirtySixED_12583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 273126599) ^ 136563299 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 273126599) ^ 25166 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 273126599) ^ 21706 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_283221641 : Nat.Prime 283221641 := by
  apply lucas_primality 283221641 (3 : ZMod 283221641)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (151, 1), (3607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (151, 1), (3607, 1)] : List FactorBlock).map factorBlockValue).prod) = 283221641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_13
      · exact prime_oneHundredThirtySixED_151
      · exact prime_oneHundredThirtySixED_3607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 283221641) ^ 141610820 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 283221641) ^ 56644328 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 283221641) ^ 21786280 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 283221641) ^ 1875640 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 283221641) ^ 78520 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_285490349 : Nat.Prime 285490349 := by
  apply lucas_primality 285490349 (2 : ZMod 285490349)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (13, 2), (38393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (13, 2), (38393, 1)] : List FactorBlock).map factorBlockValue).prod) = 285490349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_11
      · exact prime_oneHundredThirtySixED_13
      · exact prime_oneHundredThirtySixED_38393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 285490349) ^ 142745174 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 285490349) ^ 25953668 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 285490349) ^ 21960796 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 285490349) ^ 7436 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_333523903 : Nat.Prime 333523903 := by
  apply lucas_primality 333523903 (3 : ZMod 333523903)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (211, 1), (463, 1), (569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (211, 1), (463, 1), (569, 1)] : List FactorBlock).map factorBlockValue).prod) = 333523903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_211
      · exact prime_oneHundredThirtySixED_463
      · exact prime_oneHundredThirtySixED_569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 333523903) ^ 166761951 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 333523903) ^ 111174634 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 333523903) ^ 1580682 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 333523903) ^ 720354 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 333523903) ^ 586158 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_395163047 : Nat.Prime 395163047 := by
  apply lucas_primality 395163047 (5 : ZMod 395163047)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (8590501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (8590501, 1)] : List FactorBlock).map factorBlockValue).prod) = 395163047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_23
      · exact prime_oneHundredThirtySixED_8590501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 395163047) ^ 197581523 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 395163047) ^ 17181002 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 395163047) ^ 46 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_431156603 : Nat.Prime 431156603 := by
  apply lucas_primality 431156603 (2 : ZMod 431156603)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (215578301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (215578301, 1)] : List FactorBlock).map factorBlockValue).prod) = 431156603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_215578301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 431156603) ^ 215578301 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 431156603) ^ 2 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_440482171 : Nat.Prime 440482171 := by
  apply lucas_primality 440482171 (2 : ZMod 440482171)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (631, 1), (23269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (631, 1), (23269, 1)] : List FactorBlock).map factorBlockValue).prod) = 440482171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_631
      · exact prime_oneHundredThirtySixED_23269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 440482171) ^ 220241085 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 440482171) ^ 146827390 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 440482171) ^ 88096434 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 440482171) ^ 698070 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 440482171) ^ 18930 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_467169757 : Nat.Prime 467169757 := by
  apply lucas_primality 467169757 (2 : ZMod 467169757)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (38930813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (38930813, 1)] : List FactorBlock).map factorBlockValue).prod) = 467169757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_38930813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 467169757) ^ 233584878 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 467169757) ^ 155723252 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 467169757) ^ 12 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_485221151 : Nat.Prime 485221151 := by
  apply lucas_primality 485221151 (7 : ZMod 485221151)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (9704423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (9704423, 1)] : List FactorBlock).map factorBlockValue).prod) = 485221151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_9704423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 485221151) ^ 242610575 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 485221151) ^ 97044230 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 485221151) ^ 50 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_515546501 : Nat.Prime 515546501 := by
  apply lucas_primality 515546501 (2 : ZMod 515546501)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 3), (7, 1), (147299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 3), (7, 1), (147299, 1)] : List FactorBlock).map factorBlockValue).prod) = 515546501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_147299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 515546501) ^ 257773250 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 515546501) ^ 103109300 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 515546501) ^ 73649500 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 515546501) ^ 3500 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_520835531 : Nat.Prime 520835531 := by
  apply lucas_primality 520835531 (2 : ZMod 520835531)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (163, 1), (173, 1), (1847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (163, 1), (173, 1), (1847, 1)] : List FactorBlock).map factorBlockValue).prod) = 520835531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_163
      · exact prime_oneHundredThirtySixED_173
      · exact prime_oneHundredThirtySixED_1847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 520835531) ^ 260417765 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 520835531) ^ 104167106 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 520835531) ^ 3195310 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 520835531) ^ 3010610 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 520835531) ^ 281990 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_541290773 : Nat.Prime 541290773 := by
  apply lucas_primality 541290773 (2 : ZMod 541290773)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (19, 1), (647477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (19, 1), (647477, 1)] : List FactorBlock).map factorBlockValue).prod) = 541290773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_11
      · exact prime_oneHundredThirtySixED_19
      · exact prime_oneHundredThirtySixED_647477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 541290773) ^ 270645386 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 541290773) ^ 49208252 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 541290773) ^ 28488988 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 541290773) ^ 836 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_661220099 : Nat.Prime 661220099 := by
  apply lucas_primality 661220099 (2 : ZMod 661220099)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (4293637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (4293637, 1)] : List FactorBlock).map factorBlockValue).prod) = 661220099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_11
      · exact prime_oneHundredThirtySixED_4293637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 661220099) ^ 330610049 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 661220099) ^ 94460014 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 661220099) ^ 60110918 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 661220099) ^ 154 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_711904799 : Nat.Prime 711904799 := by
  apply lucas_primality 711904799 (7 : ZMod 711904799)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (53, 1), (610553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (53, 1), (610553, 1)] : List FactorBlock).map factorBlockValue).prod) = 711904799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_11
      · exact prime_oneHundredThirtySixED_53
      · exact prime_oneHundredThirtySixED_610553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 711904799) ^ 355952399 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 711904799) ^ 64718618 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 711904799) ^ 13432166 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 711904799) ^ 1166 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_17203
      · exact prime_oneHundredThirtySixED_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_762655897 : Nat.Prime 762655897 := by
  apply lucas_primality 762655897 (7 : ZMod 762655897)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (19, 1), (23, 1), (24239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (19, 1), (23, 1), (24239, 1)] : List FactorBlock).map factorBlockValue).prod) = 762655897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_19
      · exact prime_oneHundredThirtySixED_23
      · exact prime_oneHundredThirtySixED_24239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 762655897) ^ 381327948 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 762655897) ^ 254218632 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 762655897) ^ 40139784 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 762655897) ^ 33158952 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 762655897) ^ 31464 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_1161395297 : Nat.Prime 1161395297 := by
  apply lucas_primality 1161395297 (3 : ZMod 1161395297)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3691, 1), (9833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3691, 1), (9833, 1)] : List FactorBlock).map factorBlockValue).prod) = 1161395297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3691
      · exact prime_oneHundredThirtySixED_9833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1161395297) ^ 580697648 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1161395297) ^ 314656 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1161395297) ^ 118112 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_1299989947 : Nat.Prime 1299989947 := by
  apply lucas_primality 1299989947 (2 : ZMod 1299989947)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (1667, 1), (5651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (1667, 1), (5651, 1)] : List FactorBlock).map factorBlockValue).prod) = 1299989947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_23
      · exact prime_oneHundredThirtySixED_1667
      · exact prime_oneHundredThirtySixED_5651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1299989947) ^ 649994973 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299989947) ^ 433329982 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299989947) ^ 56521302 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299989947) ^ 779838 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299989947) ^ 230046 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_1359536641 : Nat.Prime 1359536641 := by
  apply lucas_primality 1359536641 (13 : ZMod 1359536641)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 1), (5, 1), (7, 1), (11, 3), (19, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 1), (5, 1), (7, 1), (11, 3), (19, 1)] : List FactorBlock).map factorBlockValue).prod) = 1359536641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_11
      · exact prime_oneHundredThirtySixED_19
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 1359536641) ^ 679768320 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (13 : ZMod 1359536641) ^ 453178880 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (13 : ZMod 1359536641) ^ 271907328 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (13 : ZMod 1359536641) ^ 194219520 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (13 : ZMod 1359536641) ^ 123594240 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (13 : ZMod 1359536641) ^ 71554560 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_1490402411 : Nat.Prime 1490402411 := by
  apply lucas_primality 1490402411 (2 : ZMod 1490402411)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (17, 1), (1252439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (17, 1), (1252439, 1)] : List FactorBlock).map factorBlockValue).prod) = 1490402411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_17
      · exact prime_oneHundredThirtySixED_1252439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1490402411) ^ 745201205 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1490402411) ^ 298080482 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1490402411) ^ 212914630 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1490402411) ^ 87670730 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1490402411) ^ 1190 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_1706467181 : Nat.Prime 1706467181 := by
  apply lucas_primality 1706467181 (2 : ZMod 1706467181)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (7756669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (7756669, 1)] : List FactorBlock).map factorBlockValue).prod) = 1706467181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_11
      · exact prime_oneHundredThirtySixED_7756669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1706467181) ^ 853233590 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1706467181) ^ 341293436 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1706467181) ^ 155133380 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1706467181) ^ 220 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_1984486577 : Nat.Prime 1984486577 := by
  apply lucas_primality 1984486577 (3 : ZMod 1984486577)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (31, 1), (1867, 1), (2143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (31, 1), (1867, 1), (2143, 1)] : List FactorBlock).map factorBlockValue).prod) = 1984486577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_31
      · exact prime_oneHundredThirtySixED_1867
      · exact prime_oneHundredThirtySixED_2143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1984486577) ^ 992243288 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1984486577) ^ 64015696 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1984486577) ^ 1062928 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1984486577) ^ 926032 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_2097407027 : Nat.Prime 2097407027 := by
  apply lucas_primality 2097407027 (6 : ZMod 2097407027)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (13, 1), (7333591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (13, 1), (7333591, 1)] : List FactorBlock).map factorBlockValue).prod) = 2097407027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_11
      · exact prime_oneHundredThirtySixED_13
      · exact prime_oneHundredThirtySixED_7333591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 2097407027) ^ 1048703513 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 2097407027) ^ 190673366 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 2097407027) ^ 161339002 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 2097407027) ^ 286 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_2175507077 : Nat.Prime 2175507077 := by
  apply lucas_primality 2175507077 (2 : ZMod 2175507077)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (97, 1), (2297, 1), (2441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (97, 1), (2297, 1), (2441, 1)] : List FactorBlock).map factorBlockValue).prod) = 2175507077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_97
      · exact prime_oneHundredThirtySixED_2297
      · exact prime_oneHundredThirtySixED_2441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2175507077) ^ 1087753538 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2175507077) ^ 22427908 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2175507077) ^ 947108 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2175507077) ^ 891236 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_2189111257 : Nat.Prime 2189111257 := by
  apply lucas_primality 2189111257 (5 : ZMod 2189111257)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (30404323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (30404323, 1)] : List FactorBlock).map factorBlockValue).prod) = 2189111257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_30404323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2189111257) ^ 1094555628 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2189111257) ^ 729703752 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2189111257) ^ 72 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_2201703901 : Nat.Prime 2201703901 := by
  apply lucas_primality 2201703901 (7 : ZMod 2201703901)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (11, 2), (131, 1), (463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (11, 2), (131, 1), (463, 1)] : List FactorBlock).map factorBlockValue).prod) = 2201703901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_11
      · exact prime_oneHundredThirtySixED_131
      · exact prime_oneHundredThirtySixED_463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2201703901) ^ 1100851950 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 2201703901) ^ 733901300 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 2201703901) ^ 440340780 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 2201703901) ^ 200154900 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 2201703901) ^ 16806900 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 2201703901) ^ 4755300 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_2416168199 : Nat.Prime 2416168199 := by
  apply lucas_primality 2416168199 (7 : ZMod 2416168199)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (71, 1), (362027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (71, 1), (362027, 1)] : List FactorBlock).map factorBlockValue).prod) = 2416168199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_47
      · exact prime_oneHundredThirtySixED_71
      · exact prime_oneHundredThirtySixED_362027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2416168199) ^ 1208084099 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 51407834 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 34030538 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 6674 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_2431500893 : Nat.Prime 2431500893 := by
  apply lucas_primality 2431500893 (2 : ZMod 2431500893)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7867, 1), (77269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7867, 1), (77269, 1)] : List FactorBlock).map factorBlockValue).prod) = 2431500893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_7867
      · exact prime_oneHundredThirtySixED_77269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2431500893) ^ 1215750446 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2431500893) ^ 309076 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2431500893) ^ 31468 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_2673598457 : Nat.Prime 2673598457 := by
  apply lucas_primality 2673598457 (3 : ZMod 2673598457)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7949, 1), (42043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7949, 1), (42043, 1)] : List FactorBlock).map factorBlockValue).prod) = 2673598457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_7949
      · exact prime_oneHundredThirtySixED_42043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2673598457) ^ 1336799228 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2673598457) ^ 336344 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2673598457) ^ 63592 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_2750335981 : Nat.Prime 2750335981 := by
  apply lucas_primality 2750335981 (6 : ZMod 2750335981)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (941, 1), (6959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (941, 1), (6959, 1)] : List FactorBlock).map factorBlockValue).prod) = 2750335981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_941
      · exact prime_oneHundredThirtySixED_6959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2750335981) ^ 1375167990 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 2750335981) ^ 916778660 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 2750335981) ^ 550067196 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 2750335981) ^ 392905140 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 2750335981) ^ 2922780 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 2750335981) ^ 395220 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_3336404189 : Nat.Prime 3336404189 := by
  apply lucas_primality 3336404189 (2 : ZMod 3336404189)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (3089, 1), (20771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (3089, 1), (20771, 1)] : List FactorBlock).map factorBlockValue).prod) = 3336404189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_13
      · exact prime_oneHundredThirtySixED_3089
      · exact prime_oneHundredThirtySixED_20771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3336404189) ^ 1668202094 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3336404189) ^ 256646476 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3336404189) ^ 1080092 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3336404189) ^ 160628 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_3402118721 : Nat.Prime 3402118721 := by
  apply lucas_primality 3402118721 (3 : ZMod 3402118721)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (7, 1), (11, 1), (13, 2), (19, 1), (43, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (7, 1), (11, 1), (13, 2), (19, 1), (43, 1)] : List FactorBlock).map factorBlockValue).prod) = 3402118721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_11
      · exact prime_oneHundredThirtySixED_13
      · exact prime_oneHundredThirtySixED_19
      · exact prime_oneHundredThirtySixED_43
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3402118721) ^ 1701059360 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3402118721) ^ 680423744 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3402118721) ^ 486016960 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3402118721) ^ 309283520 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3402118721) ^ 261701440 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3402118721) ^ 179058880 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3402118721) ^ 79119040 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_3412934363 : Nat.Prime 3412934363 := by
  apply lucas_primality 3412934363 (2 : ZMod 3412934363)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1706467181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1706467181, 1)] : List FactorBlock).map factorBlockValue).prod) = 3412934363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_1706467181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 3412934363) ^ 1706467181 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3412934363) ^ 2 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_3541035551 : Nat.Prime 3541035551 := by
  apply lucas_primality 3541035551 (7 : ZMod 3541035551)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (13, 1), (281, 1), (19387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (13, 1), (281, 1), (19387, 1)] : List FactorBlock).map factorBlockValue).prod) = 3541035551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_13
      · exact prime_oneHundredThirtySixED_281
      · exact prime_oneHundredThirtySixED_19387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3541035551) ^ 1770517775 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 3541035551) ^ 708207110 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 3541035551) ^ 272387350 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 3541035551) ^ 12601550 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 3541035551) ^ 182650 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_4041774067 : Nat.Prime 4041774067 := by
  apply lucas_primality 4041774067 (2 : ZMod 4041774067)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (61239001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (61239001, 1)] : List FactorBlock).map factorBlockValue).prod) = 4041774067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_11
      · exact prime_oneHundredThirtySixED_61239001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4041774067) ^ 2020887033 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4041774067) ^ 1347258022 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4041774067) ^ 367434006 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4041774067) ^ 66 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_4044130543 : Nat.Prime 4044130543 := by
  apply lucas_primality 4044130543 (29 : ZMod 4044130543)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (61, 1), (3683179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (61, 1), (3683179, 1)] : List FactorBlock).map factorBlockValue).prod) = 4044130543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_61
      · exact prime_oneHundredThirtySixED_3683179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (29 : ZMod 4044130543) ^ 2022065271 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (29 : ZMod 4044130543) ^ 1348043514 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (29 : ZMod 4044130543) ^ 66297222 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (29 : ZMod 4044130543) ^ 1098 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_4123911607 : Nat.Prime 4123911607 := by
  apply lucas_primality 4123911607 (3 : ZMod 4123911607)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (83, 1), (271, 1), (30557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (83, 1), (271, 1), (30557, 1)] : List FactorBlock).map factorBlockValue).prod) = 4123911607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_83
      · exact prime_oneHundredThirtySixED_271
      · exact prime_oneHundredThirtySixED_30557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4123911607) ^ 2061955803 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4123911607) ^ 1374637202 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4123911607) ^ 49685682 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4123911607) ^ 15217386 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4123911607) ^ 134958 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_4434987971 : Nat.Prime 4434987971 := by
  apply lucas_primality 4434987971 (6 : ZMod 4434987971)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (83, 1), (131, 1), (5827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (83, 1), (131, 1), (5827, 1)] : List FactorBlock).map factorBlockValue).prod) = 4434987971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_83
      · exact prime_oneHundredThirtySixED_131
      · exact prime_oneHundredThirtySixED_5827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 4434987971) ^ 2217493985 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 4434987971) ^ 886997594 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 4434987971) ^ 633569710 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 4434987971) ^ 53433590 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 4434987971) ^ 33854870 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 4434987971) ^ 761110 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_4832939099 : Nat.Prime 4832939099 := by
  apply lucas_primality 4832939099 (2 : ZMod 4832939099)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (59, 1), (3150547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (59, 1), (3150547, 1)] : List FactorBlock).map factorBlockValue).prod) = 4832939099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_13
      · exact prime_oneHundredThirtySixED_59
      · exact prime_oneHundredThirtySixED_3150547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4832939099) ^ 2416469549 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4832939099) ^ 371764546 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4832939099) ^ 81914222 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4832939099) ^ 1534 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_5126804671 : Nat.Prime 5126804671 := by
  apply lucas_primality 5126804671 (7 : ZMod 5126804671)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (1823, 1), (7211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (1823, 1), (7211, 1)] : List FactorBlock).map factorBlockValue).prod) = 5126804671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_13
      · exact prime_oneHundredThirtySixED_1823
      · exact prime_oneHundredThirtySixED_7211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 5126804671) ^ 2563402335 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 5126804671) ^ 1708934890 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 5126804671) ^ 1025360934 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 5126804671) ^ 394369590 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 5126804671) ^ 2812290 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 5126804671) ^ 710970 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_5310091289 : Nat.Prime 5310091289 := by
  apply lucas_primality 5310091289 (3 : ZMod 5310091289)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (131, 1), (5066881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (131, 1), (5066881, 1)] : List FactorBlock).map factorBlockValue).prod) = 5310091289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_131
      · exact prime_oneHundredThirtySixED_5066881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5310091289) ^ 2655045644 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 5310091289) ^ 40535048 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 5310091289) ^ 1048 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_31
      · exact prime_oneHundredThirtySixED_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_6650476597 : Nat.Prime 6650476597 := by
  apply lucas_primality 6650476597 (5 : ZMod 6650476597)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (19, 1), (1571, 1), (2063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (19, 1), (1571, 1), (2063, 1)] : List FactorBlock).map factorBlockValue).prod) = 6650476597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_19
      · exact prime_oneHundredThirtySixED_1571
      · exact prime_oneHundredThirtySixED_2063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6650476597) ^ 3325238298 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 6650476597) ^ 2216825532 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 6650476597) ^ 350025084 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 6650476597) ^ 4233276 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 6650476597) ^ 3223692 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_6825868727 : Nat.Prime 6825868727 := by
  apply lucas_primality 6825868727 (5 : ZMod 6825868727)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3412934363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3412934363, 1)] : List FactorBlock).map factorBlockValue).prod) = 6825868727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3412934363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 6825868727) ^ 3412934363 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 6825868727) ^ 2 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_6997720267 : Nat.Prime 6997720267 := by
  apply lucas_primality 6997720267 (3 : ZMod 6997720267)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (271, 1), (937, 1), (1531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (271, 1), (937, 1), (1531, 1)] : List FactorBlock).map factorBlockValue).prod) = 6997720267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_271
      · exact prime_oneHundredThirtySixED_937
      · exact prime_oneHundredThirtySixED_1531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6997720267) ^ 3498860133 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 6997720267) ^ 2332573422 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 6997720267) ^ 25821846 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 6997720267) ^ 7468218 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 6997720267) ^ 4570686 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_7992514897 : Nat.Prime 7992514897 := by
  apply lucas_primality 7992514897 (10 : ZMod 7992514897)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (103, 1), (1616609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (103, 1), (1616609, 1)] : List FactorBlock).map factorBlockValue).prod) = 7992514897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_103
      · exact prime_oneHundredThirtySixED_1616609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 7992514897) ^ 3996257448 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (10 : ZMod 7992514897) ^ 2664171632 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (10 : ZMod 7992514897) ^ 77597232 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (10 : ZMod 7992514897) ^ 4944 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_8067845633 : Nat.Prime 8067845633 := by
  apply lucas_primality 8067845633 (6 : ZMod 8067845633)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (7, 1), (11, 1), (113, 1), (1811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (7, 1), (11, 1), (113, 1), (1811, 1)] : List FactorBlock).map factorBlockValue).prod) = 8067845633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_11
      · exact prime_oneHundredThirtySixED_113
      · exact prime_oneHundredThirtySixED_1811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 8067845633) ^ 4033922816 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 8067845633) ^ 1152549376 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 8067845633) ^ 733440512 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 8067845633) ^ 71396864 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 8067845633) ^ 4454912 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_8366480557 : Nat.Prime 8366480557 := by
  apply lucas_primality 8366480557 (2 : ZMod 8366480557)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (151, 1), (659609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (151, 1), (659609, 1)] : List FactorBlock).map factorBlockValue).prod) = 8366480557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_151
      · exact prime_oneHundredThirtySixED_659609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8366480557) ^ 4183240278 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 8366480557) ^ 2788826852 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 8366480557) ^ 1195211508 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 8366480557) ^ 55407156 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 8366480557) ^ 12684 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_10195979077 : Nat.Prime 10195979077 := by
  apply lucas_primality 10195979077 (2 : ZMod 10195979077)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (283221641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (283221641, 1)] : List FactorBlock).map factorBlockValue).prod) = 10195979077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_283221641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 10195979077) ^ 5097989538 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 10195979077) ^ 3398659692 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 10195979077) ^ 36 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_10922799403 : Nat.Prime 10922799403 := by
  apply lucas_primality 10922799403 (3 : ZMod 10922799403)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (202274063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (202274063, 1)] : List FactorBlock).map factorBlockValue).prod) = 10922799403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_202274063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 10922799403) ^ 5461399701 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 10922799403) ^ 3640933134 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 10922799403) ^ 54 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_11520557303 : Nat.Prime 11520557303 := by
  apply lucas_primality 11520557303 (5 : ZMod 11520557303)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (8761, 1), (657491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (8761, 1), (657491, 1)] : List FactorBlock).map factorBlockValue).prod) = 11520557303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_8761
      · exact prime_oneHundredThirtySixED_657491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 11520557303) ^ 5760278651 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 11520557303) ^ 1314982 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 11520557303) ^ 17522 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_16135691267 : Nat.Prime 16135691267 := by
  apply lucas_primality 16135691267 (2 : ZMod 16135691267)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (8067845633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (8067845633, 1)] : List FactorBlock).map factorBlockValue).prod) = 16135691267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_8067845633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 16135691267) ^ 8067845633 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 16135691267) ^ 2 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_16934176229 : Nat.Prime 16934176229 := by
  apply lucas_primality 16934176229 (2 : ZMod 16934176229)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (6521, 1), (649217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (6521, 1), (649217, 1)] : List FactorBlock).map factorBlockValue).prod) = 16934176229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_6521
      · exact prime_oneHundredThirtySixED_649217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 16934176229) ^ 8467088114 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 16934176229) ^ 2596868 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 16934176229) ^ 26084 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_18430972757 : Nat.Prime 18430972757 := by
  apply lucas_primality 18430972757 (2 : ZMod 18430972757)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (17, 1), (4597, 1), (8423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (17, 1), (4597, 1), (8423, 1)] : List FactorBlock).map factorBlockValue).prod) = 18430972757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_17
      · exact prime_oneHundredThirtySixED_4597
      · exact prime_oneHundredThirtySixED_8423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18430972757) ^ 9215486378 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 18430972757) ^ 2632996108 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 18430972757) ^ 1084174868 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 18430972757) ^ 4009348 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 18430972757) ^ 2188172 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_21462596431 : Nat.Prime 21462596431 := by
  apply lucas_primality 21462596431 (3 : ZMod 21462596431)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 2), (197, 1), (30013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 2), (197, 1), (30013, 1)] : List FactorBlock).map factorBlockValue).prod) = 21462596431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_11
      · exact prime_oneHundredThirtySixED_197
      · exact prime_oneHundredThirtySixED_30013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 21462596431) ^ 10731298215 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 21462596431) ^ 7154198810 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 21462596431) ^ 4292519286 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 21462596431) ^ 1951145130 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 21462596431) ^ 108947190 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 21462596431) ^ 715110 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_23869257613 : Nat.Prime 23869257613 := by
  apply lucas_primality 23869257613 (5 : ZMod 23869257613)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (31, 1), (1451, 1), (44221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (31, 1), (1451, 1), (44221, 1)] : List FactorBlock).map factorBlockValue).prod) = 23869257613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_31
      · exact prime_oneHundredThirtySixED_1451
      · exact prime_oneHundredThirtySixED_44221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 23869257613) ^ 11934628806 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 23869257613) ^ 7956419204 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 23869257613) ^ 769976052 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 23869257613) ^ 16450212 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 23869257613) ^ 539772 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_24250644403 : Nat.Prime 24250644403 := by
  apply lucas_primality 24250644403 (2 : ZMod 24250644403)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4041774067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4041774067, 1)] : List FactorBlock).map factorBlockValue).prod) = 24250644403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_4041774067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 24250644403) ^ 12125322201 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 24250644403) ^ 8083548134 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 24250644403) ^ 6 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_24828938929 : Nat.Prime 24828938929 := by
  apply lucas_primality 24828938929 (19 : ZMod 24828938929)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (172423187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (172423187, 1)] : List FactorBlock).map factorBlockValue).prod) = 24828938929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_172423187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (19 : ZMod 24828938929) ^ 12414469464 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (19 : ZMod 24828938929) ^ 8276312976 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (19 : ZMod 24828938929) ^ 144 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_24888664277 : Nat.Prime 24888664277 := by
  apply lucas_primality 24888664277 (2 : ZMod 24888664277)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (126982981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (126982981, 1)] : List FactorBlock).map factorBlockValue).prod) = 24888664277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_126982981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 24888664277) ^ 12444332138 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 24888664277) ^ 3555523468 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 24888664277) ^ 196 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_29816588057 : Nat.Prime 29816588057 := by
  apply lucas_primality 29816588057 (3 : ZMod 29816588057)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (40433, 1), (92179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (40433, 1), (92179, 1)] : List FactorBlock).map factorBlockValue).prod) = 29816588057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_40433
      · exact prime_oneHundredThirtySixED_92179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 29816588057) ^ 14908294028 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 29816588057) ^ 737432 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 29816588057) ^ 323464 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_29844570527 : Nat.Prime 29844570527 := by
  apply lucas_primality 29844570527 (5 : ZMod 29844570527)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (547, 1), (947, 1), (28807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (547, 1), (947, 1), (28807, 1)] : List FactorBlock).map factorBlockValue).prod) = 29844570527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_547
      · exact prime_oneHundredThirtySixED_947
      · exact prime_oneHundredThirtySixED_28807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 29844570527) ^ 14922285263 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 29844570527) ^ 54560458 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 29844570527) ^ 31514858 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 29844570527) ^ 1036018 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_29900001559 : Nat.Prime 29900001559 := by
  apply lucas_primality 29900001559 (29 : ZMod 29900001559)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (711904799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (711904799, 1)] : List FactorBlock).map factorBlockValue).prod) = 29900001559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_711904799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (29 : ZMod 29900001559) ^ 14950000779 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (29 : ZMod 29900001559) ^ 9966667186 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (29 : ZMod 29900001559) ^ 4271428794 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (29 : ZMod 29900001559) ^ 42 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_31789660873 : Nat.Prime 31789660873 := by
  apply lucas_primality 31789660873 (5 : ZMod 31789660873)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1831, 1), (723413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1831, 1), (723413, 1)] : List FactorBlock).map factorBlockValue).prod) = 31789660873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_1831
      · exact prime_oneHundredThirtySixED_723413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 31789660873) ^ 15894830436 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 31789660873) ^ 10596553624 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 31789660873) ^ 17361912 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 31789660873) ^ 43944 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_33968448887 : Nat.Prime 33968448887 := by
  apply lucas_primality 33968448887 (5 : ZMod 33968448887)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (15773, 1), (46817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (15773, 1), (46817, 1)] : List FactorBlock).map factorBlockValue).prod) = 33968448887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_23
      · exact prime_oneHundredThirtySixED_15773
      · exact prime_oneHundredThirtySixED_46817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 33968448887) ^ 16984224443 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 33968448887) ^ 1476889082 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 33968448887) ^ 2153582 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 33968448887) ^ 725558 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_36093704951 : Nat.Prime 36093704951 := by
  apply lucas_primality 36093704951 (26 : ZMod 36093704951)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (379, 1), (1904681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (379, 1), (1904681, 1)] : List FactorBlock).map factorBlockValue).prod) = 36093704951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_379
      · exact prime_oneHundredThirtySixED_1904681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (26 : ZMod 36093704951) ^ 18046852475 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (26 : ZMod 36093704951) ^ 7218740990 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (26 : ZMod 36093704951) ^ 95234050 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (26 : ZMod 36093704951) ^ 18950 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_38125454137 : Nat.Prime 38125454137 := by
  apply lucas_primality 38125454137 (15 : ZMod 38125454137)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (11, 1), (2447, 1), (8431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (11, 1), (2447, 1), (8431, 1)] : List FactorBlock).map factorBlockValue).prod) = 38125454137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_11
      · exact prime_oneHundredThirtySixED_2447
      · exact prime_oneHundredThirtySixED_8431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 38125454137) ^ 19062727068 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (15 : ZMod 38125454137) ^ 12708484712 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (15 : ZMod 38125454137) ^ 5446493448 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (15 : ZMod 38125454137) ^ 3465950376 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (15 : ZMod 38125454137) ^ 15580488 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (15 : ZMod 38125454137) ^ 4522056 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_40726658551 : Nat.Prime 40726658551 := by
  apply lucas_primality 40726658551 (6 : ZMod 40726658551)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (47, 1), (5776831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (47, 1), (5776831, 1)] : List FactorBlock).map factorBlockValue).prod) = 40726658551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_47
      · exact prime_oneHundredThirtySixED_5776831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 40726658551) ^ 20363329275 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 40726658551) ^ 13575552850 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 40726658551) ^ 8145331710 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 40726658551) ^ 866524650 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 40726658551) ^ 7050 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_48437485823 : Nat.Prime 48437485823 := by
  apply lucas_primality 48437485823 (5 : ZMod 48437485823)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (2201703901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (2201703901, 1)] : List FactorBlock).map factorBlockValue).prod) = 48437485823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_11
      · exact prime_oneHundredThirtySixED_2201703901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 48437485823) ^ 24218742911 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 48437485823) ^ 4403407802 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 48437485823) ^ 22 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_48622436773 : Nat.Prime 48622436773 := by
  apply lucas_primality 48622436773 (6 : ZMod 48622436773)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (13, 1), (41, 1), (167, 1), (929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (13, 1), (41, 1), (167, 1), (929, 1)] : List FactorBlock).map factorBlockValue).prod) = 48622436773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_13
      · exact prime_oneHundredThirtySixED_41
      · exact prime_oneHundredThirtySixED_167
      · exact prime_oneHundredThirtySixED_929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 48622436773) ^ 24311218386 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 48622436773) ^ 16207478924 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 48622436773) ^ 6946062396 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 48622436773) ^ 3740187444 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 48622436773) ^ 1185913092 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 48622436773) ^ 291152316 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 48622436773) ^ 52338468 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_76152073229 : Nat.Prime 76152073229 := by
  apply lucas_primality 76152073229 (2 : ZMod 76152073229)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (247246991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (247246991, 1)] : List FactorBlock).map factorBlockValue).prod) = 76152073229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_11
      · exact prime_oneHundredThirtySixED_247246991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 76152073229) ^ 38076036614 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 76152073229) ^ 10878867604 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 76152073229) ^ 6922915748 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 76152073229) ^ 308 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_95575199771 : Nat.Prime 95575199771 := by
  apply lucas_primality 95575199771 (2 : ZMod 95575199771)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (509, 1), (18777053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (509, 1), (18777053, 1)] : List FactorBlock).map factorBlockValue).prod) = 95575199771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_509
      · exact prime_oneHundredThirtySixED_18777053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 95575199771) ^ 47787599885 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 95575199771) ^ 19115039954 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 95575199771) ^ 187770530 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 95575199771) ^ 5090 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_97738167361 : Nat.Prime 97738167361 := by
  apply lucas_primality 97738167361 (11 : ZMod 97738167361)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (137, 1), (743143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (137, 1), (743143, 1)] : List FactorBlock).map factorBlockValue).prod) = 97738167361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_137
      · exact prime_oneHundredThirtySixED_743143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 97738167361) ^ 48869083680 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (11 : ZMod 97738167361) ^ 32579389120 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (11 : ZMod 97738167361) ^ 19547633472 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (11 : ZMod 97738167361) ^ 713417280 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (11 : ZMod 97738167361) ^ 131520 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_100420121233 : Nat.Prime 100420121233 := by
  apply lucas_primality 100420121233 (5 : ZMod 100420121233)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (127, 1), (5491039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (127, 1), (5491039, 1)] : List FactorBlock).map factorBlockValue).prod) = 100420121233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_127
      · exact prime_oneHundredThirtySixED_5491039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 100420121233) ^ 50210060616 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 100420121233) ^ 33473373744 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 100420121233) ^ 790709616 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 100420121233) ^ 18288 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_103030056421 : Nat.Prime 103030056421 := by
  apply lucas_primality 103030056421 (6 : ZMod 103030056421)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (47, 1), (1427, 1), (25603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (47, 1), (1427, 1), (25603, 1)] : List FactorBlock).map factorBlockValue).prod) = 103030056421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_47
      · exact prime_oneHundredThirtySixED_1427
      · exact prime_oneHundredThirtySixED_25603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 103030056421) ^ 51515028210 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 103030056421) ^ 34343352140 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 103030056421) ^ 20606011284 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 103030056421) ^ 2192128860 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 103030056421) ^ 72200460 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 103030056421) ^ 4024140 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_119826767293 : Nat.Prime 119826767293 := by
  apply lucas_primality 119826767293 (2 : ZMod 119826767293)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (93089, 1), (107269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (93089, 1), (107269, 1)] : List FactorBlock).map factorBlockValue).prod) = 119826767293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_93089
      · exact prime_oneHundredThirtySixED_107269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 119826767293) ^ 59913383646 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 119826767293) ^ 39942255764 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 119826767293) ^ 1287228 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 119826767293) ^ 1117068 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_121175790187 : Nat.Prime 121175790187 := by
  apply lucas_primality 121175790187 (2 : ZMod 121175790187)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (17, 1), (107999813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (17, 1), (107999813, 1)] : List FactorBlock).map factorBlockValue).prod) = 121175790187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_11
      · exact prime_oneHundredThirtySixED_17
      · exact prime_oneHundredThirtySixED_107999813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 121175790187) ^ 60587895093 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 121175790187) ^ 40391930062 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 121175790187) ^ 11015980926 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 121175790187) ^ 7127987658 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 121175790187) ^ 1122 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_121710218477 : Nat.Prime 121710218477 := by
  apply lucas_primality 121710218477 (2 : ZMod 121710218477)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (395163047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (395163047, 1)] : List FactorBlock).map factorBlockValue).prod) = 121710218477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_11
      · exact prime_oneHundredThirtySixED_395163047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 121710218477) ^ 60855109238 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 121710218477) ^ 17387174068 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 121710218477) ^ 11064565316 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 121710218477) ^ 308 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_137741844557 : Nat.Prime 137741844557 := by
  apply lucas_primality 137741844557 (2 : ZMod 137741844557)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4217, 1), (8165867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4217, 1), (8165867, 1)] : List FactorBlock).map factorBlockValue).prod) = 137741844557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_4217
      · exact prime_oneHundredThirtySixED_8165867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 137741844557) ^ 68870922278 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 137741844557) ^ 32663468 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 137741844557) ^ 16868 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_138513235027 : Nat.Prime 138513235027 := by
  apply lucas_primality 138513235027 (2 : ZMod 138513235027)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (457, 1), (1232083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (457, 1), (1232083, 1)] : List FactorBlock).map factorBlockValue).prod) = 138513235027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_41
      · exact prime_oneHundredThirtySixED_457
      · exact prime_oneHundredThirtySixED_1232083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 138513235027) ^ 69256617513 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 138513235027) ^ 46171078342 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 138513235027) ^ 3378371586 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 138513235027) ^ 303092418 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 138513235027) ^ 112422 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_184564968157 : Nat.Prime 184564968157 := by
  apply lucas_primality 184564968157 (2 : ZMod 184564968157)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5126804671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5126804671, 1)] : List FactorBlock).map factorBlockValue).prod) = 184564968157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_5126804671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 184564968157) ^ 92282484078 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 184564968157) ^ 61521656052 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 184564968157) ^ 36 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_229254061573 : Nat.Prime 229254061573 := by
  apply lucas_primality 229254061573 (2 : ZMod 229254061573)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (29, 1), (43, 1), (683, 1), (7477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (29, 1), (43, 1), (683, 1), (7477, 1)] : List FactorBlock).map factorBlockValue).prod) = 229254061573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_29
      · exact prime_oneHundredThirtySixED_43
      · exact prime_oneHundredThirtySixED_683
      · exact prime_oneHundredThirtySixED_7477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 229254061573) ^ 114627030786 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 229254061573) ^ 76418020524 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 229254061573) ^ 7905312468 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 229254061573) ^ 5331489804 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 229254061573) ^ 335657484 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 229254061573) ^ 30661236 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_233717500609 : Nat.Prime 233717500609 := by
  apply lucas_primality 233717500609 (7 : ZMod 233717500609)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (331, 1), (3677579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (331, 1), (3677579, 1)] : List FactorBlock).map factorBlockValue).prod) = 233717500609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_331
      · exact prime_oneHundredThirtySixED_3677579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 233717500609) ^ 116858750304 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 233717500609) ^ 77905833536 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 233717500609) ^ 706095168 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 233717500609) ^ 63552 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_380936639021 : Nat.Prime 380936639021 := by
  apply lucas_primality 380936639021 (2 : ZMod 380936639021)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (4603, 1), (591131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (4603, 1), (591131, 1)] : List FactorBlock).map factorBlockValue).prod) = 380936639021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_4603
      · exact prime_oneHundredThirtySixED_591131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 380936639021) ^ 190468319510 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 380936639021) ^ 76187327804 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 380936639021) ^ 54419519860 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 380936639021) ^ 82758340 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 380936639021) ^ 644420 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_510047838721 : Nat.Prime 510047838721 := by
  apply lucas_primality 510047838721 (13 : ZMod 510047838721)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 2), (5, 1), (7, 1), (3162499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 2), (5, 1), (7, 1), (3162499, 1)] : List FactorBlock).map factorBlockValue).prod) = 510047838721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_3162499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 510047838721) ^ 255023919360 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (13 : ZMod 510047838721) ^ 170015946240 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (13 : ZMod 510047838721) ^ 102009567744 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (13 : ZMod 510047838721) ^ 72863976960 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (13 : ZMod 510047838721) ^ 161280 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_686232454673 : Nat.Prime 686232454673 := by
  apply lucas_primality 686232454673 (3 : ZMod 686232454673)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (79, 1), (419, 1), (1295717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (79, 1), (419, 1), (1295717, 1)] : List FactorBlock).map factorBlockValue).prod) = 686232454673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_79
      · exact prime_oneHundredThirtySixED_419
      · exact prime_oneHundredThirtySixED_1295717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 686232454673) ^ 343116227336 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 686232454673) ^ 8686486768 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 686232454673) ^ 1637786288 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 686232454673) ^ 529616 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_967726813453 : Nat.Prime 967726813453 := by
  apply lucas_primality 967726813453 (2 : ZMod 967726813453)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (11520557303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (11520557303, 1)] : List FactorBlock).map factorBlockValue).prod) = 967726813453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_11520557303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 967726813453) ^ 483863406726 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 967726813453) ^ 322575604484 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 967726813453) ^ 138246687636 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 967726813453) ^ 84 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_1040044758167 : Nat.Prime 1040044758167 := by
  apply lucas_primality 1040044758167 (5 : ZMod 1040044758167)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (183299, 1), (2837017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (183299, 1), (2837017, 1)] : List FactorBlock).map factorBlockValue).prod) = 1040044758167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_183299
      · exact prime_oneHundredThirtySixED_2837017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1040044758167) ^ 520022379083 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1040044758167) ^ 5674034 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1040044758167) ^ 366598 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_1043134554017 : Nat.Prime 1043134554017 := by
  apply lucas_primality 1043134554017 (3 : ZMod 1043134554017)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (67, 1), (1481, 1), (328519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (67, 1), (1481, 1), (328519, 1)] : List FactorBlock).map factorBlockValue).prod) = 1043134554017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_67
      · exact prime_oneHundredThirtySixED_1481
      · exact prime_oneHundredThirtySixED_328519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1043134554017) ^ 521567277008 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1043134554017) ^ 15569172448 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1043134554017) ^ 704344736 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1043134554017) ^ 3175264 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_2150239681943 : Nat.Prime 2150239681943 := by
  apply lucas_primality 2150239681943 (5 : ZMod 2150239681943)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (97738167361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (97738167361, 1)] : List FactorBlock).map factorBlockValue).prod) = 2150239681943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_11
      · exact prime_oneHundredThirtySixED_97738167361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2150239681943) ^ 1075119840971 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2150239681943) ^ 195476334722 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2150239681943) ^ 22 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_2269179614687 : Nat.Prime 2269179614687 := by
  apply lucas_primality 2269179614687 (5 : ZMod 2269179614687)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (16934176229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (16934176229, 1)] : List FactorBlock).map factorBlockValue).prod) = 2269179614687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_67
      · exact prime_oneHundredThirtySixED_16934176229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2269179614687) ^ 1134589807343 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2269179614687) ^ 33868352458 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2269179614687) ^ 134 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_2318003452577 : Nat.Prime 2318003452577 := by
  apply lucas_primality 2318003452577 (6 : ZMod 2318003452577)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (233, 1), (44413003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (233, 1), (44413003, 1)] : List FactorBlock).map factorBlockValue).prod) = 2318003452577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_233
      · exact prime_oneHundredThirtySixED_44413003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 2318003452577) ^ 1159001726288 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 2318003452577) ^ 331143350368 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 2318003452577) ^ 9948512672 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 2318003452577) ^ 52192 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_2351242931491 : Nat.Prime 2351242931491 := by
  apply lucas_primality 2351242931491 (3 : ZMod 2351242931491)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (59, 1), (61, 2), (127, 1), (937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (59, 1), (61, 2), (127, 1), (937, 1)] : List FactorBlock).map factorBlockValue).prod) = 2351242931491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_59
      · exact prime_oneHundredThirtySixED_61
      · exact prime_oneHundredThirtySixED_127
      · exact prime_oneHundredThirtySixED_937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2351242931491) ^ 1175621465745 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2351242931491) ^ 783747643830 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2351242931491) ^ 470248586298 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2351242931491) ^ 39851575110 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2351242931491) ^ 38544966090 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2351242931491) ^ 18513723870 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2351242931491) ^ 2509330770 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_2415003365941 : Nat.Prime 2415003365941 := by
  apply lucas_primality 2415003365941 (6 : ZMod 2415003365941)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (79, 1), (971, 1), (47701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (79, 1), (971, 1), (47701, 1)] : List FactorBlock).map factorBlockValue).prod) = 2415003365941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_11
      · exact prime_oneHundredThirtySixED_79
      · exact prime_oneHundredThirtySixED_971
      · exact prime_oneHundredThirtySixED_47701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2415003365941) ^ 1207501682970 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 2415003365941) ^ 805001121980 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 2415003365941) ^ 483000673188 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 2415003365941) ^ 219545760540 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 2415003365941) ^ 30569662860 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 2415003365941) ^ 2487130140 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 2415003365941) ^ 50627940 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_2548779381751 : Nat.Prime 2548779381751 := by
  apply lucas_primality 2548779381751 (3 : ZMod 2548779381751)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (7, 2), (19, 1), (113, 1), (32303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (7, 2), (19, 1), (113, 1), (32303, 1)] : List FactorBlock).map factorBlockValue).prod) = 2548779381751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_19
      · exact prime_oneHundredThirtySixED_113
      · exact prime_oneHundredThirtySixED_32303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2548779381751) ^ 1274389690875 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2548779381751) ^ 849593127250 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2548779381751) ^ 509755876350 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2548779381751) ^ 364111340250 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2548779381751) ^ 134146283250 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2548779381751) ^ 22555569750 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2548779381751) ^ 78902250 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_2692262496923 : Nat.Prime 2692262496923 := by
  apply lucas_primality 2692262496923 (2 : ZMod 2692262496923)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (116741, 1), (11530921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (116741, 1), (11530921, 1)] : List FactorBlock).map factorBlockValue).prod) = 2692262496923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_116741
      · exact prime_oneHundredThirtySixED_11530921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2692262496923) ^ 1346131248461 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2692262496923) ^ 23061842 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2692262496923) ^ 233482 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_2921045243449 : Nat.Prime 2921045243449 := by
  apply lucas_primality 2921045243449 (13 : ZMod 2921045243449)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (121710218477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (121710218477, 1)] : List FactorBlock).map factorBlockValue).prod) = 2921045243449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_121710218477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 2921045243449) ^ 1460522621724 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (13 : ZMod 2921045243449) ^ 973681747816 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (13 : ZMod 2921045243449) ^ 24 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_3275005491103 : Nat.Prime 3275005491103 := by
  apply lucas_primality 3275005491103 (5 : ZMod 3275005491103)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (317, 1), (90624979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (317, 1), (90624979, 1)] : List FactorBlock).map factorBlockValue).prod) = 3275005491103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_19
      · exact prime_oneHundredThirtySixED_317
      · exact prime_oneHundredThirtySixED_90624979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3275005491103) ^ 1637502745551 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 3275005491103) ^ 1091668497034 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 3275005491103) ^ 172368710058 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 3275005491103) ^ 10331247606 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 3275005491103) ^ 36138 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_4041154484167 : Nat.Prime 4041154484167 := by
  apply lucas_primality 4041154484167 (3 : ZMod 4041154484167)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (277, 1), (2431500893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (277, 1), (2431500893, 1)] : List FactorBlock).map factorBlockValue).prod) = 4041154484167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_277
      · exact prime_oneHundredThirtySixED_2431500893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4041154484167) ^ 2020577242083 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4041154484167) ^ 1347051494722 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4041154484167) ^ 14589005358 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4041154484167) ^ 1662 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_4667461964617 : Nat.Prime 4667461964617 := by
  apply lucas_primality 4667461964617 (5 : ZMod 4667461964617)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (59, 1), (197, 1), (1521103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (59, 1), (197, 1), (1521103, 1)] : List FactorBlock).map factorBlockValue).prod) = 4667461964617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_11
      · exact prime_oneHundredThirtySixED_59
      · exact prime_oneHundredThirtySixED_197
      · exact prime_oneHundredThirtySixED_1521103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4667461964617) ^ 2333730982308 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 4667461964617) ^ 1555820654872 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 4667461964617) ^ 424314724056 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 4667461964617) ^ 79109524824 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 4667461964617) ^ 23692700328 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 4667461964617) ^ 3068472 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_5043589354607 : Nat.Prime 5043589354607 := by
  apply lucas_primality 5043589354607 (5 : ZMod 5043589354607)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (229254061573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (229254061573, 1)] : List FactorBlock).map factorBlockValue).prod) = 5043589354607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_11
      · exact prime_oneHundredThirtySixED_229254061573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 5043589354607) ^ 2521794677303 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 5043589354607) ^ 458508123146 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 5043589354607) ^ 22 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_5417012621731 : Nat.Prime 5417012621731 := by
  apply lucas_primality 5417012621731 (2 : ZMod 5417012621731)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (83, 1), (2175507077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (83, 1), (2175507077, 1)] : List FactorBlock).map factorBlockValue).prod) = 5417012621731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_83
      · exact prime_oneHundredThirtySixED_2175507077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5417012621731) ^ 2708506310865 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 5417012621731) ^ 1805670873910 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 5417012621731) ^ 1083402524346 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 5417012621731) ^ 65265212310 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 5417012621731) ^ 2490 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_6880433178221 : Nat.Prime 6880433178221 := by
  apply lucas_primality 6880433178221 (2 : ZMod 6880433178221)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (179, 1), (4177, 1), (65731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (179, 1), (4177, 1), (65731, 1)] : List FactorBlock).map factorBlockValue).prod) = 6880433178221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_179
      · exact prime_oneHundredThirtySixED_4177
      · exact prime_oneHundredThirtySixED_65731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6880433178221) ^ 3440216589110 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 6880433178221) ^ 1376086635644 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 6880433178221) ^ 982919025460 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 6880433178221) ^ 38438174180 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 6880433178221) ^ 1647218860 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 6880433178221) ^ 104675620 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_7211432400817 : Nat.Prime 7211432400817 := by
  apply lucas_primality 7211432400817 (5 : ZMod 7211432400817)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (21462596431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (21462596431, 1)] : List FactorBlock).map factorBlockValue).prod) = 7211432400817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_21462596431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7211432400817) ^ 3605716200408 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 7211432400817) ^ 2403810800272 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 7211432400817) ^ 1030204628688 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 7211432400817) ^ 336 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_8896585869827 : Nat.Prime 8896585869827 := by
  apply lucas_primality 8896585869827 (2 : ZMod 8896585869827)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (59, 1), (4434987971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (59, 1), (4434987971, 1)] : List FactorBlock).map factorBlockValue).prod) = 8896585869827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_17
      · exact prime_oneHundredThirtySixED_59
      · exact prime_oneHundredThirtySixED_4434987971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8896585869827) ^ 4448292934913 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 8896585869827) ^ 523328580578 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 8896585869827) ^ 150789591014 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 8896585869827) ^ 2006 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_9770686982351 : Nat.Prime 9770686982351 := by
  apply lucas_primality 9770686982351 (11 : ZMod 9770686982351)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 2), (353, 1), (11297551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 2), (353, 1), (11297551, 1)] : List FactorBlock).map factorBlockValue).prod) = 9770686982351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_353
      · exact prime_oneHundredThirtySixED_11297551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 9770686982351) ^ 4885343491175 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (11 : ZMod 9770686982351) ^ 1954137396470 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (11 : ZMod 9770686982351) ^ 1395812426050 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (11 : ZMod 9770686982351) ^ 27678999950 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (11 : ZMod 9770686982351) ^ 864850 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_9785892628279 : Nat.Prime 9785892628279 := by
  apply lucas_primality 9785892628279 (6 : ZMod 9785892628279)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (13, 1), (229, 1), (20291147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (13, 1), (229, 1), (20291147, 1)] : List FactorBlock).map factorBlockValue).prod) = 9785892628279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_13
      · exact prime_oneHundredThirtySixED_229
      · exact prime_oneHundredThirtySixED_20291147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 9785892628279) ^ 4892946314139 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 9785892628279) ^ 3261964209426 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 9785892628279) ^ 752760971406 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 9785892628279) ^ 42733155582 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 9785892628279) ^ 482274 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_11536480800199 : Nat.Prime 11536480800199 := by
  apply lucas_primality 11536480800199 (3 : ZMod 11536480800199)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11821, 1), (18072797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11821, 1), (18072797, 1)] : List FactorBlock).map factorBlockValue).prod) = 11536480800199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_11821
      · exact prime_oneHundredThirtySixED_18072797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 11536480800199) ^ 5768240400099 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 11536480800199) ^ 3845493600066 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 11536480800199) ^ 975931038 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 11536480800199) ^ 638334 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_12588826861241 : Nat.Prime 12588826861241 := by
  apply lucas_primality 12588826861241 (3 : ZMod 12588826861241)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (61, 1), (8191, 1), (89983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (61, 1), (8191, 1), (89983, 1)] : List FactorBlock).map factorBlockValue).prod) = 12588826861241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_61
      · exact prime_oneHundredThirtySixED_8191
      · exact prime_oneHundredThirtySixED_89983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 12588826861241) ^ 6294413430620 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 12588826861241) ^ 2517765372248 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 12588826861241) ^ 1798403837320 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 12588826861241) ^ 206374210840 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 12588826861241) ^ 1536909640 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 12588826861241) ^ 139902280 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_14858519144333 : Nat.Prime 14858519144333 := by
  apply lucas_primality 14858519144333 (2 : ZMod 14858519144333)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (119826767293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (119826767293, 1)] : List FactorBlock).map factorBlockValue).prod) = 14858519144333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_31
      · exact prime_oneHundredThirtySixED_119826767293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 14858519144333) ^ 7429259572166 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 14858519144333) ^ 479307069172 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 14858519144333) ^ 124 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_17953079747549 : Nat.Prime 17953079747549 := by
  apply lucas_primality 17953079747549 (2 : ZMod 17953079747549)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (23, 1), (857, 1), (20700347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (23, 1), (857, 1), (20700347, 1)] : List FactorBlock).map factorBlockValue).prod) = 17953079747549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_11
      · exact prime_oneHundredThirtySixED_23
      · exact prime_oneHundredThirtySixED_857
      · exact prime_oneHundredThirtySixED_20700347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17953079747549) ^ 8976539873774 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 17953079747549) ^ 1632098158868 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 17953079747549) ^ 780568684676 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 17953079747549) ^ 20948751164 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 17953079747549) ^ 867284 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_18623584817213 : Nat.Prime 18623584817213 := by
  apply lucas_primality 18623584817213 (2 : ZMod 18623584817213)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1129, 1), (4123911607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1129, 1), (4123911607, 1)] : List FactorBlock).map factorBlockValue).prod) = 18623584817213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_1129
      · exact prime_oneHundredThirtySixED_4123911607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 18623584817213) ^ 9311792408606 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 18623584817213) ^ 16495646428 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 18623584817213) ^ 4516 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_20148333019621 : Nat.Prime 20148333019621 := by
  apply lucas_primality 20148333019621 (10 : ZMod 20148333019621)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 1), (19, 1), (1359536641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 1), (19, 1), (1359536641, 1)] : List FactorBlock).map factorBlockValue).prod) = 20148333019621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_13
      · exact prime_oneHundredThirtySixED_19
      · exact prime_oneHundredThirtySixED_1359536641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 20148333019621) ^ 10074166509810 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (10 : ZMod 20148333019621) ^ 6716111006540 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (10 : ZMod 20148333019621) ^ 4029666603924 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (10 : ZMod 20148333019621) ^ 1549871770740 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (10 : ZMod 20148333019621) ^ 1060438579980 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (10 : ZMod 20148333019621) ^ 14820 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_21270579382193 : Nat.Prime 21270579382193 := by
  apply lucas_primality 21270579382193 (3 : ZMod 21270579382193)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (6689, 1), (28392269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (6689, 1), (28392269, 1)] : List FactorBlock).map factorBlockValue).prod) = 21270579382193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_6689
      · exact prime_oneHundredThirtySixED_28392269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 21270579382193) ^ 10635289691096 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 21270579382193) ^ 3038654197456 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 21270579382193) ^ 3179934128 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 21270579382193) ^ 749168 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_25177653722483 : Nat.Prime 25177653722483 := by
  apply lucas_primality 25177653722483 (2 : ZMod 25177653722483)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12588826861241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12588826861241, 1)] : List FactorBlock).map factorBlockValue).prod) = 25177653722483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_12588826861241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 25177653722483) ^ 12588826861241 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 25177653722483) ^ 2 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_25865890057849 : Nat.Prime 25865890057849 := by
  apply lucas_primality 25865890057849 (11 : ZMod 25865890057849)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (223, 1), (4832939099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (223, 1), (4832939099, 1)] : List FactorBlock).map factorBlockValue).prod) = 25865890057849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_223
      · exact prime_oneHundredThirtySixED_4832939099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 25865890057849) ^ 12932945028924 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (11 : ZMod 25865890057849) ^ 8621963352616 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (11 : ZMod 25865890057849) ^ 115990538376 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (11 : ZMod 25865890057849) ^ 5352 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_30722356172369 : Nat.Prime 30722356172369 := by
  apply lucas_primality 30722356172369 (3 : ZMod 30722356172369)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (17, 1), (16135691267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (17, 1), (16135691267, 1)] : List FactorBlock).map factorBlockValue).prod) = 30722356172369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_17
      · exact prime_oneHundredThirtySixED_16135691267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 30722356172369) ^ 15361178086184 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 30722356172369) ^ 4388908024624 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 30722356172369) ^ 1807197421904 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 30722356172369) ^ 1904 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_38879198473417 : Nat.Prime 38879198473417 := by
  apply lucas_primality 38879198473417 (5 : ZMod 38879198473417)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (19, 1), (71, 1), (1091, 1), (157243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (19, 1), (71, 1), (1091, 1), (157243, 1)] : List FactorBlock).map factorBlockValue).prod) = 38879198473417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_19
      · exact prime_oneHundredThirtySixED_71
      · exact prime_oneHundredThirtySixED_1091
      · exact prime_oneHundredThirtySixED_157243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 38879198473417) ^ 19439599236708 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 38879198473417) ^ 12959732824472 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 38879198473417) ^ 5554171210488 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 38879198473417) ^ 2046273603864 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 38879198473417) ^ 547594344696 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 38879198473417) ^ 35636295576 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 38879198473417) ^ 247255512 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_40604292994541 : Nat.Prime 40604292994541 := by
  apply lucas_primality 40604292994541 (10 : ZMod 40604292994541)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (184564968157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (184564968157, 1)] : List FactorBlock).map factorBlockValue).prod) = 40604292994541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_11
      · exact prime_oneHundredThirtySixED_184564968157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 40604292994541) ^ 20302146497270 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (10 : ZMod 40604292994541) ^ 8120858598908 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (10 : ZMod 40604292994541) ^ 3691299363140 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (10 : ZMod 40604292994541) ^ 220 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_42301424132491 : Nat.Prime 42301424132491 := by
  apply lucas_primality 42301424132491 (2 : ZMod 42301424132491)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (31, 1), (37201, 1), (1222693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (31, 1), (37201, 1), (1222693, 1)] : List FactorBlock).map factorBlockValue).prod) = 42301424132491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_31
      · exact prime_oneHundredThirtySixED_37201
      · exact prime_oneHundredThirtySixED_1222693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 42301424132491) ^ 21150712066245 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 42301424132491) ^ 14100474710830 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 42301424132491) ^ 8460284826498 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 42301424132491) ^ 1364562068790 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 42301424132491) ^ 1137104490 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 42301424132491) ^ 34596930 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_52015694269601 : Nat.Prime 52015694269601 := by
  apply lucas_primality 52015694269601 (3 : ZMod 52015694269601)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 2), (31, 1), (2097407027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 2), (31, 1), (2097407027, 1)] : List FactorBlock).map factorBlockValue).prod) = 52015694269601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_31
      · exact prime_oneHundredThirtySixED_2097407027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 52015694269601) ^ 26007847134800 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 52015694269601) ^ 10403138853920 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 52015694269601) ^ 1677925621600 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 52015694269601) ^ 24800 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_70821871181927 : Nat.Prime 70821871181927 := by
  apply lucas_primality 70821871181927 (5 : ZMod 70821871181927)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3581, 1), (5153, 1), (1918991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3581, 1), (5153, 1), (1918991, 1)] : List FactorBlock).map factorBlockValue).prod) = 70821871181927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3581
      · exact prime_oneHundredThirtySixED_5153
      · exact prime_oneHundredThirtySixED_1918991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 70821871181927) ^ 35410935590963 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 70821871181927) ^ 19777121246 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 70821871181927) ^ 13743813542 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 70821871181927) ^ 36905786 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_81789266816573 : Nat.Prime 81789266816573 := by
  apply lucas_primality 81789266816573 (2 : ZMod 81789266816573)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (2921045243449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (2921045243449, 1)] : List FactorBlock).map factorBlockValue).prod) = 81789266816573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_2921045243449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 81789266816573) ^ 40894633408286 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 81789266816573) ^ 11684180973796 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 81789266816573) ^ 28 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_108859380612443 : Nat.Prime 108859380612443 := by
  apply lucas_primality 108859380612443 (2 : ZMod 108859380612443)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (1237619, 1), (1418689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (1237619, 1), (1418689, 1)] : List FactorBlock).map factorBlockValue).prod) = 108859380612443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_31
      · exact prime_oneHundredThirtySixED_1237619
      · exact prime_oneHundredThirtySixED_1418689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 108859380612443) ^ 54429690306221 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 108859380612443) ^ 3511592922982 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 108859380612443) ^ 87958718 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 108859380612443) ^ 76732378 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_119844926442239 : Nat.Prime 119844926442239 := by
  apply lucas_primality 119844926442239 (11 : ZMod 119844926442239)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (4423, 1), (467169757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (4423, 1), (467169757, 1)] : List FactorBlock).map factorBlockValue).prod) = 119844926442239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_29
      · exact prime_oneHundredThirtySixED_4423
      · exact prime_oneHundredThirtySixED_467169757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 119844926442239) ^ 59922463221119 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (11 : ZMod 119844926442239) ^ 4132583670422 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (11 : ZMod 119844926442239) ^ 27095845906 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (11 : ZMod 119844926442239) ^ 256534 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_129985840728413 : Nat.Prime 129985840728413 := by
  apply lucas_primality 129985840728413 (2 : ZMod 129985840728413)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (251, 1), (3079, 1), (42048707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (251, 1), (3079, 1), (42048707, 1)] : List FactorBlock).map factorBlockValue).prod) = 129985840728413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_251
      · exact prime_oneHundredThirtySixED_3079
      · exact prime_oneHundredThirtySixED_42048707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 129985840728413) ^ 64992920364206 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 129985840728413) ^ 517871875412 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 129985840728413) ^ 42216901828 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 129985840728413) ^ 3091316 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_171036973802353 : Nat.Prime 171036973802353 := by
  apply lucas_primality 171036973802353 (10 : ZMod 171036973802353)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (61, 1), (4507, 1), (1851541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (61, 1), (4507, 1), (1851541, 1)] : List FactorBlock).map factorBlockValue).prod) = 171036973802353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_61
      · exact prime_oneHundredThirtySixED_4507
      · exact prime_oneHundredThirtySixED_1851541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 171036973802353) ^ 85518486901176 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (10 : ZMod 171036973802353) ^ 57012324600784 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (10 : ZMod 171036973802353) ^ 24433853400336 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (10 : ZMod 171036973802353) ^ 2803884816432 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (10 : ZMod 171036973802353) ^ 37949184336 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (10 : ZMod 171036973802353) ^ 92375472 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_248492743638439 : Nat.Prime 248492743638439 := by
  apply lucas_primality 248492743638439 (3 : ZMod 248492743638439)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (23, 1), (138513235027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (23, 1), (138513235027, 1)] : List FactorBlock).map factorBlockValue).prod) = 248492743638439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_13
      · exact prime_oneHundredThirtySixED_23
      · exact prime_oneHundredThirtySixED_138513235027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 248492743638439) ^ 124246371819219 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 248492743638439) ^ 82830914546146 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 248492743638439) ^ 19114826433726 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 248492743638439) ^ 10804032332106 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 248492743638439) ^ 1794 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_258862483991359 : Nat.Prime 258862483991359 := by
  apply lucas_primality 258862483991359 (6 : ZMod 258862483991359)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (10789, 1), (102534983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (10789, 1), (102534983, 1)] : List FactorBlock).map factorBlockValue).prod) = 258862483991359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_13
      · exact prime_oneHundredThirtySixED_10789
      · exact prime_oneHundredThirtySixED_102534983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 258862483991359) ^ 129431241995679 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 86287494663786 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 19912498768566 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 23993186022 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 2524626 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_273515612853037 : Nat.Prime 273515612853037 := by
  apply lucas_primality 273515612853037 (5 : ZMod 273515612853037)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1153, 1), (32233, 1), (613297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1153, 1), (32233, 1), (613297, 1)] : List FactorBlock).map factorBlockValue).prod) = 273515612853037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_1153
      · exact prime_oneHundredThirtySixED_32233
      · exact prime_oneHundredThirtySixED_613297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 273515612853037) ^ 136757806426518 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 273515612853037) ^ 91171870951012 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 273515612853037) ^ 237220826412 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 273515612853037) ^ 8485577292 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 273515612853037) ^ 445975788 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_301916280394081 : Nat.Prime 301916280394081 := by
  apply lucas_primality 301916280394081 (7 : ZMod 301916280394081)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 1), (11, 1), (5023, 1), (1264873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 1), (11, 1), (5023, 1), (1264873, 1)] : List FactorBlock).map factorBlockValue).prod) = 301916280394081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_11
      · exact prime_oneHundredThirtySixED_5023
      · exact prime_oneHundredThirtySixED_1264873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 301916280394081) ^ 150958140197040 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 301916280394081) ^ 100638760131360 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 301916280394081) ^ 60383256078816 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 301916280394081) ^ 27446934581280 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 301916280394081) ^ 60106764960 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 301916280394081) ^ 238692960 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_361790716440337 : Nat.Prime 361790716440337 := by
  apply lucas_primality 361790716440337 (5 : ZMod 361790716440337)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (67, 1), (28607, 1), (3932503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (67, 1), (28607, 1), (3932503, 1)] : List FactorBlock).map factorBlockValue).prod) = 361790716440337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_67
      · exact prime_oneHundredThirtySixED_28607
      · exact prime_oneHundredThirtySixED_3932503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 361790716440337) ^ 180895358220168 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 361790716440337) ^ 120596905480112 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 361790716440337) ^ 5399861439408 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 361790716440337) ^ 12646929648 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 361790716440337) ^ 92000112 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_542733195323689 : Nat.Prime 542733195323689 := by
  apply lucas_primality 542733195323689 (7 : ZMod 542733195323689)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 2), (23, 1), (3402118721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 2), (23, 1), (3402118721, 1)] : List FactorBlock).map factorBlockValue).prod) = 542733195323689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_17
      · exact prime_oneHundredThirtySixED_23
      · exact prime_oneHundredThirtySixED_3402118721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 542733195323689) ^ 271366597661844 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 542733195323689) ^ 180911065107896 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 542733195323689) ^ 31925482077864 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 542733195323689) ^ 23597095448856 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 542733195323689) ^ 159528 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_777594629002747 : Nat.Prime 777594629002747 := by
  apply lucas_primality 777594629002747 (2 : ZMod 777594629002747)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (9491, 1), (440482171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (9491, 1), (440482171, 1)] : List FactorBlock).map factorBlockValue).prod) = 777594629002747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_31
      · exact prime_oneHundredThirtySixED_9491
      · exact prime_oneHundredThirtySixED_440482171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 777594629002747) ^ 388797314501373 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 777594629002747) ^ 259198209667582 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 777594629002747) ^ 25083697709766 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 777594629002747) ^ 81929683806 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 777594629002747) ^ 1765326 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_866934580455847 : Nat.Prime 866934580455847 := by
  apply lucas_primality 866934580455847 (3 : ZMod 866934580455847)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (6880433178221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (6880433178221, 1)] : List FactorBlock).map factorBlockValue).prod) = 866934580455847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_6880433178221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 866934580455847) ^ 433467290227923 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 866934580455847) ^ 288978193485282 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 866934580455847) ^ 123847797207978 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 866934580455847) ^ 126 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_996610072199803 : Nat.Prime 996610072199803 := by
  apply lucas_primality 996610072199803 (2 : ZMod 996610072199803)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (9770686982351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (9770686982351, 1)] : List FactorBlock).map factorBlockValue).prod) = 996610072199803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_17
      · exact prime_oneHundredThirtySixED_9770686982351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 996610072199803) ^ 498305036099901 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 996610072199803) ^ 332203357399934 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 996610072199803) ^ 58624121894106 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 996610072199803) ^ 102 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_1291737826932829 : Nat.Prime 1291737826932829 := by
  apply lucas_primality 1291737826932829 (2 : ZMod 1291737826932829)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (9785892628279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (9785892628279, 1)] : List FactorBlock).map factorBlockValue).prod) = 1291737826932829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_11
      · exact prime_oneHundredThirtySixED_9785892628279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1291737826932829) ^ 645868913466414 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1291737826932829) ^ 430579275644276 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1291737826932829) ^ 117430711539348 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1291737826932829) ^ 132 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_1328927666859929 : Nat.Prime 1328927666859929 := by
  apply lucas_primality 1328927666859929 (3 : ZMod 1328927666859929)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (89, 1), (179, 1), (467, 1), (1933, 1), (11551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (89, 1), (179, 1), (467, 1), (1933, 1), (11551, 1)] : List FactorBlock).map factorBlockValue).prod) = 1328927666859929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_89
      · exact prime_oneHundredThirtySixED_179
      · exact prime_oneHundredThirtySixED_467
      · exact prime_oneHundredThirtySixED_1933
      · exact prime_oneHundredThirtySixED_11551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1328927666859929) ^ 664463833429964 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1328927666859929) ^ 14931771537752 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1328927666859929) ^ 7424176909832 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1328927666859929) ^ 2845669522184 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1328927666859929) ^ 687494913016 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1328927666859929) ^ 115048711528 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_2336824753242557 : Nat.Prime 2336824753242557 := by
  apply lucas_primality 2336824753242557 (2 : ZMod 2336824753242557)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (241, 1), (74219, 1), (32661341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (241, 1), (74219, 1), (32661341, 1)] : List FactorBlock).map factorBlockValue).prod) = 2336824753242557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_241
      · exact prime_oneHundredThirtySixED_74219
      · exact prime_oneHundredThirtySixED_32661341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2336824753242557) ^ 1168412376621278 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2336824753242557) ^ 9696368270716 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2336824753242557) ^ 31485532724 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2336824753242557) ^ 71547116 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_2642915032645219 : Nat.Prime 2642915032645219 := by
  apply lucas_primality 2642915032645219 (2 : ZMod 2642915032645219)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (109, 1), (4041154484167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (109, 1), (4041154484167, 1)] : List FactorBlock).map factorBlockValue).prod) = 2642915032645219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_109
      · exact prime_oneHundredThirtySixED_4041154484167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2642915032645219) ^ 1321457516322609 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2642915032645219) ^ 880971677548406 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2642915032645219) ^ 24246926905002 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2642915032645219) ^ 654 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_3537434893525811 : Nat.Prime 3537434893525811 := by
  apply lucas_primality 3537434893525811 (2 : ZMod 3537434893525811)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (107, 1), (593, 1), (24551, 1), (227081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (107, 1), (593, 1), (24551, 1), (227081, 1)] : List FactorBlock).map factorBlockValue).prod) = 3537434893525811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_107
      · exact prime_oneHundredThirtySixED_593
      · exact prime_oneHundredThirtySixED_24551
      · exact prime_oneHundredThirtySixED_227081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3537434893525811) ^ 1768717446762905 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3537434893525811) ^ 707486978705162 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3537434893525811) ^ 33060139191830 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3537434893525811) ^ 5965320225170 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3537434893525811) ^ 144085165310 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3537434893525811) ^ 15577855010 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_4135586703206347 : Nat.Prime 4135586703206347 := by
  apply lucas_primality 4135586703206347 (2 : ZMod 4135586703206347)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (83537, 1), (2750335981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (83537, 1), (2750335981, 1)] : List FactorBlock).map factorBlockValue).prod) = 4135586703206347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_83537
      · exact prime_oneHundredThirtySixED_2750335981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4135586703206347) ^ 2067793351603173 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4135586703206347) ^ 1378528901068782 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4135586703206347) ^ 49506047658 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4135586703206347) ^ 1503666 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_4931749931514223 : Nat.Prime 4931749931514223 := by
  apply lucas_primality 4931749931514223 (6 : ZMod 4931749931514223)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1693987, 1), (485221151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1693987, 1), (485221151, 1)] : List FactorBlock).map factorBlockValue).prod) = 4931749931514223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_1693987
      · exact prime_oneHundredThirtySixED_485221151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 4931749931514223) ^ 2465874965757111 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 4931749931514223) ^ 1643916643838074 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 4931749931514223) ^ 2911326906 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 4931749931514223) ^ 10163922 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_5410643371526969 : Nat.Prime 5410643371526969 := by
  apply lucas_primality 5410643371526969 (3 : ZMod 5410643371526969)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (37, 1), (15739, 1), (1161395297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (37, 1), (15739, 1), (1161395297, 1)] : List FactorBlock).map factorBlockValue).prod) = 5410643371526969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_37
      · exact prime_oneHundredThirtySixED_15739
      · exact prime_oneHundredThirtySixED_1161395297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5410643371526969) ^ 2705321685763484 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 5410643371526969) ^ 146233604635864 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 5410643371526969) ^ 343773007912 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 5410643371526969) ^ 4658744 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_7270207559318861 : Nat.Prime 7270207559318861 := by
  apply lucas_primality 7270207559318861 (2 : ZMod 7270207559318861)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 2), (3253, 1), (661220099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 2), (3253, 1), (661220099, 1)] : List FactorBlock).map factorBlockValue).prod) = 7270207559318861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_13
      · exact prime_oneHundredThirtySixED_3253
      · exact prime_oneHundredThirtySixED_661220099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7270207559318861) ^ 3635103779659430 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7270207559318861) ^ 1454041511863772 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7270207559318861) ^ 559246735332220 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7270207559318861) ^ 2234923934620 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 7270207559318861) ^ 10995140 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_10771847848529401 : Nat.Prime 10771847848529401 := by
  apply lucas_primality 10771847848529401 (17 : ZMod 10771847848529401)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (17953079747549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (17953079747549, 1)] : List FactorBlock).map factorBlockValue).prod) = 10771847848529401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_17953079747549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 10771847848529401) ^ 5385923924264700 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (17 : ZMod 10771847848529401) ^ 3590615949509800 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (17 : ZMod 10771847848529401) ^ 2154369569705880 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (17 : ZMod 10771847848529401) ^ 600 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_10821286743053939 : Nat.Prime 10821286743053939 := by
  apply lucas_primality 10821286743053939 (2 : ZMod 10821286743053939)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5410643371526969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5410643371526969, 1)] : List FactorBlock).map factorBlockValue).prod) = 10821286743053939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5410643371526969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 10821286743053939) ^ 5410643371526969 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 10821286743053939) ^ 2 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_11386144570981007 : Nat.Prime 11386144570981007 := by
  apply lucas_primality 11386144570981007 (5 : ZMod 11386144570981007)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (131, 1), (68903, 1), (21748999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (131, 1), (68903, 1), (21748999, 1)] : List FactorBlock).map factorBlockValue).prod) = 11386144570981007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_29
      · exact prime_oneHundredThirtySixED_131
      · exact prime_oneHundredThirtySixED_68903
      · exact prime_oneHundredThirtySixED_21748999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 11386144570981007) ^ 5693072285490503 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 11386144570981007) ^ 392625674861414 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 11386144570981007) ^ 86917134129626 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 11386144570981007) ^ 165248894402 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 11386144570981007) ^ 523524994 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_13859455535240563 : Nat.Prime 13859455535240563 := by
  apply lucas_primality 13859455535240563 (2 : ZMod 13859455535240563)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (37, 1), (157, 1), (10195979077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (37, 1), (157, 1), (10195979077, 1)] : List FactorBlock).map factorBlockValue).prod) = 13859455535240563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_13
      · exact prime_oneHundredThirtySixED_37
      · exact prime_oneHundredThirtySixED_157
      · exact prime_oneHundredThirtySixED_10195979077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13859455535240563) ^ 6929727767620281 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 13859455535240563) ^ 4619818511746854 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 13859455535240563) ^ 1066111964249274 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 13859455535240563) ^ 374579879330826 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 13859455535240563) ^ 88276786848666 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 13859455535240563) ^ 1359306 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_17199000483384449 : Nat.Prime 17199000483384449 := by
  apply lucas_primality 17199000483384449 (3 : ZMod 17199000483384449)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (614279, 1), (218739679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (614279, 1), (218739679, 1)] : List FactorBlock).map factorBlockValue).prod) = 17199000483384449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_614279
      · exact prime_oneHundredThirtySixED_218739679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 17199000483384449) ^ 8599500241692224 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 17199000483384449) ^ 27998678912 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 17199000483384449) ^ 78627712 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_33884742454793303 : Nat.Prime 33884742454793303 := by
  apply lucas_primality 33884742454793303 (5 : ZMod 33884742454793303)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (996610072199803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (996610072199803, 1)] : List FactorBlock).map factorBlockValue).prod) = 33884742454793303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_17
      · exact prime_oneHundredThirtySixED_996610072199803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 33884742454793303) ^ 16942371227396651 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 33884742454793303) ^ 1993220144399606 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 33884742454793303) ^ 34 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_37051420944511243 : Nat.Prime 37051420944511243 := by
  apply lucas_primality 37051420944511243 (3 : ZMod 37051420944511243)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (131, 1), (170603, 1), (92103133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (131, 1), (170603, 1), (92103133, 1)] : List FactorBlock).map factorBlockValue).prod) = 37051420944511243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_131
      · exact prime_oneHundredThirtySixED_170603
      · exact prime_oneHundredThirtySixED_92103133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 37051420944511243) ^ 18525710472255621 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 37051420944511243) ^ 12350473648170414 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 37051420944511243) ^ 282835274385582 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 37051420944511243) ^ 217179187614 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 37051420944511243) ^ 402281874 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_39739808160661181 : Nat.Prime 39739808160661181 := by
  apply lucas_primality 39739808160661181 (7 : ZMod 39739808160661181)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (13, 1), (17, 1), (1669, 1), (4637, 1), (105613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (13, 1), (17, 1), (1669, 1), (4637, 1), (105613, 1)] : List FactorBlock).map factorBlockValue).prod) = 39739808160661181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_11
      · exact prime_oneHundredThirtySixED_13
      · exact prime_oneHundredThirtySixED_17
      · exact prime_oneHundredThirtySixED_1669
      · exact prime_oneHundredThirtySixED_4637
      · exact prime_oneHundredThirtySixED_105613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 39739808160661181) ^ 19869904080330590 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 39739808160661181) ^ 7947961632132236 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 39739808160661181) ^ 3612709832787380 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 39739808160661181) ^ 3056908320050860 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 39739808160661181) ^ 2337635774156540 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 39739808160661181) ^ 23810550126220 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 39739808160661181) ^ 8570154876140 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 39739808160661181) ^ 376277618860 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_70075919093336591 : Nat.Prime 70075919093336591 := by
  apply lucas_primality 70075919093336591 (14 : ZMod 70075919093336591)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (31, 1), (24841, 1), (1299989947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (31, 1), (24841, 1), (1299989947, 1)] : List FactorBlock).map factorBlockValue).prod) = 70075919093336591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_31
      · exact prime_oneHundredThirtySixED_24841
      · exact prime_oneHundredThirtySixED_1299989947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 70075919093336591) ^ 35037959546668295 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 14015183818667318 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 10010845584762370 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 2260513519139890 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 2820978184990 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 53904970 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_85506511358660377 : Nat.Prime 85506511358660377 := by
  apply lucas_primality 85506511358660377 (5 : ZMod 85506511358660377)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (29, 1), (53, 1), (2318003452577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (29, 1), (53, 1), (2318003452577, 1)] : List FactorBlock).map factorBlockValue).prod) = 85506511358660377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_29
      · exact prime_oneHundredThirtySixED_53
      · exact prime_oneHundredThirtySixED_2318003452577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 85506511358660377) ^ 42753255679330188 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 85506511358660377) ^ 28502170452886792 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 85506511358660377) ^ 2948500391677944 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 85506511358660377) ^ 1613330402993592 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 85506511358660377) ^ 36888 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_123502803087987373 : Nat.Prime 123502803087987373 := by
  apply lucas_primality 123502803087987373 (5 : ZMod 123502803087987373)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (3727, 1), (21067, 1), (18725587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (3727, 1), (21067, 1), (18725587, 1)] : List FactorBlock).map factorBlockValue).prod) = 123502803087987373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_3727
      · exact prime_oneHundredThirtySixED_21067
      · exact prime_oneHundredThirtySixED_18725587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 123502803087987373) ^ 61751401543993686 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 123502803087987373) ^ 41167601029329124 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 123502803087987373) ^ 17643257583998196 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 123502803087987373) ^ 33137323071636 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 123502803087987373) ^ 5862382070916 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 123502803087987373) ^ 6595403556 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_144034804976325343 : Nat.Prime 144034804976325343 := by
  apply lucas_primality 144034804976325343 (3 : ZMod 144034804976325343)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1289, 1), (18623584817213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1289, 1), (18623584817213, 1)] : List FactorBlock).map factorBlockValue).prod) = 144034804976325343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_1289
      · exact prime_oneHundredThirtySixED_18623584817213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 144034804976325343) ^ 72017402488162671 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 144034804976325343) ^ 48011601658775114 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 144034804976325343) ^ 111741508903278 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 144034804976325343) ^ 7734 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_245873436519459197 : Nat.Prime 245873436519459197 := by
  apply lucas_primality 245873436519459197 (2 : ZMod 245873436519459197)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 3), (73, 1), (83, 1), (1867, 1), (15842081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 3), (73, 1), (83, 1), (1867, 1), (15842081, 1)] : List FactorBlock).map factorBlockValue).prod) = 245873436519459197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_73
      · exact prime_oneHundredThirtySixED_83
      · exact prime_oneHundredThirtySixED_1867
      · exact prime_oneHundredThirtySixED_15842081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 245873436519459197) ^ 122936718259729598 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 245873436519459197) ^ 35124776645637028 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 245873436519459197) ^ 3368129267389852 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 245873436519459197) ^ 2962330560475412 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 245873436519459197) ^ 131694395564788 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 245873436519459197) ^ 15520273916 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_343207110292651133 : Nat.Prime 343207110292651133 := by
  apply lucas_primality 343207110292651133 (2 : ZMod 343207110292651133)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (41, 1), (373, 1), (510047838721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (41, 1), (373, 1), (510047838721, 1)] : List FactorBlock).map factorBlockValue).prod) = 343207110292651133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_11
      · exact prime_oneHundredThirtySixED_41
      · exact prime_oneHundredThirtySixED_373
      · exact prime_oneHundredThirtySixED_510047838721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 343207110292651133) ^ 171603555146325566 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 343207110292651133) ^ 31200646390241012 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 343207110292651133) ^ 8370905129089052 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 343207110292651133) ^ 920126301052684 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 343207110292651133) ^ 672892 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_464464324697673533 : Nat.Prime 464464324697673533 := by
  apply lucas_primality 464464324697673533 (2 : ZMod 464464324697673533)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (28591, 1), (109987, 1), (36925099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (28591, 1), (109987, 1), (36925099, 1)] : List FactorBlock).map factorBlockValue).prod) = 464464324697673533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_28591
      · exact prime_oneHundredThirtySixED_109987
      · exact prime_oneHundredThirtySixED_36925099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 464464324697673533) ^ 232232162348836766 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 464464324697673533) ^ 16245123454852 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 464464324697673533) ^ 4222902022036 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 464464324697673533) ^ 12578553268 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_819763689963477131 : Nat.Prime 819763689963477131 := by
  apply lucas_primality 819763689963477131 (2 : ZMod 819763689963477131)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (47, 1), (6997457, 1), (249258847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (47, 1), (6997457, 1), (249258847, 1)] : List FactorBlock).map factorBlockValue).prod) = 819763689963477131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_47
      · exact prime_oneHundredThirtySixED_6997457
      · exact prime_oneHundredThirtySixED_249258847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 819763689963477131) ^ 409881844981738565 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 819763689963477131) ^ 163952737992695426 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 819763689963477131) ^ 17441780637520790 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 819763689963477131) ^ 117151658090 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 819763689963477131) ^ 3288804790 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_951498532749386893 : Nat.Prime 951498532749386893 := by
  apply lucas_primality 951498532749386893 (2 : ZMod 951498532749386893)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (41, 1), (546151, 1), (3541035551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (41, 1), (546151, 1), (3541035551, 1)] : List FactorBlock).map factorBlockValue).prod) = 951498532749386893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_41
      · exact prime_oneHundredThirtySixED_546151
      · exact prime_oneHundredThirtySixED_3541035551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 951498532749386893) ^ 475749266374693446 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 951498532749386893) ^ 317166177583128964 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 951498532749386893) ^ 23207281286570412 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 951498532749386893) ^ 1742189491092 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 951498532749386893) ^ 268706292 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_968990184323152991 : Nat.Prime 968990184323152991 := by
  apply lucas_primality 968990184323152991 (37 : ZMod 968990184323152991)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (97, 1), (549019, 1), (79110191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (97, 1), (549019, 1), (79110191, 1)] : List FactorBlock).map factorBlockValue).prod) = 968990184323152991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_23
      · exact prime_oneHundredThirtySixED_97
      · exact prime_oneHundredThirtySixED_549019
      · exact prime_oneHundredThirtySixED_79110191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (37 : ZMod 968990184323152991) ^ 484495092161576495 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (37 : ZMod 968990184323152991) ^ 193798036864630598 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (37 : ZMod 968990184323152991) ^ 42130008014050130 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (37 : ZMod 968990184323152991) ^ 9989589529104670 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (37 : ZMod 968990184323152991) ^ 1764948361210 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (37 : ZMod 968990184323152991) ^ 12248613890 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_1142102489347470943 : Nat.Prime 1142102489347470943 := by
  apply lucas_primality 1142102489347470943 (3 : ZMod 1142102489347470943)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (157, 1), (21270579382193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (157, 1), (21270579382193, 1)] : List FactorBlock).map factorBlockValue).prod) = 1142102489347470943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_19
      · exact prime_oneHundredThirtySixED_157
      · exact prime_oneHundredThirtySixED_21270579382193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1142102489347470943) ^ 571051244673735471 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1142102489347470943) ^ 380700829782490314 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1142102489347470943) ^ 60110657334077418 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1142102489347470943) ^ 7274538148710006 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1142102489347470943) ^ 53694 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_2220502305087140441 : Nat.Prime 2220502305087140441 := by
  apply lucas_primality 2220502305087140441 (3 : ZMod 2220502305087140441)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2220502305087140441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_101
      · exact prime_oneHundredThirtySixED_191
      · exact prime_oneHundredThirtySixED_48017
      · exact prime_oneHundredThirtySixED_59929613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2220502305087140441) ^ 1110251152543570220 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 444100461017428088 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 21985171337496440 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 11625666518780840 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 46244086575320 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 37051837880 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_2656574897467719719 : Nat.Prime 2656574897467719719 := by
  apply lucas_primality 2656574897467719719 (7 : ZMod 2656574897467719719)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (37, 1), (42323, 1), (121175790187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (37, 1), (42323, 1), (121175790187, 1)] : List FactorBlock).map factorBlockValue).prod) = 2656574897467719719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_37
      · exact prime_oneHundredThirtySixED_42323
      · exact prime_oneHundredThirtySixED_121175790187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2656574897467719719) ^ 1328287448733859859 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 2656574897467719719) ^ 379510699638245674 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 2656574897467719719) ^ 71799321553181614 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 2656574897467719719) ^ 62769059316866 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 2656574897467719719) ^ 21923314 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_3128891451364766141 : Nat.Prime 3128891451364766141 := by
  apply lucas_primality 3128891451364766141 (2 : ZMod 3128891451364766141)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (359, 1), (419, 1), (1040044758167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (359, 1), (419, 1), (1040044758167, 1)] : List FactorBlock).map factorBlockValue).prod) = 3128891451364766141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_359
      · exact prime_oneHundredThirtySixED_419
      · exact prime_oneHundredThirtySixED_1040044758167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3128891451364766141) ^ 1564445725682383070 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3128891451364766141) ^ 625778290272953228 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3128891451364766141) ^ 8715575073439460 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3128891451364766141) ^ 7467521363639060 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3128891451364766141) ^ 3008420 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_3503795954666829551 : Nat.Prime 3503795954666829551 := by
  apply lucas_primality 3503795954666829551 (13 : ZMod 3503795954666829551)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (70075919093336591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (70075919093336591, 1)] : List FactorBlock).map factorBlockValue).prod) = 3503795954666829551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_70075919093336591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 3503795954666829551) ^ 1751897977333414775 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (13 : ZMod 3503795954666829551) ^ 700759190933365910 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (13 : ZMod 3503795954666829551) ^ 50 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_6884584512019465129 : Nat.Prime 6884584512019465129 := by
  apply lucas_primality 6884584512019465129 (11 : ZMod 6884584512019465129)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2437, 1), (226001, 1), (520835531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2437, 1), (226001, 1), (520835531, 1)] : List FactorBlock).map factorBlockValue).prod) = 6884584512019465129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_2437
      · exact prime_oneHundredThirtySixED_226001
      · exact prime_oneHundredThirtySixED_520835531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 6884584512019465129) ^ 3442292256009732564 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (11 : ZMod 6884584512019465129) ^ 2294861504006488376 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (11 : ZMod 6884584512019465129) ^ 2825024420196744 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (11 : ZMod 6884584512019465129) ^ 30462628537128 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (11 : ZMod 6884584512019465129) ^ 13218346488 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_10281858113958598067 : Nat.Prime 10281858113958598067 := by
  apply lucas_primality 10281858113958598067 (2 : ZMod 10281858113958598067)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (4597027, 1), (48622436773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (4597027, 1), (48622436773, 1)] : List FactorBlock).map factorBlockValue).prod) = 10281858113958598067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_23
      · exact prime_oneHundredThirtySixED_4597027
      · exact prime_oneHundredThirtySixED_48622436773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10281858113958598067) ^ 5140929056979299033 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 10281858113958598067) ^ 447037309302547742 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 10281858113958598067) ^ 2236632091558 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 10281858113958598067) ^ 211463242 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_12027856749917614883 : Nat.Prime 12027856749917614883 := by
  apply lucas_primality 12027856749917614883 (2 : ZMod 12027856749917614883)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2903, 1), (20107, 1), (103030056421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2903, 1), (20107, 1), (103030056421, 1)] : List FactorBlock).map factorBlockValue).prod) = 12027856749917614883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_2903
      · exact prime_oneHundredThirtySixED_20107
      · exact prime_oneHundredThirtySixED_103030056421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 12027856749917614883) ^ 6013928374958807441 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 12027856749917614883) ^ 4143250688914094 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 12027856749917614883) ^ 598192507580326 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 12027856749917614883) ^ 116741242 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_12123193775820152411 : Nat.Prime 12123193775820152411 := by
  apply lucas_primality 12123193775820152411 (2 : ZMod 12123193775820152411)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (11, 2), (5990311, 1), (238937473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (11, 2), (5990311, 1), (238937473, 1)] : List FactorBlock).map factorBlockValue).prod) = 12123193775820152411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_11
      · exact prime_oneHundredThirtySixED_5990311
      · exact prime_oneHundredThirtySixED_238937473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12123193775820152411) ^ 6061596887910076205 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 12123193775820152411) ^ 2424638755164030482 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 12123193775820152411) ^ 1731884825117164630 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 12123193775820152411) ^ 1102108525074559310 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 12123193775820152411) ^ 2023800396310 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 12123193775820152411) ^ 50737934170 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_15139880605354301861 : Nat.Prime 15139880605354301861 := by
  apply lucas_primality 15139880605354301861 (2 : ZMod 15139880605354301861)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (19, 1), (2647, 1), (2150239681943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (19, 1), (2647, 1), (2150239681943, 1)] : List FactorBlock).map factorBlockValue).prod) = 15139880605354301861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_19
      · exact prime_oneHundredThirtySixED_2647
      · exact prime_oneHundredThirtySixED_2150239681943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15139880605354301861) ^ 7569940302677150930 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 15139880605354301861) ^ 3027976121070860372 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 15139880605354301861) ^ 2162840086479185980 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 15139880605354301861) ^ 796835821334436940 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 15139880605354301861) ^ 5719637553968380 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 15139880605354301861) ^ 7041020 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_15660823346077790081 : Nat.Prime 15660823346077790081 := by
  apply lucas_primality 15660823346077790081 (3 : ZMod 15660823346077790081)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 1), (17, 2), (251, 1), (1621, 1), (13099, 1), (15887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 1), (17, 2), (251, 1), (1621, 1), (13099, 1), (15887, 1)] : List FactorBlock).map factorBlockValue).prod) = 15660823346077790081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_17
      · exact prime_oneHundredThirtySixED_251
      · exact prime_oneHundredThirtySixED_1621
      · exact prime_oneHundredThirtySixED_13099
      · exact prime_oneHundredThirtySixED_15887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 15660823346077790081) ^ 7830411673038895040 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 15660823346077790081) ^ 3132164669215558016 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 15660823346077790081) ^ 921224902710458240 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 15660823346077790081) ^ 62393718510270080 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 15660823346077790081) ^ 9661211194372480 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 15660823346077790081) ^ 1195573963361920 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 15660823346077790081) ^ 985763413235840 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_19379803686463059821 : Nat.Prime 19379803686463059821 := by
  apply lucas_primality 19379803686463059821 (2 : ZMod 19379803686463059821)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (968990184323152991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (968990184323152991, 1)] : List FactorBlock).map factorBlockValue).prod) = 19379803686463059821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_968990184323152991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 19379803686463059821) ^ 9689901843231529910 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 19379803686463059821) ^ 3875960737292611964 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 19379803686463059821) ^ 20 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_19595964807207672119 : Nat.Prime 19595964807207672119 := by
  apply lucas_primality 19595964807207672119 (11 : ZMod 19595964807207672119)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (9392827, 1), (1043134554017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (9392827, 1), (1043134554017, 1)] : List FactorBlock).map factorBlockValue).prod) = 19595964807207672119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_9392827
      · exact prime_oneHundredThirtySixED_1043134554017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 19595964807207672119) ^ 9797982403603836059 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (11 : ZMod 19595964807207672119) ^ 2086269108034 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (11 : ZMod 19595964807207672119) ^ 18785654 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_30147096096777913439 : Nat.Prime 30147096096777913439 := by
  apply lucas_primality 30147096096777913439 (7 : ZMod 30147096096777913439)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (115963, 1), (129985840728413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (115963, 1), (129985840728413, 1)] : List FactorBlock).map factorBlockValue).prod) = 30147096096777913439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_115963
      · exact prime_oneHundredThirtySixED_129985840728413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 30147096096777913439) ^ 15073548048388956719 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 30147096096777913439) ^ 259971681456826 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 30147096096777913439) ^ 231926 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_36724560189401065727 : Nat.Prime 36724560189401065727 := by
  apply lucas_primality 36724560189401065727 (5 : ZMod 36724560189401065727)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (41, 1), (101, 1), (119844926442239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (41, 1), (101, 1), (119844926442239, 1)] : List FactorBlock).map factorBlockValue).prod) = 36724560189401065727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_37
      · exact prime_oneHundredThirtySixED_41
      · exact prime_oneHundredThirtySixED_101
      · exact prime_oneHundredThirtySixED_119844926442239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 36724560189401065727) ^ 18362280094700532863 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 36724560189401065727) ^ 992555680794623398 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 36724560189401065727) ^ 895720980229294286 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 36724560189401065727) ^ 363609506825753126 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 36724560189401065727) ^ 306434 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_48596607568432215373 : Nat.Prime 48596607568432215373 := by
  apply lucas_primality 48596607568432215373 (2 : ZMod 48596607568432215373)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1733, 1), (2336824753242557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1733, 1), (2336824753242557, 1)] : List FactorBlock).map factorBlockValue).prod) = 48596607568432215373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_1733
      · exact prime_oneHundredThirtySixED_2336824753242557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 48596607568432215373) ^ 24298303784216107686 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 48596607568432215373) ^ 16198869189477405124 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 48596607568432215373) ^ 28041897038910684 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 48596607568432215373) ^ 20796 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_54691503679666912193 : Nat.Prime 54691503679666912193 := by
  apply lucas_primality 54691503679666912193 (3 : ZMod 54691503679666912193)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (33941, 1), (25177653722483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (33941, 1), (25177653722483, 1)] : List FactorBlock).map factorBlockValue).prod) = 54691503679666912193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_33941
      · exact prime_oneHundredThirtySixED_25177653722483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 54691503679666912193) ^ 27345751839833456096 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 54691503679666912193) ^ 1611369838238912 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 54691503679666912193) ^ 2172224 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_81022617185474593483 : Nat.Prime 81022617185474593483 := by
  apply lucas_primality 81022617185474593483 (2 : ZMod 81022617185474593483)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (1409, 1), (14221, 1), (57251, 1), (1681639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (1409, 1), (14221, 1), (57251, 1), (1681639, 1)] : List FactorBlock).map factorBlockValue).prod) = 81022617185474593483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_1409
      · exact prime_oneHundredThirtySixED_14221
      · exact prime_oneHundredThirtySixED_57251
      · exact prime_oneHundredThirtySixED_1681639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 81022617185474593483) ^ 40511308592737296741 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 81022617185474593483) ^ 27007539061824864494 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 81022617185474593483) ^ 11574659597924941926 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 81022617185474593483) ^ 57503631785290698 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 81022617185474593483) ^ 5697392390512242 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 81022617185474593483) ^ 1415217501623982 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 81022617185474593483) ^ 48180743420838 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_404215901228104962433 : Nat.Prime 404215901228104962433 := by
  apply lucas_primality 404215901228104962433 (10 : ZMod 404215901228104962433)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (145969, 1), (7211432400817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (145969, 1), (7211432400817, 1)] : List FactorBlock).map factorBlockValue).prod) = 404215901228104962433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_145969
      · exact prime_oneHundredThirtySixED_7211432400817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 404215901228104962433) ^ 202107950614052481216 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (10 : ZMod 404215901228104962433) ^ 134738633742701654144 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (10 : ZMod 404215901228104962433) ^ 2769190041913728 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (10 : ZMod 404215901228104962433) ^ 56052096 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_438730547277022707709 : Nat.Prime 438730547277022707709 := by
  apply lucas_primality 438730547277022707709 (2 : ZMod 438730547277022707709)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (109, 2), (127, 1), (2692262496923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (109, 2), (127, 1), (2692262496923, 1)] : List FactorBlock).map factorBlockValue).prod) = 438730547277022707709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_109
      · exact prime_oneHundredThirtySixED_127
      · exact prime_oneHundredThirtySixED_2692262496923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 438730547277022707709) ^ 219365273638511353854 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 438730547277022707709) ^ 146243515759007569236 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 438730547277022707709) ^ 4025050892449749612 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 438730547277022707709) ^ 3454571238401753604 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 438730547277022707709) ^ 162959796 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_554244401786064875243 : Nat.Prime 554244401786064875243 := by
  apply lucas_primality 554244401786064875243 (2 : ZMod 554244401786064875243)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (31, 2), (15319, 1), (297263, 1), (9046459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (31, 2), (15319, 1), (297263, 1), (9046459, 1)] : List FactorBlock).map factorBlockValue).prod) = 554244401786064875243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_31
      · exact prime_oneHundredThirtySixED_15319
      · exact prime_oneHundredThirtySixED_297263
      · exact prime_oneHundredThirtySixED_9046459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 554244401786064875243) ^ 277122200893032437621 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 554244401786064875243) ^ 79177771683723553606 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 554244401786064875243) ^ 17878851670518221782 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 554244401786064875243) ^ 36180194646260518 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 554244401786064875243) ^ 1864491718734134 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 554244401786064875243) ^ 61266447102238 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_860864737206563162999 : Nat.Prime 860864737206563162999 := by
  apply lucas_primality 860864737206563162999 (7 : ZMod 860864737206563162999)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3923, 1), (89753, 1), (423209, 1), (2888569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3923, 1), (89753, 1), (423209, 1), (2888569, 1)] : List FactorBlock).map factorBlockValue).prod) = 860864737206563162999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3923
      · exact prime_oneHundredThirtySixED_89753
      · exact prime_oneHundredThirtySixED_423209
      · exact prime_oneHundredThirtySixED_2888569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 860864737206563162999) ^ 430432368603281581499 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 860864737206563162999) ^ 219440412237207026 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 860864737206563162999) ^ 9591487050088166 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 860864737206563162999) ^ 2034136176703622 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 860864737206563162999) ^ 298024640299942 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_1083406758269741723789 : Nat.Prime 1083406758269741723789 := by
  apply lucas_primality 1083406758269741723789 (2 : ZMod 1083406758269741723789)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (6650476597, 1), (40726658551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (6650476597, 1), (40726658551, 1)] : List FactorBlock).map factorBlockValue).prod) = 1083406758269741723789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_6650476597
      · exact prime_oneHundredThirtySixED_40726658551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1083406758269741723789) ^ 541703379134870861894 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1083406758269741723789) ^ 162906634204 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1083406758269741723789) ^ 26601906388 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_1170343195281745878391 : Nat.Prime 1170343195281745878391 := by
  apply lucas_primality 1170343195281745878391 (19 : ZMod 1170343195281745878391)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (41, 1), (951498532749386893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (41, 1), (951498532749386893, 1)] : List FactorBlock).map factorBlockValue).prod) = 1170343195281745878391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_41
      · exact prime_oneHundredThirtySixED_951498532749386893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 1170343195281745878391) ^ 585171597640872939195 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (19 : ZMod 1170343195281745878391) ^ 390114398427248626130 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (19 : ZMod 1170343195281745878391) ^ 234068639056349175678 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (19 : ZMod 1170343195281745878391) ^ 28544955982481606790 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (19 : ZMod 1170343195281745878391) ^ 1230 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_1563121067959893364261 : Nat.Prime 1563121067959893364261 := by
  apply lucas_primality 1563121067959893364261 (2 : ZMod 1563121067959893364261)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 1), (19, 1), (1693, 1), (3304607, 1), (18852443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 1), (19, 1), (1693, 1), (3304607, 1), (18852443, 1)] : List FactorBlock).map factorBlockValue).prod) = 1563121067959893364261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_13
      · exact prime_oneHundredThirtySixED_19
      · exact prime_oneHundredThirtySixED_1693
      · exact prime_oneHundredThirtySixED_3304607
      · exact prime_oneHundredThirtySixED_18852443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1563121067959893364261) ^ 781560533979946682130 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1563121067959893364261) ^ 521040355986631121420 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1563121067959893364261) ^ 312624213591978672852 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1563121067959893364261) ^ 120240082150761028020 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1563121067959893364261) ^ 82269529892625966540 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1563121067959893364261) ^ 923284741854632820 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1563121067959893364261) ^ 473012696505180 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1563121067959893364261) ^ 82913448827820 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_2334900312219571567777 : Nat.Prime 2334900312219571567777 := by
  apply lucas_primality 2334900312219571567777 (5 : ZMod 2334900312219571567777)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (1736981, 1), (4667461964617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (1736981, 1), (4667461964617, 1)] : List FactorBlock).map factorBlockValue).prod) = 2334900312219571567777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_1736981
      · exact prime_oneHundredThirtySixED_4667461964617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2334900312219571567777) ^ 1167450156109785783888 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2334900312219571567777) ^ 778300104073190522592 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2334900312219571567777) ^ 1344229045809696 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2334900312219571567777) ^ 500250528 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_2519080308297458895527 : Nat.Prime 2519080308297458895527 := by
  apply lucas_primality 2519080308297458895527 (5 : ZMod 2519080308297458895527)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (353, 1), (10559, 1), (5043589354607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (353, 1), (10559, 1), (5043589354607, 1)] : List FactorBlock).map factorBlockValue).prod) = 2519080308297458895527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_67
      · exact prime_oneHundredThirtySixED_353
      · exact prime_oneHundredThirtySixED_10559
      · exact prime_oneHundredThirtySixED_5043589354607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2519080308297458895527) ^ 1259540154148729447763 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2519080308297458895527) ^ 37598213556678490978 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2519080308297458895527) ^ 7136204839369571942 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2519080308297458895527) ^ 238571863651620314 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2519080308297458895527) ^ 499461818 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_2982305668851757493107 : Nat.Prime 2982305668851757493107 := by
  apply lucas_primality 2982305668851757493107 (2 : ZMod 2982305668851757493107)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (12123193775820152411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (12123193775820152411, 1)] : List FactorBlock).map factorBlockValue).prod) = 2982305668851757493107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_41
      · exact prime_oneHundredThirtySixED_12123193775820152411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2982305668851757493107) ^ 1491152834425878746553 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2982305668851757493107) ^ 994101889617252497702 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2982305668851757493107) ^ 72739162654920914466 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2982305668851757493107) ^ 246 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_3677968923429174504457 : Nat.Prime 3677968923429174504457 := by
  apply lucas_primality 3677968923429174504457 (5 : ZMod 3677968923429174504457)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (107, 1), (197, 1), (7270207559318861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (107, 1), (197, 1), (7270207559318861, 1)] : List FactorBlock).map factorBlockValue).prod) = 3677968923429174504457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_107
      · exact prime_oneHundredThirtySixED_197
      · exact prime_oneHundredThirtySixED_7270207559318861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3677968923429174504457) ^ 1838984461714587252228 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 3677968923429174504457) ^ 1225989641143058168152 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 3677968923429174504457) ^ 34373541340459574808 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 3677968923429174504457) ^ 18669893012330835048 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 3677968923429174504457) ^ 505896 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_3762425242983873046849 : Nat.Prime 3762425242983873046849 := by
  apply lucas_primality 3762425242983873046849 (13 : ZMod 3762425242983873046849)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (19595964807207672119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (19595964807207672119, 1)] : List FactorBlock).map factorBlockValue).prod) = 3762425242983873046849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_19595964807207672119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 3762425242983873046849) ^ 1881212621491936523424 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (13 : ZMod 3762425242983873046849) ^ 1254141747661291015616 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (13 : ZMod 3762425242983873046849) ^ 192 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_4695053119369635358541 : Nat.Prime 4695053119369635358541 := by
  apply lucas_primality 4695053119369635358541 (2 : ZMod 4695053119369635358541)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 2), (1707067, 1), (380936639021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 2), (1707067, 1), (380936639021, 1)] : List FactorBlock).map factorBlockValue).prod) = 4695053119369635358541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_19
      · exact prime_oneHundredThirtySixED_1707067
      · exact prime_oneHundredThirtySixED_380936639021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4695053119369635358541) ^ 2347526559684817679270 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4695053119369635358541) ^ 939010623873927071708 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4695053119369635358541) ^ 247108058914191334660 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4695053119369635358541) ^ 2750362533731620 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4695053119369635358541) ^ 12325023740 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_7447361144334382793303 : Nat.Prime 7447361144334382793303 := by
  apply lucas_primality 7447361144334382793303 (5 : ZMod 7447361144334382793303)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (254729, 1), (1328927666859929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (254729, 1), (1328927666859929, 1)] : List FactorBlock).map factorBlockValue).prod) = 7447361144334382793303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_11
      · exact prime_oneHundredThirtySixED_254729
      · exact prime_oneHundredThirtySixED_1328927666859929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7447361144334382793303) ^ 3723680572167191396651 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 7447361144334382793303) ^ 677032831303125708482 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 7447361144334382793303) ^ 29236408670918438 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 7447361144334382793303) ^ 5604038 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_16154998827771444598291 : Nat.Prime 16154998827771444598291 := by
  apply lucas_primality 16154998827771444598291 (11 : ZMod 16154998827771444598291)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (83, 1), (479, 1), (3229, 1), (12577, 1), (333523903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (83, 1), (479, 1), (3229, 1), (12577, 1), (333523903, 1)] : List FactorBlock).map factorBlockValue).prod) = 16154998827771444598291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_83
      · exact prime_oneHundredThirtySixED_479
      · exact prime_oneHundredThirtySixED_3229
      · exact prime_oneHundredThirtySixED_12577
      · exact prime_oneHundredThirtySixED_333523903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 16154998827771444598291) ^ 8077499413885722299145 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (11 : ZMod 16154998827771444598291) ^ 5384999609257148199430 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (11 : ZMod 16154998827771444598291) ^ 3230999765554288919658 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (11 : ZMod 16154998827771444598291) ^ 194638540093631862630 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (11 : ZMod 16154998827771444598291) ^ 33726511122696126510 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (11 : ZMod 16154998827771444598291) ^ 5003096571003854010 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (11 : ZMod 16154998827771444598291) ^ 1284487463446882770 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (11 : ZMod 16154998827771444598291) ^ 48437304440430 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_19795380672439900412821 : Nat.Prime 19795380672439900412821 := by
  apply lucas_primality 19795380672439900412821 (2 : ZMod 19795380672439900412821)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (13, 1), (157, 1), (197, 1), (273515612853037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (13, 1), (157, 1), (197, 1), (273515612853037, 1)] : List FactorBlock).map factorBlockValue).prod) = 19795380672439900412821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_13
      · exact prime_oneHundredThirtySixED_157
      · exact prime_oneHundredThirtySixED_197
      · exact prime_oneHundredThirtySixED_273515612853037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 19795380672439900412821) ^ 9897690336219950206410 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 19795380672439900412821) ^ 6598460224146633470940 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 19795380672439900412821) ^ 3959076134487980082564 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 19795380672439900412821) ^ 1522721590187684647140 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 19795380672439900412821) ^ 126085227212992996260 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 19795380672439900412821) ^ 100484165849948733060 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 19795380672439900412821) ^ 72373860 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_40960913168257630835201 : Nat.Prime 40960913168257630835201 := by
  apply lucas_primality 40960913168257630835201 (3 : ZMod 40960913168257630835201)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (5, 2), (104161, 1), (30722356172369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (5, 2), (104161, 1), (30722356172369, 1)] : List FactorBlock).map factorBlockValue).prod) = 40960913168257630835201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_104161
      · exact prime_oneHundredThirtySixED_30722356172369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 40960913168257630835201) ^ 20480456584128815417600 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 40960913168257630835201) ^ 8192182633651526167040 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 40960913168257630835201) ^ 393246159006323200 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 40960913168257630835201) ^ 1333260800 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_85428128747639716845467 : Nat.Prime 85428128747639716845467 := by
  apply lucas_primality 85428128747639716845467 (2 : ZMod 85428128747639716845467)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (71, 1), (54691503679666912193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (71, 1), (54691503679666912193, 1)] : List FactorBlock).map factorBlockValue).prod) = 85428128747639716845467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_11
      · exact prime_oneHundredThirtySixED_71
      · exact prime_oneHundredThirtySixED_54691503679666912193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 85428128747639716845467) ^ 42714064373819858422733 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 85428128747639716845467) ^ 7766193522512701531406 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 85428128747639716845467) ^ 1203213080952672068246 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 85428128747639716845467) ^ 1562 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_91847588304336887054971 : Nat.Prime 91847588304336887054971 := by
  apply lucas_primality 91847588304336887054971 (10 : ZMod 91847588304336887054971)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (7, 1), (48596607568432215373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (7, 1), (48596607568432215373, 1)] : List FactorBlock).map factorBlockValue).prod) = 91847588304336887054971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_48596607568432215373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 91847588304336887054971) ^ 45923794152168443527485 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (10 : ZMod 91847588304336887054971) ^ 30615862768112295684990 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (10 : ZMod 91847588304336887054971) ^ 18369517660867377410994 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (10 : ZMod 91847588304336887054971) ^ 13121084043476698150710 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (10 : ZMod 91847588304336887054971) ^ 1890 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_101315302079562151280519 : Nat.Prime 101315302079562151280519 := by
  apply lucas_primality 101315302079562151280519 (7 : ZMod 101315302079562151280519)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (2741, 1), (8508553, 1), (23869257613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (2741, 1), (8508553, 1), (23869257613, 1)] : List FactorBlock).map factorBlockValue).prod) = 101315302079562151280519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_13
      · exact prime_oneHundredThirtySixED_2741
      · exact prime_oneHundredThirtySixED_8508553
      · exact prime_oneHundredThirtySixED_23869257613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 101315302079562151280519) ^ 50657651039781075640259 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 101315302079562151280519) ^ 14473614582794593040074 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 101315302079562151280519) ^ 7793484775350934713886 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 101315302079562151280519) ^ 36962897511697245998 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 101315302079562151280519) ^ 11907465591336406 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 101315302079562151280519) ^ 4244593766686 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_113643592726269236278937 : Nat.Prime 113643592726269236278937 := by
  apply lucas_primality 113643592726269236278937 (3 : ZMod 113643592726269236278937)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (31, 1), (569, 1), (48953, 1), (967726813453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (31, 1), (569, 1), (48953, 1), (967726813453, 1)] : List FactorBlock).map factorBlockValue).prod) = 113643592726269236278937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_17
      · exact prime_oneHundredThirtySixED_31
      · exact prime_oneHundredThirtySixED_569
      · exact prime_oneHundredThirtySixED_48953
      · exact prime_oneHundredThirtySixED_967726813453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 113643592726269236278937) ^ 56821796363134618139468 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 113643592726269236278937) ^ 6684917219192308016408 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 113643592726269236278937) ^ 3665922346008685041256 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 113643592726269236278937) ^ 199725119026835213144 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 113643592726269236278937) ^ 2321483723699655512 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 113643592726269236278937) ^ 117433547512 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_134561460263806399952419 : Nat.Prime 134561460263806399952419 := by
  apply lucas_primality 134561460263806399952419 (3 : ZMod 134561460263806399952419)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (431156603, 1), (52015694269601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (431156603, 1), (52015694269601, 1)] : List FactorBlock).map factorBlockValue).prod) = 134561460263806399952419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_431156603
      · exact prime_oneHundredThirtySixED_52015694269601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 134561460263806399952419) ^ 67280730131903199976209 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 134561460263806399952419) ^ 44853820087935466650806 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 134561460263806399952419) ^ 312094165617606 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 134561460263806399952419) ^ 2586939618 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_174621269330541343771057 : Nat.Prime 174621269330541343771057 := by
  apply lucas_primality 174621269330541343771057 (5 : ZMod 174621269330541343771057)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (404215901228104962433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (404215901228104962433, 1)] : List FactorBlock).map factorBlockValue).prod) = 174621269330541343771057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_404215901228104962433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 174621269330541343771057) ^ 87310634665270671885528 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 174621269330541343771057) ^ 58207089776847114590352 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 174621269330541343771057) ^ 432 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_327687305346061046681609 : Nat.Prime 327687305346061046681609 := by
  apply lucas_primality 327687305346061046681609 (3 : ZMod 327687305346061046681609)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (40960913168257630835201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (40960913168257630835201, 1)] : List FactorBlock).map factorBlockValue).prod) = 327687305346061046681609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_40960913168257630835201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 327687305346061046681609) ^ 163843652673030523340804 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 327687305346061046681609) ^ 8 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_551695338514376175668551 : Nat.Prime 551695338514376175668551 := by
  apply lucas_primality 551695338514376175668551 (13 : ZMod 551695338514376175668551)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (3677968923429174504457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (3677968923429174504457, 1)] : List FactorBlock).map factorBlockValue).prod) = 551695338514376175668551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_3677968923429174504457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 551695338514376175668551) ^ 275847669257188087834275 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (13 : ZMod 551695338514376175668551) ^ 183898446171458725222850 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (13 : ZMod 551695338514376175668551) ^ 110339067702875235133710 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (13 : ZMod 551695338514376175668551) ^ 150 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_756472812222930369990803 : Nat.Prime 756472812222930369990803 := by
  apply lucas_primality 756472812222930369990803 (2 : ZMod 756472812222930369990803)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (113, 1), (1367, 1), (144034804976325343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (113, 1), (1367, 1), (144034804976325343, 1)] : List FactorBlock).map factorBlockValue).prod) = 756472812222930369990803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_17
      · exact prime_oneHundredThirtySixED_113
      · exact prime_oneHundredThirtySixED_1367
      · exact prime_oneHundredThirtySixED_144034804976325343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 756472812222930369990803) ^ 378236406111465184995401 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 756472812222930369990803) ^ 44498400718995904117106 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 756472812222930369990803) ^ 6694449665689649291954 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 756472812222930369990803) ^ 553381720719041967806 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 756472812222930369990803) ^ 5252014 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_2510316720082182169545287 : Nat.Prime 2510316720082182169545287 := by
  apply lucas_primality 2510316720082182169545287 (5 : ZMod 2510316720082182169545287)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (37, 1), (61, 1), (73, 1), (131, 1), (13619, 1), (137741844557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (37, 1), (61, 1), (73, 1), (131, 1), (13619, 1), (137741844557, 1)] : List FactorBlock).map factorBlockValue).prod) = 2510316720082182169545287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_31
      · exact prime_oneHundredThirtySixED_37
      · exact prime_oneHundredThirtySixED_61
      · exact prime_oneHundredThirtySixED_73
      · exact prime_oneHundredThirtySixED_131
      · exact prime_oneHundredThirtySixED_13619
      · exact prime_oneHundredThirtySixED_137741844557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2510316720082182169545287) ^ 1255158360041091084772643 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2510316720082182169545287) ^ 80977958712328457082106 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2510316720082182169545287) ^ 67846397840058977555278 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2510316720082182169545287) ^ 41152733116101347041726 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2510316720082182169545287) ^ 34387900275098385884182 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2510316720082182169545287) ^ 19162723054062459309506 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2510316720082182169545287) ^ 184324599462675832994 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2510316720082182169545287) ^ 18224793839198 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_3581828831320647140600249 : Nat.Prime 3581828831320647140600249 := by
  apply lucas_primality 3581828831320647140600249 (3 : ZMod 3581828831320647140600249)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (17, 1), (3762425242983873046849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (17, 1), (3762425242983873046849, 1)] : List FactorBlock).map factorBlockValue).prod) = 3581828831320647140600249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_7
      · exact prime_oneHundredThirtySixED_17
      · exact prime_oneHundredThirtySixED_3762425242983873046849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3581828831320647140600249) ^ 1790914415660323570300124 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3581828831320647140600249) ^ 511689833045806734371464 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3581828831320647140600249) ^ 210695813607096890623544 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3581828831320647140600249) ^ 952 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_4983829156220440460651701 : Nat.Prime 4983829156220440460651701 := by
  apply lucas_primality 4983829156220440460651701 (2 : ZMod 4983829156220440460651701)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (1542239, 1), (10771847848529401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (1542239, 1), (10771847848529401, 1)] : List FactorBlock).map factorBlockValue).prod) = 4983829156220440460651701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_1542239
      · exact prime_oneHundredThirtySixED_10771847848529401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4983829156220440460651701) ^ 2491914578110220230325850 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4983829156220440460651701) ^ 1661276385406813486883900 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4983829156220440460651701) ^ 996765831244088092130340 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4983829156220440460651701) ^ 3231554354558820300 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4983829156220440460651701) ^ 462671700 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_5950714146483488162159333 : Nat.Prime 5950714146483488162159333 := by
  apply lucas_primality 5950714146483488162159333 (2 : ZMod 5950714146483488162159333)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (257, 1), (919, 1), (2608211, 1), (2415003365941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (257, 1), (919, 1), (2608211, 1), (2415003365941, 1)] : List FactorBlock).map factorBlockValue).prod) = 5950714146483488162159333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_257
      · exact prime_oneHundredThirtySixED_919
      · exact prime_oneHundredThirtySixED_2608211
      · exact prime_oneHundredThirtySixED_2415003365941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5950714146483488162159333) ^ 2975357073241744081079666 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 5950714146483488162159333) ^ 23154529752854039541476 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 5950714146483488162159333) ^ 6475205817718703114428 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 5950714146483488162159333) ^ 2281530959912172812 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 5950714146483488162159333) ^ 2464060394452 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_15642406482924783553025117 : Nat.Prime 15642406482924783553025117 := by
  apply lucas_primality 15642406482924783553025117 (2 : ZMod 15642406482924783553025117)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1621, 1), (57030289, 1), (42301424132491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1621, 1), (57030289, 1), (42301424132491, 1)] : List FactorBlock).map factorBlockValue).prod) = 15642406482924783553025117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_1621
      · exact prime_oneHundredThirtySixED_57030289
      · exact prime_oneHundredThirtySixED_42301424132491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15642406482924783553025117) ^ 7821203241462391776512558 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 15642406482924783553025117) ^ 9649849773550144079596 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 15642406482924783553025117) ^ 274282434075071644 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 15642406482924783553025117) ^ 369784393876 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_45228775313075625918859403 : Nat.Prime 45228775313075625918859403 := by
  apply lucas_primality 45228775313075625918859403 (2 : ZMod 45228775313075625918859403)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (47, 1), (53, 1), (72865747, 1), (5417012621731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (47, 1), (53, 1), (72865747, 1), (5417012621731, 1)] : List FactorBlock).map factorBlockValue).prod) = 45228775313075625918859403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_23
      · exact prime_oneHundredThirtySixED_47
      · exact prime_oneHundredThirtySixED_53
      · exact prime_oneHundredThirtySixED_72865747
      · exact prime_oneHundredThirtySixED_5417012621731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 45228775313075625918859403) ^ 22614387656537812959429701 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 45228775313075625918859403) ^ 1966468491872853300819974 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 45228775313075625918859403) ^ 962314368363311189762966 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 45228775313075625918859403) ^ 853373119114634451299234 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 45228775313075625918859403) ^ 620713808273668366 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 45228775313075625918859403) ^ 8349394485742 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_58256629071733279036791731 : Nat.Prime 58256629071733279036791731 := by
  apply lucas_primality 58256629071733279036791731 (2 : ZMod 58256629071733279036791731)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (457, 1), (554244401786064875243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (457, 1), (554244401786064875243, 1)] : List FactorBlock).map factorBlockValue).prod) = 58256629071733279036791731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_23
      · exact prime_oneHundredThirtySixED_457
      · exact prime_oneHundredThirtySixED_554244401786064875243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 58256629071733279036791731) ^ 29128314535866639518395865 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 58256629071733279036791731) ^ 11651325814346655807358346 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 58256629071733279036791731) ^ 2532896916162316479860510 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 58256629071733279036791731) ^ 127476212410794921305890 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 58256629071733279036791731) ^ 105110 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_149154263671599118869707957 : Nat.Prime 149154263671599118869707957 := by
  apply lucas_primality 149154263671599118869707957 (2 : ZMod 149154263671599118869707957)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3229, 1), (2341567, 1), (4931749931514223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3229, 1), (2341567, 1), (4931749931514223, 1)] : List FactorBlock).map factorBlockValue).prod) = 149154263671599118869707957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3229
      · exact prime_oneHundredThirtySixED_2341567
      · exact prime_oneHundredThirtySixED_4931749931514223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 149154263671599118869707957) ^ 74577131835799559434853978 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 149154263671599118869707957) ^ 46192091567543858429764 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 149154263671599118869707957) ^ 63698482115437704268 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 149154263671599118869707957) ^ 30243679372 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_206668761231341709693502799 : Nat.Prime 206668761231341709693502799 := by
  apply lucas_primality 206668761231341709693502799 (7 : ZMod 206668761231341709693502799)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (227, 1), (2237, 1), (11113, 1), (41467, 1), (33968448887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (227, 1), (2237, 1), (11113, 1), (41467, 1), (33968448887, 1)] : List FactorBlock).map factorBlockValue).prod) = 206668761231341709693502799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_13
      · exact prime_oneHundredThirtySixED_227
      · exact prime_oneHundredThirtySixED_2237
      · exact prime_oneHundredThirtySixED_11113
      · exact prime_oneHundredThirtySixED_41467
      · exact prime_oneHundredThirtySixED_33968448887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 206668761231341709693502799) ^ 103334380615670854846751399 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 206668761231341709693502799) ^ 15897597017795516130269446 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 206668761231341709693502799) ^ 910435071503707972218074 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 206668761231341709693502799) ^ 92386571851292673086054 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 206668761231341709693502799) ^ 18597027016227995113246 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 206668761231341709693502799) ^ 4983933277819512134794 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 206668761231341709693502799) ^ 6084138899566754 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_247747759996893451681887793 : Nat.Prime 247747759996893451681887793 := by
  apply lucas_primality 247747759996893451681887793 (7 : ZMod 247747759996893451681887793)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (23, 1), (263, 1), (1129, 1), (4556173, 1), (18430972757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (23, 1), (263, 1), (1129, 1), (4556173, 1), (18430972757, 1)] : List FactorBlock).map factorBlockValue).prod) = 247747759996893451681887793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_23
      · exact prime_oneHundredThirtySixED_263
      · exact prime_oneHundredThirtySixED_1129
      · exact prime_oneHundredThirtySixED_4556173
      · exact prime_oneHundredThirtySixED_18430972757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 247747759996893451681887793) ^ 123873879998446725840943896 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 247747759996893451681887793) ^ 82582586665631150560629264 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 247747759996893451681887793) ^ 10771641738995367464429904 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 247747759996893451681887793) ^ 942006692003397154683984 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 247747759996893451681887793) ^ 219439999997248407158448 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 247747759996893451681887793) ^ 54376284657517054704 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (7 : ZMod 247747759996893451681887793) ^ 13441925353766256 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_1710513789765785639803672103 : Nat.Prime 1710513789765785639803672103 := by
  apply lucas_primality 1710513789765785639803672103 (5 : ZMod 1710513789765785639803672103)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3578837, 1), (7992514897, 1), (29900001559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3578837, 1), (7992514897, 1), (29900001559, 1)] : List FactorBlock).map factorBlockValue).prod) = 1710513789765785639803672103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3578837
      · exact prime_oneHundredThirtySixED_7992514897
      · exact prime_oneHundredThirtySixED_29900001559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1710513789765785639803672103) ^ 855256894882892819901836051 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1710513789765785639803672103) ^ 477952415761261448846 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1710513789765785639803672103) ^ 214014463758813766 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1710513789765785639803672103) ^ 57207816072869578 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_1985040694296096915327718243 : Nat.Prime 1985040694296096915327718243 := by
  apply lucas_primality 1985040694296096915327718243 (2 : ZMod 1985040694296096915327718243)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (11701, 1), (482323, 1), (66413909, 1), (80242691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (11701, 1), (482323, 1), (66413909, 1), (80242691, 1)] : List FactorBlock).map factorBlockValue).prod) = 1985040694296096915327718243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_11
      · exact prime_oneHundredThirtySixED_11701
      · exact prime_oneHundredThirtySixED_482323
      · exact prime_oneHundredThirtySixED_66413909
      · exact prime_oneHundredThirtySixED_80242691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1985040694296096915327718243) ^ 992520347148048457663859121 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1985040694296096915327718243) ^ 661680231432032305109239414 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1985040694296096915327718243) ^ 180458244936008810484338022 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1985040694296096915327718243) ^ 169647098051115025666842 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1985040694296096915327718243) ^ 4115583735994544973654 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1985040694296096915327718243) ^ 29888930258511013338 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1985040694296096915327718243) ^ 24737962667479545462 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_3495397744303996742207503861 : Nat.Prime 3495397744303996742207503861 := by
  apply lucas_primality 3495397744303996742207503861 (2 : ZMod 3495397744303996742207503861)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (58256629071733279036791731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (58256629071733279036791731, 1)] : List FactorBlock).map factorBlockValue).prod) = 3495397744303996742207503861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_58256629071733279036791731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3495397744303996742207503861) ^ 1747698872151998371103751930 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3495397744303996742207503861) ^ 1165132581434665580735834620 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3495397744303996742207503861) ^ 699079548860799348441500772 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3495397744303996742207503861) ^ 60 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_26798049372997308356924196281 : Nat.Prime 26798049372997308356924196281 := by
  apply lucas_primality 26798049372997308356924196281 (6 : ZMod 26798049372997308356924196281)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (73, 1), (1607, 1), (140647657, 1), (40604292994541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (73, 1), (1607, 1), (140647657, 1), (40604292994541, 1)] : List FactorBlock).map factorBlockValue).prod) = 26798049372997308356924196281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_5
      · exact prime_oneHundredThirtySixED_73
      · exact prime_oneHundredThirtySixED_1607
      · exact prime_oneHundredThirtySixED_140647657
      · exact prime_oneHundredThirtySixED_40604292994541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 26798049372997308356924196281) ^ 13399024686498654178462098140 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 26798049372997308356924196281) ^ 5359609874599461671384839256 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 26798049372997308356924196281) ^ 367096566753387785711290360 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 26798049372997308356924196281) ^ 16675824127565219886076040 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 26798049372997308356924196281) ^ 190533208619303970040 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (6 : ZMod 26798049372997308356924196281) ^ 659980691613080 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_40197074059495962535386294403 : Nat.Prime 40197074059495962535386294403 := by
  apply lucas_primality 40197074059495962535386294403 (2 : ZMod 40197074059495962535386294403)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (53, 1), (47582281, 1), (2656574897467719719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (53, 1), (47582281, 1), (2656574897467719719, 1)] : List FactorBlock).map factorBlockValue).prod) = 40197074059495962535386294403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_53
      · exact prime_oneHundredThirtySixED_47582281
      · exact prime_oneHundredThirtySixED_2656574897467719719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 40197074059495962535386294403) ^ 20098537029747981267693147201 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 40197074059495962535386294403) ^ 13399024686498654178462098134 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 40197074059495962535386294403) ^ 758435359613131368592194234 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 40197074059495962535386294403) ^ 844790817394734870642 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 40197074059495962535386294403) ^ 15131165358 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_53596098745994616713848392553 : Nat.Prime 53596098745994616713848392553 := by
  apply lucas_primality 53596098745994616713848392553 (5 : ZMod 53596098745994616713848392553)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (1613, 1), (12899, 1), (41269, 1), (866934580455847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (1613, 1), (12899, 1), (41269, 1), (866934580455847, 1)] : List FactorBlock).map factorBlockValue).prod) = 53596098745994616713848392553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_3
      · exact prime_oneHundredThirtySixED_1613
      · exact prime_oneHundredThirtySixED_12899
      · exact prime_oneHundredThirtySixED_41269
      · exact prime_oneHundredThirtySixED_866934580455847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 53596098745994616713848392553) ^ 26798049372997308356924196276 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 53596098745994616713848392553) ^ 17865366248664872237949464184 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 53596098745994616713848392553) ^ 33227587567262626604989704 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 53596098745994616713848392553) ^ 4155058434451865781366648 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 53596098745994616713848392553) ^ 1298701173907645368529608 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (5 : ZMod 53596098745994616713848392553) ^ 61822541117016 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySixED_80394148118991925070772588827 : Nat.Prime 80394148118991925070772588827 := by
  apply lucas_primality 80394148118991925070772588827 (2 : ZMod 80394148118991925070772588827)
  · rw [← oneHundredThirtySixEDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (29, 1), (83, 1), (1993, 1), (52363, 1), (72797, 1), (95575199771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (29, 1), (83, 1), (1993, 1), (52363, 1), (72797, 1), (95575199771, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991925070772588827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySixED_2
      · exact prime_oneHundredThirtySixED_23
      · exact prime_oneHundredThirtySixED_29
      · exact prime_oneHundredThirtySixED_83
      · exact prime_oneHundredThirtySixED_1993
      · exact prime_oneHundredThirtySixED_52363
      · exact prime_oneHundredThirtySixED_72797
      · exact prime_oneHundredThirtySixED_95575199771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 80394148118991925070772588827) ^ 40197074059495962535386294413 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 80394148118991925070772588827) ^ 3495397744303996742207503862 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 80394148118991925070772588827) ^ 2772212004103169830026640994 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 80394148118991925070772588827) ^ 968604194204721988804489022 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 80394148118991925070772588827) ^ 40338257962364237366167882 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 80394148118991925070772588827) ^ 1535323570440806009410702 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 80394148118991925070772588827) ^ 1104360730785498373157858 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide
    · change (2 : ZMod 80394148118991925070772588827) ^ 841161183148116206 ≠ 1
      rw [← oneHundredThirtySixEDFastPow_eq_pow]
      decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177600 : Nat.totient 160788296237983850141545177600 = 60531711210754398962122752000 := by
  rw [← show ((([(2, 9), (5, 2), (17, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177600 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_5, prime_oneHundredThirtySixED_17, prime_oneHundredThirtySixED_171401, prime_oneHundredThirtySixED_714027719, prime_oneHundredThirtySixED_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177601 : Nat.totient 160788296237983850141545177601 = 154060967331120522659805000000 := by
  rw [← show ((([(31, 1), (101, 1), (2548779381751, 1), (20148333019621, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177601 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_31, prime_oneHundredThirtySixED_101, prime_oneHundredThirtySixED_2548779381751, prime_oneHundredThirtySixED_20148333019621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177602 : Nat.totient 160788296237983850141545177602 = 48719459716623694586633760000 := by
  rw [← show ((([(2, 1), (3, 5), (11, 1), (11701, 1), (482323, 1), (66413909, 1), (80242691, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177602 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_3, prime_oneHundredThirtySixED_11, prime_oneHundredThirtySixED_11701, prime_oneHundredThirtySixED_482323, prime_oneHundredThirtySixED_66413909, prime_oneHundredThirtySixED_80242691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177603 : Nat.totient 160788296237983850141545177603 = 159946175704467933310700788800 := by
  rw [← show ((([(191, 1), (538553, 1), (1563121067959893364261, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177603 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_191, prime_oneHundredThirtySixED_538553, prime_oneHundredThirtySixED_1563121067959893364261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177604 : Nat.totient 160788296237983850141545177604 = 67227676987801030640734233600 := by
  rw [← show ((([(2, 2), (7, 1), (43, 1), (853, 1), (486329, 1), (8919023, 1), (36093704951, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177604 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_7, prime_oneHundredThirtySixED_43, prime_oneHundredThirtySixED_853, prime_oneHundredThirtySixED_486329, prime_oneHundredThirtySixED_8919023, prime_oneHundredThirtySixED_36093704951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177605 : Nat.totient 160788296237983850141545177605 = 81176305720141262272431628800 := by
  rw [← show ((([(3, 1), (5, 1), (19, 2), (1301, 1), (49139, 1), (464464324697673533, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177605 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_3, prime_oneHundredThirtySixED_5, prime_oneHundredThirtySixED_19, prime_oneHundredThirtySixED_1301, prime_oneHundredThirtySixED_49139, prime_oneHundredThirtySixED_464464324697673533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177606 : Nat.totient 160788296237983850141545177606 = 76898750374687928328565084920 := by
  rw [← show ((([(2, 1), (23, 1), (3495397744303996742207503861, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177606 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_23, prime_oneHundredThirtySixED_3495397744303996742207503861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177607 : Nat.totient 160788296237983850141545177607 = 156899336379940445787540836352 := by
  rw [← show ((([(73, 1), (97, 1), (3049, 1), (7447361144334382793303, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177607 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_73, prime_oneHundredThirtySixED_97, prime_oneHundredThirtySixED_3049, prime_oneHundredThirtySixED_7447361144334382793303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177608 : Nat.totient 160788296237983850141545177608 = 52584850494708617522693168640 := by
  rw [← show ((([(2, 3), (3, 1), (53, 1), (47582281, 1), (2656574897467719719, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177608 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_3, prime_oneHundredThirtySixED_53, prime_oneHundredThirtySixED_47582281, prime_oneHundredThirtySixED_2656574897467719719]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177609 : Nat.totient 160788296237983850141545177609 = 160773637115124163416308765184 := by
  rw [← show ((([(12889, 1), (73607, 1), (6825868727, 1), (24828938929, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177609 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_12889, prime_oneHundredThirtySixED_73607, prime_oneHundredThirtySixED_6825868727, prime_oneHundredThirtySixED_24828938929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177610 : Nat.totient 160788296237983850141545177610 = 63355388368399606622937186624 := by
  rw [← show ((([(2, 1), (5, 1), (67, 2), (3581828831320647140600249, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177610 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_5, prime_oneHundredThirtySixED_67, prime_oneHundredThirtySixED_3581828831320647140600249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177611 : Nat.totient 160788296237983850141545177611 = 84811212585533310159518037504 := by
  rw [← show ((([(3, 2), (7, 1), (13, 1), (698249, 1), (1131479, 1), (248492743638439, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177611 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_3, prime_oneHundredThirtySixED_7, prime_oneHundredThirtySixED_13, prime_oneHundredThirtySixED_698249, prime_oneHundredThirtySixED_1131479, prime_oneHundredThirtySixED_248492743638439]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177612 : Nat.totient 160788296237983850141545177612 = 80394148118991925070772588804 := by
  rw [← show ((([(2, 2), (40197074059495962535386294403, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177612 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_40197074059495962535386294403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177613 : Nat.totient 160788296237983850141545177613 = 146162295410888938612722191040 := by
  rw [← show ((([(11, 1), (16493, 1), (7176047, 1), (123502803087987373, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177613 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_11, prime_oneHundredThirtySixED_16493, prime_oneHundredThirtySixED_7176047, prime_oneHundredThirtySixED_123502803087987373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177614 : Nat.totient 160788296237983850141545177614 = 53595829623074089101048089400 := by
  rw [← show ((([(2, 1), (3, 1), (199151, 1), (134561460263806399952419, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177614 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_3, prime_oneHundredThirtySixED_199151, prime_oneHundredThirtySixED_134561460263806399952419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177615 : Nat.totient 160788296237983850141545177615 = 128609646176102238101466395136 := by
  rw [← show ((([(5, 1), (6143, 1), (2905783, 1), (17939899, 1), (100420121233, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177615 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_5, prime_oneHundredThirtySixED_6143, prime_oneHundredThirtySixED_2905783, prime_oneHundredThirtySixED_17939899, prime_oneHundredThirtySixED_100420121233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177616 : Nat.totient 160788296237983850141545177616 = 80392448770439120461157745024 := by
  rw [← show ((([(2, 4), (47317, 1), (273126599, 1), (777594629002747, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177616 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_47317, prime_oneHundredThirtySixED_273126599, prime_oneHundredThirtySixED_777594629002747]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177617 : Nat.totient 160788296237983850141545177617 = 99465705508266175307962005504 := by
  rw [← show ((([(3, 1), (17, 1), (89, 1), (347, 1), (2755243, 1), (37051420944511243, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177617 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_3, prime_oneHundredThirtySixED_17, prime_oneHundredThirtySixED_89, prime_oneHundredThirtySixED_347, prime_oneHundredThirtySixED_2755243, prime_oneHundredThirtySixED_37051420944511243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177618 : Nat.totient 160788296237983850141545177618 = 68814483653143544462867584512 := by
  rw [← show ((([(2, 1), (7, 1), (727, 1), (184753553, 1), (85506511358660377, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177618 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_7, prime_oneHundredThirtySixED_727, prime_oneHundredThirtySixED_184753553, prime_oneHundredThirtySixED_85506511358660377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177619 : Nat.totient 160788296237983850141545177619 = 160670829025532569283283485280 := by
  rw [← show ((([(1877, 1), (8779, 1), (11903, 1), (819763689963477131, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177619 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_1877, prime_oneHundredThirtySixED_8779, prime_oneHundredThirtySixED_11903, prime_oneHundredThirtySixED_819763689963477131]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177620 : Nat.totient 160788296237983850141545177620 = 42876878846608903691866402560 := by
  rw [← show ((([(2, 2), (3, 2), (5, 1), (285490349, 1), (3128891451364766141, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177620 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_3, prime_oneHundredThirtySixED_5, prime_oneHundredThirtySixED_285490349, prime_oneHundredThirtySixED_3128891451364766141]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177621 : Nat.totient 160788296237983850141545177621 = 160779732529770024579370938288 := by
  rw [← show ((([(19219, 1), (813677, 1), (10281858113958598067, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177621 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_19219, prime_oneHundredThirtySixED_813677, prime_oneHundredThirtySixED_10281858113958598067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177622 : Nat.totient 160788296237983850141545177622 = 80187479357760583361079085624 := by
  rw [← show ((([(2, 1), (389, 1), (206668761231341709693502799, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177622 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_389, prime_oneHundredThirtySixED_206668761231341709693502799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177623 : Nat.totient 160788296237983850141545177623 = 103495854149073210548695870080 := by
  rw [← show ((([(3, 1), (29, 1), (1705861, 1), (1083406758269741723789, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177623 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_3, prime_oneHundredThirtySixED_29, prime_oneHundredThirtySixED_1705861, prime_oneHundredThirtySixED_1083406758269741723789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177624 : Nat.totient 160788296237983850141545177624 = 63912845242311283923968102400 := by
  rw [← show ((([(2, 3), (11, 1), (13, 1), (19, 1), (1094963, 1), (212514941, 1), (31789660873, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177624 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_11, prime_oneHundredThirtySixED_13, prime_oneHundredThirtySixED_19, prime_oneHundredThirtySixED_1094963, prime_oneHundredThirtySixED_212514941, prime_oneHundredThirtySixED_31789660873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177625 : Nat.totient 160788296237983850141545177625 = 109825819374088744726453862400 := by
  rw [← show ((([(5, 3), (7, 1), (257, 1), (21101293, 1), (33884742454793303, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177625 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_5, prime_oneHundredThirtySixED_7, prime_oneHundredThirtySixED_257, prime_oneHundredThirtySixED_21101293, prime_oneHundredThirtySixED_33884742454793303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177626 : Nat.totient 160788296237983850141545177626 = 53420293829837889931397534400 := by
  rw [← show ((([(2, 1), (3, 1), (311, 1), (15803, 1), (669679, 1), (5463023, 1), (1490402411, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177626 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_3, prime_oneHundredThirtySixED_311, prime_oneHundredThirtySixED_15803, prime_oneHundredThirtySixED_669679, prime_oneHundredThirtySixED_5463023, prime_oneHundredThirtySixED_1490402411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177627 : Nat.totient 160788296237983850141545177627 = 159195849934854905842102594560 := by
  rw [← show ((([(197, 1), (223, 1), (4493, 1), (6793, 1), (10978711, 1), (10922799403, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177627 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_197, prime_oneHundredThirtySixED_223, prime_oneHundredThirtySixED_4493, prime_oneHundredThirtySixED_6793, prime_oneHundredThirtySixED_10978711, prime_oneHundredThirtySixED_10922799403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177628 : Nat.totient 160788296237983850141545177628 = 80339045891672847447320156928 := by
  rw [← show ((([(2, 2), (1459, 1), (76152073229, 1), (361790716440337, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177628 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_1459, prime_oneHundredThirtySixED_76152073229, prime_oneHundredThirtySixED_361790716440337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177629 : Nat.totient 160788296237983850141545177629 = 102495295521282053697478562160 := by
  rw [← show ((([(3, 3), (23, 1), (2819, 1), (91847588304336887054971, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177629 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_3, prime_oneHundredThirtySixED_23, prime_oneHundredThirtySixED_2819, prime_oneHundredThirtySixED_91847588304336887054971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177630 : Nat.totient 160788296237983850141545177630 = 63712976254644212892198900384 := by
  rw [← show ((([(2, 1), (5, 1), (107, 1), (50387, 1), (2982305668851757493107, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177630 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_5, prime_oneHundredThirtySixED_107, prime_oneHundredThirtySixED_50387, prime_oneHundredThirtySixED_2982305668851757493107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177631 : Nat.totient 160788296237983850141545177631 = 160788121616714519600200485792 := by
  rw [← show ((([(920783, 1), (174621269330541343771057, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177631 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_920783, prime_oneHundredThirtySixED_174621269330541343771057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177632 : Nat.totient 160788296237983850141545177632 = 44279977325443733984647680000 := by
  rw [← show ((([(2, 5), (3, 1), (7, 1), (31, 1), (251, 1), (89597, 1), (343207110292651133, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177632 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_3, prime_oneHundredThirtySixED_7, prime_oneHundredThirtySixED_31, prime_oneHundredThirtySixED_251, prime_oneHundredThirtySixED_89597, prime_oneHundredThirtySixED_343207110292651133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177633 : Nat.totient 160788296237983850141545177633 = 156441851562644880169426151040 := by
  rw [← show ((([(37, 1), (198073, 1), (6202103, 1), (3537434893525811, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177633 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_37, prime_oneHundredThirtySixED_198073, prime_oneHundredThirtySixED_6202103, prime_oneHundredThirtySixED_3537434893525811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177634 : Nat.totient 160788296237983850141545177634 = 75655073266440591946121648640 := by
  rw [← show ((([(2, 1), (17, 1), (7561, 1), (2416168199, 1), (258862483991359, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177634 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_17, prime_oneHundredThirtySixED_7561, prime_oneHundredThirtySixED_2416168199, prime_oneHundredThirtySixED_258862483991359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177635 : Nat.totient 160788296237983850141545177635 = 76272555916134520011074396160 := by
  rw [← show ((([(3, 1), (5, 1), (11, 2), (47, 1), (2857, 1), (3857267, 1), (171036973802353, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177635 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_3, prime_oneHundredThirtySixED_5, prime_oneHundredThirtySixED_11, prime_oneHundredThirtySixED_47, prime_oneHundredThirtySixED_2857, prime_oneHundredThirtySixED_3857267, prime_oneHundredThirtySixED_171036973802353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177636 : Nat.totient 160788296237983850141545177636 = 79073835818901528593034259200 := by
  rw [← show ((([(2, 2), (61, 1), (33289, 1), (19795380672439900412821, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177636 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_61, prime_oneHundredThirtySixED_33289, prime_oneHundredThirtySixED_19795380672439900412821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177637 : Nat.totient 160788296237983850141545177637 = 148028356349806118173746424848 := by
  rw [← show ((([(13, 2), (379, 1), (2510316720082182169545287, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177637 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_13, prime_oneHundredThirtySixED_379, prime_oneHundredThirtySixED_2510316720082182169545287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177638 : Nat.totient 160788296237983850141545177638 = 52288869590057538443613528960 := by
  rw [← show ((([(2, 1), (3, 2), (41, 1), (7226909, 1), (30147096096777913439, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177638 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_3, prime_oneHundredThirtySixED_41, prime_oneHundredThirtySixED_7226909, prime_oneHundredThirtySixED_30147096096777913439]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177639 : Nat.totient 160788296237983850141545177639 = 137817857771001228220191265920 := by
  rw [← show ((([(7, 1), (202121, 1), (113643592726269236278937, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177639 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_7, prime_oneHundredThirtySixED_202121, prime_oneHundredThirtySixED_113643592726269236278937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177640 : Nat.totient 160788296237983850141545177640 = 64315318494918352309403910144 := by
  rw [← show ((([(2, 3), (5, 1), (233717500609, 1), (17199000483384449, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177640 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_5, prime_oneHundredThirtySixED_233717500609, prime_oneHundredThirtySixED_17199000483384449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177641 : Nat.totient 160788296237983850141545177641 = 105680186531702792841957795600 := by
  rw [← show ((([(3, 1), (71, 1), (46727, 1), (16154998827771444598291, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177641 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_3, prime_oneHundredThirtySixED_71, prime_oneHundredThirtySixED_46727, prime_oneHundredThirtySixED_16154998827771444598291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177642 : Nat.totient 160788296237983850141545177642 = 80314471052887338476765736768 := by
  rw [← show ((([(2, 1), (1009, 1), (6997720267, 1), (11386144570981007, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177642 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_1009, prime_oneHundredThirtySixED_6997720267, prime_oneHundredThirtySixED_11386144570981007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177643 : Nat.totient 160788296237983850141545177643 = 152044191014028896135404127520 := by
  rw [← show ((([(19, 1), (541, 1), (15642406482924783553025117, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177643 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_19, prime_oneHundredThirtySixED_541, prime_oneHundredThirtySixED_15642406482924783553025117]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177644 : Nat.totient 160788296237983850141545177644 = 52909789744882732751316619200 := by
  rw [← show ((([(2, 2), (3, 1), (149, 1), (163, 1), (551695338514376175668551, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177644 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_3, prime_oneHundredThirtySixED_149, prime_oneHundredThirtySixED_163, prime_oneHundredThirtySixED_551695338514376175668551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177645 : Nat.totient 160788296237983850141545177645 = 127071182770910840492072640000 := by
  rw [← show ((([(5, 1), (131, 1), (349, 1), (601, 1), (1170343195281745878391, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177645 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_5, prime_oneHundredThirtySixED_131, prime_oneHundredThirtySixED_349, prime_oneHundredThirtySixED_601, prime_oneHundredThirtySixED_1170343195281745878391]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177646 : Nat.totient 160788296237983850141545177646 = 62644790742071629925277341520 := by
  rw [← show ((([(2, 1), (7, 2), (11, 1), (149154263671599118869707957, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177646 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_7, prime_oneHundredThirtySixED_11, prime_oneHundredThirtySixED_149154263671599118869707957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177647 : Nat.totient 160788296237983850141545177647 = 104626999531048377662579918016 := by
  rw [← show ((([(3, 2), (43, 1), (1447, 1), (24888664277, 1), (11536480800199, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177647 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_3, prime_oneHundredThirtySixED_43, prime_oneHundredThirtySixED_1447, prime_oneHundredThirtySixED_24888664277, prime_oneHundredThirtySixED_11536480800199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177648 : Nat.totient 160788296237983850141545177648 = 80239428284703007380371048448 := by
  rw [← show ((([(2, 4), (557, 1), (7727, 1), (2334900312219571567777, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177648 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_557, prime_oneHundredThirtySixED_7727, prime_oneHundredThirtySixED_2334900312219571567777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177649 : Nat.totient 160788296237983850141545177649 = 160788210809855102501826450036 := by
  rw [← show ((([(1882147, 1), (85428128747639716845467, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177649 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_1882147, prime_oneHundredThirtySixED_85428128747639716845467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177650 : Nat.totient 160788296237983850141545177650 = 39215550585636710380323175680 := by
  rw [← show ((([(2, 1), (3, 1), (5, 2), (13, 1), (109, 1), (756472812222930369990803, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177650 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_3, prime_oneHundredThirtySixED_5, prime_oneHundredThirtySixED_13, prime_oneHundredThirtySixED_109, prime_oneHundredThirtySixED_756472812222930369990803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177651 : Nat.totient 160788296237983850141545177651 = 151128614244556337618149200000 := by
  rw [← show ((([(17, 1), (751, 1), (3594403, 1), (3503795954666829551, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177651 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_17, prime_oneHundredThirtySixED_751, prime_oneHundredThirtySixED_3594403, prime_oneHundredThirtySixED_3503795954666829551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177652 : Nat.totient 160788296237983850141545177652 = 73313313991641175762234552320 := by
  rw [← show ((([(2, 2), (23, 1), (29, 1), (83, 1), (1993, 1), (52363, 1), (72797, 1), (95575199771, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177652 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_23, prime_oneHundredThirtySixED_29, prime_oneHundredThirtySixED_83, prime_oneHundredThirtySixED_1993, prime_oneHundredThirtySixED_52363, prime_oneHundredThirtySixED_72797, prime_oneHundredThirtySixED_95575199771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177653 : Nat.totient 160788296237983850141545177653 = 90404228280910001193235906560 := by
  rw [← show ((([(3, 1), (7, 1), (113, 1), (139, 1), (16981, 1), (88463, 1), (425489, 1), (762655897, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177653 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_3, prime_oneHundredThirtySixED_7, prime_oneHundredThirtySixED_113, prime_oneHundredThirtySixED_139, prime_oneHundredThirtySixED_16981, prime_oneHundredThirtySixED_88463, prime_oneHundredThirtySixED_425489, prime_oneHundredThirtySixED_762655897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177654 : Nat.totient 160788296237983850141545177654 = 80394148118991925070772588826 := by
  rw [← show ((([(2, 1), (80394148118991925070772588827, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177654 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_80394148118991925070772588827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177655 : Nat.totient 160788296237983850141545177655 = 128630636942275653102871288768 := by
  rw [← show ((([(5, 1), (2673598457, 1), (12027856749917614883, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177655 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_5, prime_oneHundredThirtySixED_2673598457, prime_oneHundredThirtySixED_12027856749917614883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177656 : Nat.totient 160788296237983850141545177656 = 53557420880566917441721391616 := by
  rw [← show ((([(2, 3), (3, 3), (1613, 1), (12899, 1), (41269, 1), (866934580455847, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177656 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_3, prime_oneHundredThirtySixED_1613, prime_oneHundredThirtySixED_12899, prime_oneHundredThirtySixED_41269, prime_oneHundredThirtySixED_866934580455847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177657 : Nat.totient 160788296237983850141545177657 = 143693700798198201975494919360 := by
  rw [← show ((([(11, 1), (59, 1), (247747759996893451681887793, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177657 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_11, prime_oneHundredThirtySixED_59, prime_oneHundredThirtySixED_247747759996893451681887793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177658 : Nat.totient 160788296237983850141545177658 = 80394148103852044460108195680 := by
  rw [← show ((([(2, 1), (5310091289, 1), (15139880605354301861, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177658 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_5310091289, prime_oneHundredThirtySixED_15139880605354301861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177659 : Nat.totient 160788296237983850141545177659 = 107192197491989233427696785104 := by
  rw [← show ((([(3, 1), (53596098745994616713848392553, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177659 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_3, prime_oneHundredThirtySixED_53596098745994616713848392553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177660 : Nat.totient 160788296237983850141545177660 = 54841781573991826902460403712 := by
  rw [← show ((([(2, 2), (5, 1), (7, 1), (193, 1), (5950714146483488162159333, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177660 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_5, prime_oneHundredThirtySixED_7, prime_oneHundredThirtySixED_193, prime_oneHundredThirtySixED_5950714146483488162159333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177661 : Nat.totient 160788296237983850141545177661 = 157754310656769117446104156480 := by
  rw [← show ((([(53, 1), (646157, 1), (4695053119369635358541, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177661 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_53, prime_oneHundredThirtySixED_646157, prime_oneHundredThirtySixED_4695053119369635358541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177662 : Nat.totient 160788296237983850141545177662 = 50595833593949911556536058400 := by
  rw [← show ((([(2, 1), (3, 1), (19, 1), (283, 1), (4983829156220440460651701, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177662 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_3, prime_oneHundredThirtySixED_19, prime_oneHundredThirtySixED_283, prime_oneHundredThirtySixED_4983829156220440460651701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177663 : Nat.totient 160788296237983850141545177663 = 143342200666123163339279040000 := by
  rw [← show ((([(13, 1), (31, 1), (587, 1), (3323, 1), (65831, 1), (19820621, 1), (156759271, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177663 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_13, prime_oneHundredThirtySixED_31, prime_oneHundredThirtySixED_587, prime_oneHundredThirtySixED_3323, prime_oneHundredThirtySixED_65831, prime_oneHundredThirtySixED_19820621, prime_oneHundredThirtySixED_156759271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177664 : Nat.totient 160788296237983850141545177664 = 80394118527429527372491484160 := by
  rw [← show ((([(2, 6), (2717291, 1), (24250644403, 1), (38125454137, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177664 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_2717291, prime_oneHundredThirtySixED_24250644403, prime_oneHundredThirtySixED_38125454137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177665 : Nat.totient 160788296237983850141545177665 = 84668267386077571720104800544 := by
  rw [← show ((([(3, 2), (5, 1), (79, 1), (45228775313075625918859403, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177665 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_3, prime_oneHundredThirtySixED_5, prime_oneHundredThirtySixED_79, prime_oneHundredThirtySixED_45228775313075625918859403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177666 : Nat.totient 160788296237983850141545177666 = 80383355680477797254864747520 := by
  rw [← show ((([(2, 1), (12959, 1), (18371, 1), (389797, 1), (15266233, 1), (56747897, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177666 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_12959, prime_oneHundredThirtySixED_18371, prime_oneHundredThirtySixED_389797, prime_oneHundredThirtySixED_15266233, prime_oneHundredThirtySixED_56747897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177667 : Nat.totient 160788296237983850141545177667 = 137818539591250078743474936384 := by
  rw [← show ((([(7, 1), (3336404189, 1), (6884584512019465129, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177667 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_7, prime_oneHundredThirtySixED_3336404189, prime_oneHundredThirtySixED_6884584512019465129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177668 : Nat.totient 160788296237983850141545177668 = 45757496639721319570937856000 := by
  rw [← show ((([(2, 2), (3, 1), (11, 1), (17, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177668 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_3, prime_oneHundredThirtySixED_11, prime_oneHundredThirtySixED_17, prime_oneHundredThirtySixED_461, prime_oneHundredThirtySixED_69997, prime_oneHundredThirtySixED_2220502305087140441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177669 : Nat.totient 160788296237983850141545177669 = 160760518715508405967777945872 := by
  rw [← show ((([(7559, 1), (24709, 1), (860864737206563162999, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177669 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_7559, prime_oneHundredThirtySixED_24709, prime_oneHundredThirtySixED_860864737206563162999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177670 : Nat.totient 160788296237983850141545177670 = 62552126845436757527673815040 := by
  rw [← show ((([(2, 1), (5, 1), (37, 1), (3847, 1), (7213, 1), (15660823346077790081, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177670 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_5, prime_oneHundredThirtySixED_37, prime_oneHundredThirtySixED_3847, prime_oneHundredThirtySixED_7213, prime_oneHundredThirtySixED_15660823346077790081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177671 : Nat.totient 160788296237983850141545177671 = 107191994861385074303393166072 := by
  rw [← show ((([(3, 1), (529003, 1), (101315302079562151280519, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177671 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_3, prime_oneHundredThirtySixED_529003, prime_oneHundredThirtySixED_101315302079562151280519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177672 : Nat.totient 160788296237983850141545177672 = 79882083479642130355405898304 := by
  rw [← show ((([(2, 3), (157, 1), (48437485823, 1), (2642915032645219, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177672 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_157, prime_oneHundredThirtySixED_48437485823, prime_oneHundredThirtySixED_2642915032645219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177673 : Nat.totient 160788296237983850141545177673 = 159115394408903331666578841600 := by
  rw [← show ((([(137, 1), (673, 1), (1031, 1), (1481, 1), (1142102489347470943, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177673 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_137, prime_oneHundredThirtySixED_673, prime_oneHundredThirtySixED_1031, prime_oneHundredThirtySixED_1481, prime_oneHundredThirtySixED_1142102489347470943]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177674 : Nat.totient 160788296237983850141545177674 = 45939513210832905572092864320 := by
  rw [← show ((([(2, 1), (3, 2), (7, 1), (2351242931491, 1), (542733195323689, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177674 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_3, prime_oneHundredThirtySixED_7, prime_oneHundredThirtySixED_2351242931491, prime_oneHundredThirtySixED_542733195323689]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177675 : Nat.totient 160788296237983850141545177675 = 122134108572754596572728320000 := by
  rw [← show ((([(5, 2), (23, 1), (151, 1), (1373, 1), (3043321, 1), (19626767, 1), (22580969, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177675 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_5, prime_oneHundredThirtySixED_23, prime_oneHundredThirtySixED_151, prime_oneHundredThirtySixED_1373, prime_oneHundredThirtySixED_3043321, prime_oneHundredThirtySixED_19626767, prime_oneHundredThirtySixED_22580969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177676 : Nat.totient 160788296237983850141545177676 = 74198171276318643786569437440 := by
  rw [← show ((([(2, 2), (13, 1), (11399, 1), (13997, 1), (19379803686463059821, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177676 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_13, prime_oneHundredThirtySixED_11399, prime_oneHundredThirtySixED_13997, prime_oneHundredThirtySixED_19379803686463059821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177677 : Nat.totient 160788296237983850141545177677 = 105592243575509573075146666944 := by
  rw [← show ((([(3, 1), (67, 1), (2341907, 1), (4176307, 1), (81789266816573, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177677 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_3, prime_oneHundredThirtySixED_67, prime_oneHundredThirtySixED_2341907, prime_oneHundredThirtySixED_4176307, prime_oneHundredThirtySixED_81789266816573]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177678 : Nat.totient 160788296237983850141545177678 = 80394148082267364879182411856 := by
  rw [← show ((([(2, 1), (2189111257, 1), (36724560189401065727, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177678 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_2189111257, prime_oneHundredThirtySixED_36724560189401065727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177679 : Nat.totient 160788296237983850141545177679 = 142606027705484059896596433600 := by
  rw [← show ((([(11, 1), (41, 1), (3275005491103, 1), (108859380612443, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177679 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_11, prime_oneHundredThirtySixED_41, prime_oneHundredThirtySixED_3275005491103, prime_oneHundredThirtySixED_108859380612443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177680 : Nat.totient 160788296237983850141545177680 = 42263208368410293540741611520 := by
  rw [← show ((([(2, 4), (3, 1), (5, 1), (73, 1), (1607, 1), (140647657, 1), (40604292994541, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177680 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_3, prime_oneHundredThirtySixED_5, prime_oneHundredThirtySixED_73, prime_oneHundredThirtySixED_1607, prime_oneHundredThirtySixED_140647657, prime_oneHundredThirtySixED_40604292994541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177681 : Nat.totient 160788296237983850141545177681 = 125294005120694505081062630400 := by
  rw [← show ((([(7, 1), (19, 1), (29, 1), (199, 1), (2351, 1), (2447, 1), (4093, 1), (8896585869827, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177681 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_7, prime_oneHundredThirtySixED_19, prime_oneHundredThirtySixED_29, prime_oneHundredThirtySixED_199, prime_oneHundredThirtySixED_2351, prime_oneHundredThirtySixED_2447, prime_oneHundredThirtySixED_4093, prime_oneHundredThirtySixED_8896585869827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177682 : Nat.totient 160788296237983850141545177682 = 78683634329226139430968916692 := by
  rw [← show ((([(2, 1), (47, 1), (1710513789765785639803672103, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177682 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_47, prime_oneHundredThirtySixED_1710513789765785639803672103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177683 : Nat.totient 160788296237983850141545177683 = 107192197491989233427696785068 := by
  rw [← show ((([(3, 4), (1985040694296096915327718243, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177683 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_3, prime_oneHundredThirtySixED_1985040694296096915327718243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177684 : Nat.totient 160788296237983850141545177684 = 79903272535583525622843294720 := by
  rw [← show ((([(2, 2), (241, 1), (509, 1), (327687305346061046681609, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177684 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_241, prime_oneHundredThirtySixED_509, prime_oneHundredThirtySixED_327687305346061046681609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177685 : Nat.totient 160788296237983850141545177685 = 120518260252729805567676579840 := by
  rw [← show ((([(5, 1), (17, 1), (271, 1), (1217, 1), (4440187, 1), (1291737826932829, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177685 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_5, prime_oneHundredThirtySixED_17, prime_oneHundredThirtySixED_271, prime_oneHundredThirtySixED_1217, prime_oneHundredThirtySixED_4440187, prime_oneHundredThirtySixED_1291737826932829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177686 : Nat.totient 160788296237983850141545177686 = 53596098745994616713848392560 := by
  rw [← show ((([(2, 1), (3, 1), (26798049372997308356924196281, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177686 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_3, prime_oneHundredThirtySixED_26798049372997308356924196281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177687 : Nat.totient 160788296237983850141545177687 = 160788296237973013996282979416 := by
  rw [← show ((([(14858519144333, 1), (10821286743053939, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177687 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_14858519144333, prime_oneHundredThirtySixED_10821286743053939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177688 : Nat.totient 160788296237983850141545177688 = 68905886379832757269934899200 := by
  rw [← show ((([(2, 3), (7, 1), (21377, 1), (450301, 1), (10003657, 1), (29816588057, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177688 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_7, prime_oneHundredThirtySixED_21377, prime_oneHundredThirtySixED_450301, prime_oneHundredThirtySixED_10003657, prime_oneHundredThirtySixED_29816588057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177689 : Nat.totient 160788296237983850141545177689 = 98775158995799171441966592000 := by
  rw [← show ((([(3, 1), (13, 1), (577, 1), (515546501, 1), (13859455535240563, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177689 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_3, prime_oneHundredThirtySixED_13, prime_oneHundredThirtySixED_577, prime_oneHundredThirtySixED_515546501, prime_oneHundredThirtySixED_13859455535240563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177690 : Nat.totient 160788296237983850141545177690 = 57090045527617716228514099200 := by
  rw [← show ((([(2, 1), (5, 1), (11, 1), (43, 1), (3089, 1), (276917, 1), (39739808160661181, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177690 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_5, prime_oneHundredThirtySixED_11, prime_oneHundredThirtySixED_43, prime_oneHundredThirtySixED_3089, prime_oneHundredThirtySixED_276917, prime_oneHundredThirtySixED_39739808160661181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177691 : Nat.totient 160788296237983850141545177691 = 160788296156961232954086097632 := by
  rw [← show ((([(1984486577, 1), (81022617185474593483, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177691 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_1984486577, prime_oneHundredThirtySixED_81022617185474593483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177692 : Nat.totient 160788296237983850141545177692 = 53585895592539404793689203200 := by
  rw [← show ((([(2, 2), (3, 2), (6803, 1), (23063, 1), (41482451, 1), (686232454673, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177692 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_3, prime_oneHundredThirtySixED_6803, prime_oneHundredThirtySixED_23063, prime_oneHundredThirtySixED_41482451, prime_oneHundredThirtySixED_686232454673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177693 : Nat.totient 160788296237983850141545177693 = 160788191593183221213259966368 := by
  rw [← show ((([(1537099, 1), (4044130543, 1), (25865890057849, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177693 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_1537099, prime_oneHundredThirtySixED_4044130543, prime_oneHundredThirtySixED_25865890057849]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177694 : Nat.totient 160788296237983850141545177694 = 77625934213767051279494396160 := by
  rw [← show ((([(2, 1), (31, 1), (599, 1), (2203, 1), (7993, 1), (245873436519459197, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177694 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_31, prime_oneHundredThirtySixED_599, prime_oneHundredThirtySixED_2203, prime_oneHundredThirtySixED_7993, prime_oneHundredThirtySixED_245873436519459197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177695 : Nat.totient 160788296237983850141545177695 = 73425214454083040150565562368 := by
  rw [← show ((([(3, 1), (5, 1), (7, 2), (947, 1), (189257, 1), (40897789, 1), (29844570527, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177695 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_3, prime_oneHundredThirtySixED_5, prime_oneHundredThirtySixED_7, prime_oneHundredThirtySixED_947, prime_oneHundredThirtySixED_189257, prime_oneHundredThirtySixED_40897789, prime_oneHundredThirtySixED_29844570527]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177696 : Nat.totient 160788296237983850141545177696 = 80322060679121698456310839296 := by
  rw [← show ((([(2, 5), (1117, 1), (1360213, 1), (1457389, 1), (2269179614687, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177696 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_1117, prime_oneHundredThirtySixED_1360213, prime_oneHundredThirtySixED_1457389, prime_oneHundredThirtySixED_2269179614687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177697 : Nat.totient 160788296237983850141545177697 = 156907127573704091935861171200 := by
  rw [← show ((([(61, 1), (127, 2), (541290773, 1), (301916280394081, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177697 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_61, prime_oneHundredThirtySixED_127, prime_oneHundredThirtySixED_541290773, prime_oneHundredThirtySixED_301916280394081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177698 : Nat.totient 160788296237983850141545177698 = 51114759298876070347473887040 := by
  rw [← show ((([(2, 1), (3, 1), (23, 1), (631, 1), (733, 1), (2519080308297458895527, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177698 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_3, prime_oneHundredThirtySixED_23, prime_oneHundredThirtySixED_631, prime_oneHundredThirtySixED_733, prime_oneHundredThirtySixED_2519080308297458895527]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177699 : Nat.totient 160788296237983850141545177699 = 160788296237979675675643497936 := by
  rw [← show ((([(38879198473417, 1), (4135586703206347, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177699 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_38879198473417, prime_oneHundredThirtySixED_4135586703206347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177700 : Nat.totient 160788296237983850141545177700 = 60929985846294577439255007360 := by
  rw [← show ((([(2, 2), (5, 2), (19, 1), (192887, 1), (438730547277022707709, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177700 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_2, prime_oneHundredThirtySixED_5, prime_oneHundredThirtySixED_19, prime_oneHundredThirtySixED_192887, prime_oneHundredThirtySixED_438730547277022707709]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySixED_160788296237983850141545177701 : Nat.totient 160788296237983850141545177701 = 97411900465305029538512726400 := by
  rw [← show ((([(3, 2), (11, 1), (2741, 1), (8366480557, 1), (70821871181927, 1)] : List FactorBlock).map factorBlockValue).prod) = 160788296237983850141545177701 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySixED_3, prime_oneHundredThirtySixED_11, prime_oneHundredThirtySixED_2741, prime_oneHundredThirtySixED_8366480557, prime_oneHundredThirtySixED_70821871181927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredThirtySixED : certifiedKill 1 160788296237983850141545177599 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredThirtySixED_160788296237983850141545177600, phi_oneHundredThirtySixED_160788296237983850141545177601, phi_oneHundredThirtySixED_160788296237983850141545177602,
    phi_oneHundredThirtySixED_160788296237983850141545177603, phi_oneHundredThirtySixED_160788296237983850141545177604, phi_oneHundredThirtySixED_160788296237983850141545177605,
    phi_oneHundredThirtySixED_160788296237983850141545177606, phi_oneHundredThirtySixED_160788296237983850141545177607, phi_oneHundredThirtySixED_160788296237983850141545177608,
    phi_oneHundredThirtySixED_160788296237983850141545177609, phi_oneHundredThirtySixED_160788296237983850141545177610, phi_oneHundredThirtySixED_160788296237983850141545177611,
    phi_oneHundredThirtySixED_160788296237983850141545177612, phi_oneHundredThirtySixED_160788296237983850141545177613, phi_oneHundredThirtySixED_160788296237983850141545177614,
    phi_oneHundredThirtySixED_160788296237983850141545177615, phi_oneHundredThirtySixED_160788296237983850141545177616, phi_oneHundredThirtySixED_160788296237983850141545177617,
    phi_oneHundredThirtySixED_160788296237983850141545177618, phi_oneHundredThirtySixED_160788296237983850141545177619, phi_oneHundredThirtySixED_160788296237983850141545177620,
    phi_oneHundredThirtySixED_160788296237983850141545177621, phi_oneHundredThirtySixED_160788296237983850141545177622, phi_oneHundredThirtySixED_160788296237983850141545177623,
    phi_oneHundredThirtySixED_160788296237983850141545177624, phi_oneHundredThirtySixED_160788296237983850141545177625, phi_oneHundredThirtySixED_160788296237983850141545177626,
    phi_oneHundredThirtySixED_160788296237983850141545177627, phi_oneHundredThirtySixED_160788296237983850141545177628, phi_oneHundredThirtySixED_160788296237983850141545177629,
    phi_oneHundredThirtySixED_160788296237983850141545177630, phi_oneHundredThirtySixED_160788296237983850141545177631, phi_oneHundredThirtySixED_160788296237983850141545177632,
    phi_oneHundredThirtySixED_160788296237983850141545177633, phi_oneHundredThirtySixED_160788296237983850141545177634, phi_oneHundredThirtySixED_160788296237983850141545177635,
    phi_oneHundredThirtySixED_160788296237983850141545177636, phi_oneHundredThirtySixED_160788296237983850141545177637, phi_oneHundredThirtySixED_160788296237983850141545177638,
    phi_oneHundredThirtySixED_160788296237983850141545177639, phi_oneHundredThirtySixED_160788296237983850141545177640, phi_oneHundredThirtySixED_160788296237983850141545177641,
    phi_oneHundredThirtySixED_160788296237983850141545177642, phi_oneHundredThirtySixED_160788296237983850141545177643, phi_oneHundredThirtySixED_160788296237983850141545177644,
    phi_oneHundredThirtySixED_160788296237983850141545177645, phi_oneHundredThirtySixED_160788296237983850141545177646, phi_oneHundredThirtySixED_160788296237983850141545177647,
    phi_oneHundredThirtySixED_160788296237983850141545177648, phi_oneHundredThirtySixED_160788296237983850141545177649, phi_oneHundredThirtySixED_160788296237983850141545177650,
    phi_oneHundredThirtySixED_160788296237983850141545177651, phi_oneHundredThirtySixED_160788296237983850141545177652, phi_oneHundredThirtySixED_160788296237983850141545177653,
    phi_oneHundredThirtySixED_160788296237983850141545177654, phi_oneHundredThirtySixED_160788296237983850141545177655, phi_oneHundredThirtySixED_160788296237983850141545177656,
    phi_oneHundredThirtySixED_160788296237983850141545177657, phi_oneHundredThirtySixED_160788296237983850141545177658, phi_oneHundredThirtySixED_160788296237983850141545177659,
    phi_oneHundredThirtySixED_160788296237983850141545177660, phi_oneHundredThirtySixED_160788296237983850141545177661, phi_oneHundredThirtySixED_160788296237983850141545177662,
    phi_oneHundredThirtySixED_160788296237983850141545177663, phi_oneHundredThirtySixED_160788296237983850141545177664, phi_oneHundredThirtySixED_160788296237983850141545177665,
    phi_oneHundredThirtySixED_160788296237983850141545177666, phi_oneHundredThirtySixED_160788296237983850141545177667, phi_oneHundredThirtySixED_160788296237983850141545177668,
    phi_oneHundredThirtySixED_160788296237983850141545177669, phi_oneHundredThirtySixED_160788296237983850141545177670, phi_oneHundredThirtySixED_160788296237983850141545177671,
    phi_oneHundredThirtySixED_160788296237983850141545177672, phi_oneHundredThirtySixED_160788296237983850141545177673, phi_oneHundredThirtySixED_160788296237983850141545177674,
    phi_oneHundredThirtySixED_160788296237983850141545177675, phi_oneHundredThirtySixED_160788296237983850141545177676, phi_oneHundredThirtySixED_160788296237983850141545177677,
    phi_oneHundredThirtySixED_160788296237983850141545177678, phi_oneHundredThirtySixED_160788296237983850141545177679, phi_oneHundredThirtySixED_160788296237983850141545177680,
    phi_oneHundredThirtySixED_160788296237983850141545177681, phi_oneHundredThirtySixED_160788296237983850141545177682, phi_oneHundredThirtySixED_160788296237983850141545177683,
    phi_oneHundredThirtySixED_160788296237983850141545177684, phi_oneHundredThirtySixED_160788296237983850141545177685, phi_oneHundredThirtySixED_160788296237983850141545177686,
    phi_oneHundredThirtySixED_160788296237983850141545177687, phi_oneHundredThirtySixED_160788296237983850141545177688, phi_oneHundredThirtySixED_160788296237983850141545177689,
    phi_oneHundredThirtySixED_160788296237983850141545177690, phi_oneHundredThirtySixED_160788296237983850141545177691, phi_oneHundredThirtySixED_160788296237983850141545177692,
    phi_oneHundredThirtySixED_160788296237983850141545177693, phi_oneHundredThirtySixED_160788296237983850141545177694, phi_oneHundredThirtySixED_160788296237983850141545177695,
    phi_oneHundredThirtySixED_160788296237983850141545177696, phi_oneHundredThirtySixED_160788296237983850141545177697, phi_oneHundredThirtySixED_160788296237983850141545177698,
    phi_oneHundredThirtySixED_160788296237983850141545177699, phi_oneHundredThirtySixED_160788296237983850141545177700, phi_oneHundredThirtySixED_160788296237983850141545177701
    ]

end TotientTailPeriodKiller
end Erdos249257
