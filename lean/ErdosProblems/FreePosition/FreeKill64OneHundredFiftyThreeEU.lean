import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredFiftyThreeEUFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredFiftyThreeEUFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredFiftyThreeEUFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredFiftyThreeEUFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredFiftyThreeEUFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredFiftyThreeEUFastPow a n * oneHundredFiftyThreeEUFastPow a n * a else oneHundredFiftyThreeEUFastPow a n * oneHundredFiftyThreeEUFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredFiftyThreeEU_2 : Nat.Prime 2 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_3 : Nat.Prime 3 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_5 : Nat.Prime 5 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_7 : Nat.Prime 7 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_11 : Nat.Prime 11 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_13 : Nat.Prime 13 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_17 : Nat.Prime 17 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_19 : Nat.Prime 19 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_23 : Nat.Prime 23 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_29 : Nat.Prime 29 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_31 : Nat.Prime 31 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_37 : Nat.Prime 37 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_41 : Nat.Prime 41 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_43 : Nat.Prime 43 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_47 : Nat.Prime 47 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_53 : Nat.Prime 53 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_59 : Nat.Prime 59 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_61 : Nat.Prime 61 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_67 : Nat.Prime 67 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_71 : Nat.Prime 71 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_73 : Nat.Prime 73 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_79 : Nat.Prime 79 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_83 : Nat.Prime 83 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_89 : Nat.Prime 89 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_97 : Nat.Prime 97 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_101 : Nat.Prime 101 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_103 : Nat.Prime 103 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_107 : Nat.Prime 107 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_109 : Nat.Prime 109 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_113 : Nat.Prime 113 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_127 : Nat.Prime 127 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_131 : Nat.Prime 131 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_137 : Nat.Prime 137 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_139 : Nat.Prime 139 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_149 : Nat.Prime 149 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_151 : Nat.Prime 151 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_157 : Nat.Prime 157 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_163 : Nat.Prime 163 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_167 : Nat.Prime 167 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_173 : Nat.Prime 173 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_179 : Nat.Prime 179 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_181 : Nat.Prime 181 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_191 : Nat.Prime 191 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_193 : Nat.Prime 193 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_197 : Nat.Prime 197 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_223 : Nat.Prime 223 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_227 : Nat.Prime 227 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_229 : Nat.Prime 229 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_239 : Nat.Prime 239 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_241 : Nat.Prime 241 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_251 : Nat.Prime 251 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_257 : Nat.Prime 257 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_263 : Nat.Prime 263 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_269 : Nat.Prime 269 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_271 : Nat.Prime 271 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_277 : Nat.Prime 277 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_283 : Nat.Prime 283 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_293 : Nat.Prime 293 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_307 : Nat.Prime 307 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_311 : Nat.Prime 311 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_317 : Nat.Prime 317 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_331 : Nat.Prime 331 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_347 : Nat.Prime 347 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_349 : Nat.Prime 349 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_353 : Nat.Prime 353 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_359 : Nat.Prime 359 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_367 : Nat.Prime 367 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_373 : Nat.Prime 373 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_379 : Nat.Prime 379 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_383 : Nat.Prime 383 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_419 : Nat.Prime 419 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_433 : Nat.Prime 433 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_457 : Nat.Prime 457 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_463 : Nat.Prime 463 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_479 : Nat.Prime 479 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_487 : Nat.Prime 487 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_509 : Nat.Prime 509 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_521 : Nat.Prime 521 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_523 : Nat.Prime 523 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_541 : Nat.Prime 541 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_557 : Nat.Prime 557 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_563 : Nat.Prime 563 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_577 : Nat.Prime 577 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_587 : Nat.Prime 587 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_599 : Nat.Prime 599 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_619 : Nat.Prime 619 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_631 : Nat.Prime 631 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_641 : Nat.Prime 641 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_661 : Nat.Prime 661 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_683 : Nat.Prime 683 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_691 : Nat.Prime 691 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_727 : Nat.Prime 727 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_733 : Nat.Prime 733 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_739 : Nat.Prime 739 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_757 : Nat.Prime 757 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_761 : Nat.Prime 761 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_769 : Nat.Prime 769 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_773 : Nat.Prime 773 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_787 : Nat.Prime 787 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_877 : Nat.Prime 877 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_887 : Nat.Prime 887 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_907 : Nat.Prime 907 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_929 : Nat.Prime 929 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_937 : Nat.Prime 937 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_953 : Nat.Prime 953 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_977 : Nat.Prime 977 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1033 : Nat.Prime 1033 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1063 : Nat.Prime 1063 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1069 : Nat.Prime 1069 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1097 : Nat.Prime 1097 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1103 : Nat.Prime 1103 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1109 : Nat.Prime 1109 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1129 : Nat.Prime 1129 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1171 : Nat.Prime 1171 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1181 : Nat.Prime 1181 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1187 : Nat.Prime 1187 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1217 : Nat.Prime 1217 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1279 : Nat.Prime 1279 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1429 : Nat.Prime 1429 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1481 : Nat.Prime 1481 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1499 : Nat.Prime 1499 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1511 : Nat.Prime 1511 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1543 : Nat.Prime 1543 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1553 : Nat.Prime 1553 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1571 : Nat.Prime 1571 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1583 : Nat.Prime 1583 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1607 : Nat.Prime 1607 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1609 : Nat.Prime 1609 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1613 : Nat.Prime 1613 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1669 : Nat.Prime 1669 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1699 : Nat.Prime 1699 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1721 : Nat.Prime 1721 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1733 : Nat.Prime 1733 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1787 : Nat.Prime 1787 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1823 : Nat.Prime 1823 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1831 : Nat.Prime 1831 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1847 : Nat.Prime 1847 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1873 : Nat.Prime 1873 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1913 : Nat.Prime 1913 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1973 : Nat.Prime 1973 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1999 : Nat.Prime 1999 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_2063 : Nat.Prime 2063 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_2081 : Nat.Prime 2081 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_2083 : Nat.Prime 2083 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_2087 : Nat.Prime 2087 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_2131 : Nat.Prime 2131 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_2203 : Nat.Prime 2203 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_2213 : Nat.Prime 2213 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_2273 : Nat.Prime 2273 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_2411 : Nat.Prime 2411 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_2423 : Nat.Prime 2423 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_2447 : Nat.Prime 2447 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_2543 : Nat.Prime 2543 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_2683 : Nat.Prime 2683 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_2689 : Nat.Prime 2689 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_2707 : Nat.Prime 2707 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_2797 : Nat.Prime 2797 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_3079 : Nat.Prime 3079 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_3119 : Nat.Prime 3119 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_3457 : Nat.Prime 3457 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_3511 : Nat.Prime 3511 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_3517 : Nat.Prime 3517 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_3593 : Nat.Prime 3593 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_3623 : Nat.Prime 3623 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_3659 : Nat.Prime 3659 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_3673 : Nat.Prime 3673 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_3947 : Nat.Prime 3947 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_4027 : Nat.Prime 4027 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_4099 : Nat.Prime 4099 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_4177 : Nat.Prime 4177 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_4201 : Nat.Prime 4201 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_4259 : Nat.Prime 4259 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_4457 : Nat.Prime 4457 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_4547 : Nat.Prime 4547 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_4597 : Nat.Prime 4597 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_4723 : Nat.Prime 4723 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_4733 : Nat.Prime 4733 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_4793 : Nat.Prime 4793 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_4801 : Nat.Prime 4801 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_4871 : Nat.Prime 4871 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_4877 : Nat.Prime 4877 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_4987 : Nat.Prime 4987 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_5009 : Nat.Prime 5009 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_5039 : Nat.Prime 5039 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_5167 : Nat.Prime 5167 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_5179 : Nat.Prime 5179 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_5519 : Nat.Prime 5519 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_5683 : Nat.Prime 5683 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_5869 : Nat.Prime 5869 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_6011 : Nat.Prime 6011 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_6029 : Nat.Prime 6029 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_6343 : Nat.Prime 6343 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_6359 : Nat.Prime 6359 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_6421 : Nat.Prime 6421 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_6427 : Nat.Prime 6427 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_6469 : Nat.Prime 6469 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_6763 : Nat.Prime 6763 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_6863 : Nat.Prime 6863 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_7039 : Nat.Prime 7039 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_7151 : Nat.Prime 7151 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_7193 : Nat.Prime 7193 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_7211 : Nat.Prime 7211 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_7349 : Nat.Prime 7349 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_7541 : Nat.Prime 7541 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_7621 : Nat.Prime 7621 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_7727 : Nat.Prime 7727 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_7867 : Nat.Prime 7867 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_8423 : Nat.Prime 8423 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_8431 : Nat.Prime 8431 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_8719 : Nat.Prime 8719 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_8753 : Nat.Prime 8753 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_9049 : Nat.Prime 9049 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_9349 : Nat.Prime 9349 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_9491 : Nat.Prime 9491 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_9511 : Nat.Prime 9511 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_9613 : Nat.Prime 9613 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_9677 : Nat.Prime 9677 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_9859 : Nat.Prime 9859 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_10069 : Nat.Prime 10069 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_10853 : Nat.Prime 10853 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_11003 : Nat.Prime 11003 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_11587 : Nat.Prime 11587 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_12203 : Nat.Prime 12203 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_12227 : Nat.Prime 12227 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_12241 : Nat.Prime 12241 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_12487 : Nat.Prime 12487 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_12583 : Nat.Prime 12583 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_12637 : Nat.Prime 12637 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_12899 : Nat.Prime 12899 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_12923 : Nat.Prime 12923 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_13697 : Nat.Prime 13697 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_14033 : Nat.Prime 14033 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_14207 : Nat.Prime 14207 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_16301 : Nat.Prime 16301 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_17203 : Nat.Prime 17203 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_18307 : Nat.Prime 18307 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_19273 : Nat.Prime 19273 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_20599 : Nat.Prime 20599 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_20611 : Nat.Prime 20611 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_20747 : Nat.Prime 20747 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_20753 : Nat.Prime 20753 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_21013 : Nat.Prime 21013 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_21377 : Nat.Prime 21377 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_21481 : Nat.Prime 21481 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_21523 : Nat.Prime 21523 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_21559 : Nat.Prime 21559 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_21563 : Nat.Prime 21563 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_22469 : Nat.Prime 22469 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_23269 : Nat.Prime 23269 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_23509 : Nat.Prime 23509 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_24697 : Nat.Prime 24697 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_24847 : Nat.Prime 24847 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_25117 : Nat.Prime 25117 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_26783 : Nat.Prime 26783 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_26927 : Nat.Prime 26927 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_28181 : Nat.Prime 28181 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_28393 : Nat.Prime 28393 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_28403 : Nat.Prime 28403 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_29437 : Nat.Prime 29437 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_31177 : Nat.Prime 31177 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_32363 : Nat.Prime 32363 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_33487 : Nat.Prime 33487 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_34337 : Nat.Prime 34337 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_39623 : Nat.Prime 39623 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_40433 : Nat.Prime 40433 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_41269 : Nat.Prime 41269 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_41543 : Nat.Prime 41543 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_41999 : Nat.Prime 41999 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_42323 : Nat.Prime 42323 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_43177 : Nat.Prime 43177 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_43801 : Nat.Prime 43801 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_46919 : Nat.Prime 46919 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_47317 : Nat.Prime 47317 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_48487 : Nat.Prime 48487 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_49547 : Nat.Prime 49547 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_49663 : Nat.Prime 49663 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_49787 : Nat.Prime 49787 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_50087 : Nat.Prime 50087 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_50177 : Nat.Prime 50177 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_55589 : Nat.Prime 55589 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_56093 : Nat.Prime 56093 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_58937 : Nat.Prime 58937 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_63803 : Nat.Prime 63803 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_64063 : Nat.Prime 64063 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_64577 : Nat.Prime 64577 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_65731 : Nat.Prime 65731 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_66949 : Nat.Prime 66949 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_72617 : Nat.Prime 72617 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_75709 : Nat.Prime 75709 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_76871 : Nat.Prime 76871 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_77249 : Nat.Prime 77249 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_77269 : Nat.Prime 77269 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_77557 : Nat.Prime 77557 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_79847 : Nat.Prime 79847 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_79973 : Nat.Prime 79973 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_89597 : Nat.Prime 89597 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_92179 : Nat.Prime 92179 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_95723 : Nat.Prime 95723 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_96431 : Nat.Prime 96431 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_100699 : Nat.Prime 100699 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_100981 : Nat.Prime 100981 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_107923 : Nat.Prime 107923 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_108011 : Nat.Prime 108011 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_108217 : Nat.Prime 108217 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_109303 : Nat.Prime 109303 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_110017 : Nat.Prime 110017 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_110119 : Nat.Prime 110119 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_115853 : Nat.Prime 115853 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_131783 : Nat.Prime 131783 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_132173 : Nat.Prime 132173 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_138967 : Nat.Prime 138967 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_149861 : Nat.Prime 149861 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_153641 : Nat.Prime 153641 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_159013 : Nat.Prime 159013 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_160583 : Nat.Prime 160583 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_167267 : Nat.Prime 167267 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_171401 : Nat.Prime 171401 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_175873 : Nat.Prime 175873 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_185723 : Nat.Prime 185723 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_187303 : Nat.Prime 187303 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_188911 : Nat.Prime 188911 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_200927 : Nat.Prime 200927 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_202747 : Nat.Prime 202747 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_207709 : Nat.Prime 207709 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_219533 : Nat.Prime 219533 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_219983 : Nat.Prime 219983 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_228797 : Nat.Prime 228797 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_230149 : Nat.Prime 230149 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_242173 : Nat.Prime 242173 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_247739 : Nat.Prime 247739 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_254899 : Nat.Prime 254899 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_256163 : Nat.Prime 256163 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_274139 : Nat.Prime 274139 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_284509 : Nat.Prime 284509 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_284833 : Nat.Prime 284833 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_298999 : Nat.Prime 298999 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_334973 : Nat.Prime 334973 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_361871 : Nat.Prime 361871 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_450301 : Nat.Prime 450301 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_480827 : Nat.Prime 480827 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_493813 : Nat.Prime 493813 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_552127 : Nat.Prime 552127 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_563747 : Nat.Prime 563747 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_576721 : Nat.Prime 576721 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_596257 : Nat.Prime 596257 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_614279 : Nat.Prime 614279 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_652969 : Nat.Prime 652969 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_674117 : Nat.Prime 674117 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_676747 : Nat.Prime 676747 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_684109 : Nat.Prime 684109 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_685459 : Nat.Prime 685459 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_688907 : Nat.Prime 688907 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_723413 : Nat.Prime 723413 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_765727 : Nat.Prime 765727 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_770039 : Nat.Prime 770039 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_773879 : Nat.Prime 773879 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_778091 : Nat.Prime 778091 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_862973 : Nat.Prime 862973 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_921143 : Nat.Prime 921143 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_941329 : Nat.Prime 941329 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_947357 : Nat.Prime 947357 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1047979 : Nat.Prime 1047979 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1086299 : Nat.Prime 1086299 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1094963 : Nat.Prime 1094963 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1152937 : Nat.Prime 1152937 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1221503 : Nat.Prime 1221503 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1226549 : Nat.Prime 1226549 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1268167 : Nat.Prime 1268167 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1446559 : Nat.Prime 1446559 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1511891 : Nat.Prime 1511891 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1521103 : Nat.Prime 1521103 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1545641 : Nat.Prime 1545641 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1688987 : Nat.Prime 1688987 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_1736981 : Nat.Prime 1736981 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_2040653 : Nat.Prime 2040653 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_2162911 : Nat.Prime 2162911 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_2169397 : Nat.Prime 2169397 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_2207411 : Nat.Prime 2207411 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_2347369 : Nat.Prime 2347369 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_2717291 : Nat.Prime 2717291 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_2951537 : Nat.Prime 2951537 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_3093359 : Nat.Prime 3093359 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_3161023 : Nat.Prime 3161023 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_3162499 : Nat.Prime 3162499 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_3259561 : Nat.Prime 3259561 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_3437719 : Nat.Prime 3437719 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_3677579 : Nat.Prime 3677579 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_3766153 : Nat.Prime 3766153 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_4194847 : Nat.Prime 4194847 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_4382047 : Nat.Prime 4382047 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_4556173 : Nat.Prime 4556173 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_4924013 : Nat.Prime 4924013 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_5583499 : Nat.Prime 5583499 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_5816549 : Nat.Prime 5816549 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_5867531 : Nat.Prime 5867531 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_6207491 : Nat.Prime 6207491 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_6531181 : Nat.Prime 6531181 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_6724951 : Nat.Prime 6724951 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_7504733 : Nat.Prime 7504733 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_7639153 : Nat.Prime 7639153 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_7682107 : Nat.Prime 7682107 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_7711703 : Nat.Prime 7711703 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_8303717 : Nat.Prime 8303717 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_10003657 : Nat.Prime 10003657 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_10008491 : Nat.Prime 10008491 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_10097959 : Nat.Prime 10097959 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_10209449 : Nat.Prime 10209449 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_10332431 : Nat.Prime 10332431 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_10629859 : Nat.Prime 10629859 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_10820141 : Nat.Prime 10820141 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_11349763 : Nat.Prime 11349763 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_11676701 : Nat.Prime 11676701 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_12802483 : Nat.Prime 12802483 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_12857951 : Nat.Prime 12857951 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_13026067 : Nat.Prime 13026067 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_13581397 : Nat.Prime 13581397 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_14108707 : Nat.Prime 14108707 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_15096281 : Nat.Prime 15096281 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_15969601 : Nat.Prime 15969601 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_19973323 : Nat.Prime 19973323 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_22010179 : Nat.Prime 22010179 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_27625669 : Nat.Prime 27625669 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_28985921 : Nat.Prime 28985921 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_29700119 : Nat.Prime 29700119 := by
  norm_num

private theorem prime_oneHundredFiftyThreeEU_30237821 : Nat.Prime 30237821 := by
  apply lucas_primality 30237821 (2 : ZMod 30237821)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1511891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1511891, 1)] : List FactorBlock).map factorBlockValue).prod) = 30237821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_1511891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30237821) ^ 15118910 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 30237821) ^ 6047564 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 30237821) ^ 20 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_32218313 : Nat.Prime 32218313 := by
  apply lucas_primality 32218313 (5 : ZMod 32218313)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (47, 1), (12241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (47, 1), (12241, 1)] : List FactorBlock).map factorBlockValue).prod) = 32218313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_47
      · exact prime_oneHundredFiftyThreeEU_12241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 32218313) ^ 16109156 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 32218313) ^ 4602616 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 32218313) ^ 685496 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 32218313) ^ 2632 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_34135747 : Nat.Prime 34135747 := by
  apply lucas_primality 34135747 (3 : ZMod 34135747)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1187, 1), (4793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1187, 1), (4793, 1)] : List FactorBlock).map factorBlockValue).prod) = 34135747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_1187
      · exact prime_oneHundredFiftyThreeEU_4793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 34135747) ^ 17067873 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 34135747) ^ 11378582 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 34135747) ^ 28758 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 34135747) ^ 7122 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_34418159 : Nat.Prime 34418159 := by
  apply lucas_primality 34418159 (17 : ZMod 34418159)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (587, 1), (1543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (587, 1), (1543, 1)] : List FactorBlock).map factorBlockValue).prod) = 34418159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_19
      · exact prime_oneHundredFiftyThreeEU_587
      · exact prime_oneHundredFiftyThreeEU_1543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 34418159) ^ 17209079 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (17 : ZMod 34418159) ^ 1811482 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (17 : ZMod 34418159) ^ 58634 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (17 : ZMod 34418159) ^ 22306 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_35002367 : Nat.Prime 35002367 := by
  apply lucas_primality 35002367 (5 : ZMod 35002367)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (23, 1), (53, 1), (293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (23, 1), (53, 1), (293, 1)] : List FactorBlock).map factorBlockValue).prod) = 35002367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_23
      · exact prime_oneHundredFiftyThreeEU_53
      · exact prime_oneHundredFiftyThreeEU_293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 35002367) ^ 17501183 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 35002367) ^ 5000338 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 35002367) ^ 1521842 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 35002367) ^ 660422 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 35002367) ^ 119462 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_36456613 : Nat.Prime 36456613 := by
  apply lucas_primality 36456613 (6 : ZMod 36456613)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (107, 1), (28393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (107, 1), (28393, 1)] : List FactorBlock).map factorBlockValue).prod) = 36456613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_107
      · exact prime_oneHundredFiftyThreeEU_28393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 36456613) ^ 18228306 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 36456613) ^ 12152204 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 36456613) ^ 340716 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 36456613) ^ 1284 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_37097537 : Nat.Prime 37097537 := by
  apply lucas_primality 37097537 (3 : ZMod 37097537)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (17, 1), (4871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (17, 1), (4871, 1)] : List FactorBlock).map factorBlockValue).prod) = 37097537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_17
      · exact prime_oneHundredFiftyThreeEU_4871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 37097537) ^ 18548768 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 37097537) ^ 5299648 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 37097537) ^ 2182208 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 37097537) ^ 7616 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_37266179 : Nat.Prime 37266179 := by
  apply lucas_primality 37266179 (2 : ZMod 37266179)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (139, 1), (3623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (139, 1), (3623, 1)] : List FactorBlock).map factorBlockValue).prod) = 37266179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_37
      · exact prime_oneHundredFiftyThreeEU_139
      · exact prime_oneHundredFiftyThreeEU_3623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 37266179) ^ 18633089 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 37266179) ^ 1007194 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 37266179) ^ 268102 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 37266179) ^ 10286 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_42472741 : Nat.Prime 42472741 := by
  apply lucas_primality 42472741 (2 : ZMod 42472741)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (137, 1), (5167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (137, 1), (5167, 1)] : List FactorBlock).map factorBlockValue).prod) = 42472741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_137
      · exact prime_oneHundredFiftyThreeEU_5167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 42472741) ^ 21236370 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 42472741) ^ 14157580 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 42472741) ^ 8494548 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 42472741) ^ 310020 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 42472741) ^ 8220 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_43535477 : Nat.Prime 43535477 := by
  apply lucas_primality 43535477 (2 : ZMod 43535477)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1481, 1), (7349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1481, 1), (7349, 1)] : List FactorBlock).map factorBlockValue).prod) = 43535477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_1481
      · exact prime_oneHundredFiftyThreeEU_7349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 43535477) ^ 21767738 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 43535477) ^ 29396 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 43535477) ^ 5924 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_44443171 : Nat.Prime 44443171 := by
  apply lucas_primality 44443171 (2 : ZMod 44443171)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (493813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (493813, 1)] : List FactorBlock).map factorBlockValue).prod) = 44443171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_493813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 44443171) ^ 22221585 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 44443171) ^ 14814390 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 44443171) ^ 8888634 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 44443171) ^ 90 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_44461057 : Nat.Prime 44461057 := by
  apply lucas_primality 44461057 (5 : ZMod 44461057)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (3, 1), (41, 1), (353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (3, 1), (41, 1), (353, 1)] : List FactorBlock).map factorBlockValue).prod) = 44461057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_41
      · exact prime_oneHundredFiftyThreeEU_353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 44461057) ^ 22230528 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 44461057) ^ 14820352 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 44461057) ^ 1084416 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 44461057) ^ 125952 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_45991931 : Nat.Prime 45991931 := by
  apply lucas_primality 45991931 (2 : ZMod 45991931)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1699, 1), (2707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1699, 1), (2707, 1)] : List FactorBlock).map factorBlockValue).prod) = 45991931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_1699
      · exact prime_oneHundredFiftyThreeEU_2707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 45991931) ^ 22995965 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 45991931) ^ 9198386 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 45991931) ^ 27070 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 45991931) ^ 16990 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_47582281 : Nat.Prime 47582281 := by
  apply lucas_primality 47582281 (7 : ZMod 47582281)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (132173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (132173, 1)] : List FactorBlock).map factorBlockValue).prod) = 47582281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_132173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 47582281) ^ 23791140 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 47582281) ^ 15860760 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 47582281) ^ 9516456 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 47582281) ^ 360 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_49213049 : Nat.Prime 49213049 := by
  apply lucas_primality 49213049 (3 : ZMod 49213049)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (433, 1), (14207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (433, 1), (14207, 1)] : List FactorBlock).map factorBlockValue).prod) = 49213049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_433
      · exact prime_oneHundredFiftyThreeEU_14207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 49213049) ^ 24606524 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 49213049) ^ 113656 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 49213049) ^ 3464 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_50689799 : Nat.Prime 50689799 := by
  apply lucas_primality 50689799 (29 : ZMod 50689799)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (587, 1), (43177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (587, 1), (43177, 1)] : List FactorBlock).map factorBlockValue).prod) = 50689799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_587
      · exact prime_oneHundredFiftyThreeEU_43177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (29 : ZMod 50689799) ^ 25344899 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (29 : ZMod 50689799) ^ 86354 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (29 : ZMod 50689799) ^ 1174 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_51429551 : Nat.Prime 51429551 := by
  apply lucas_primality 51429551 (17 : ZMod 51429551)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (107, 1), (9613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (107, 1), (9613, 1)] : List FactorBlock).map factorBlockValue).prod) = 51429551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_107
      · exact prime_oneHundredFiftyThreeEU_9613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 51429551) ^ 25714775 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (17 : ZMod 51429551) ^ 10285910 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (17 : ZMod 51429551) ^ 480650 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (17 : ZMod 51429551) ^ 5350 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_52142353 : Nat.Prime 52142353 := by
  apply lucas_primality 52142353 (10 : ZMod 52142353)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (1086299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (1086299, 1)] : List FactorBlock).map factorBlockValue).prod) = 52142353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_1086299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 52142353) ^ 26071176 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (10 : ZMod 52142353) ^ 17380784 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (10 : ZMod 52142353) ^ 48 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_52623773 : Nat.Prime 52623773 := by
  apply lucas_primality 52623773 (2 : ZMod 52623773)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (773879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (773879, 1)] : List FactorBlock).map factorBlockValue).prod) = 52623773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_17
      · exact prime_oneHundredFiftyThreeEU_773879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 52623773) ^ 26311886 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 52623773) ^ 3095516 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 52623773) ^ 68 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_57868189 : Nat.Prime 57868189 := by
  apply lucas_primality 57868189 (2 : ZMod 57868189)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (688907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (688907, 1)] : List FactorBlock).map factorBlockValue).prod) = 57868189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_688907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 57868189) ^ 28934094 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 57868189) ^ 19289396 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 57868189) ^ 8266884 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 57868189) ^ 84 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_57971843 : Nat.Prime 57971843 := by
  apply lucas_primality 57971843 (2 : ZMod 57971843)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (28985921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (28985921, 1)] : List FactorBlock).map factorBlockValue).prod) = 57971843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_28985921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 57971843) ^ 28985921 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 57971843) ^ 2 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_60710329 : Nat.Prime 60710329 := by
  apply lucas_primality 60710329 (29 : ZMod 60710329)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (163, 1), (739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (163, 1), (739, 1)] : List FactorBlock).map factorBlockValue).prod) = 60710329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_163
      · exact prime_oneHundredFiftyThreeEU_739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 60710329) ^ 30355164 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (29 : ZMod 60710329) ^ 20236776 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (29 : ZMod 60710329) ^ 8672904 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (29 : ZMod 60710329) ^ 372456 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (29 : ZMod 60710329) ^ 82152 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_61239001 : Nat.Prime 61239001 := by
  apply lucas_primality 61239001 (17 : ZMod 61239001)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 3), (137, 1), (149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 3), (137, 1), (149, 1)] : List FactorBlock).map factorBlockValue).prod) = 61239001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_137
      · exact prime_oneHundredFiftyThreeEU_149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 61239001) ^ 30619500 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (17 : ZMod 61239001) ^ 20413000 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (17 : ZMod 61239001) ^ 12247800 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (17 : ZMod 61239001) ^ 447000 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (17 : ZMod 61239001) ^ 411000 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_61405583 : Nat.Prime 61405583 := by
  apply lucas_primality 61405583 (5 : ZMod 61405583)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (149, 1), (29437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (149, 1), (29437, 1)] : List FactorBlock).map factorBlockValue).prod) = 61405583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_149
      · exact prime_oneHundredFiftyThreeEU_29437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 61405583) ^ 30702791 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 61405583) ^ 8772226 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 61405583) ^ 412118 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 61405583) ^ 2086 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_61483663 : Nat.Prime 61483663 := by
  apply lucas_primality 61483663 (3 : ZMod 61483663)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (200927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (200927, 1)] : List FactorBlock).map factorBlockValue).prod) = 61483663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_17
      · exact prime_oneHundredFiftyThreeEU_200927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 61483663) ^ 30741831 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 61483663) ^ 20494554 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 61483663) ^ 3616686 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 61483663) ^ 306 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_71924353 : Nat.Prime 71924353 := by
  apply lucas_primality 71924353 (5 : ZMod 71924353)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (187303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (187303, 1)] : List FactorBlock).map factorBlockValue).prod) = 71924353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_187303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 71924353) ^ 35962176 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 71924353) ^ 23974784 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 71924353) ^ 384 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_73978211 : Nat.Prime 73978211 := by
  apply lucas_primality 73978211 (2 : ZMod 73978211)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (353, 1), (1103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (353, 1), (1103, 1)] : List FactorBlock).map factorBlockValue).prod) = 73978211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_19
      · exact prime_oneHundredFiftyThreeEU_353
      · exact prime_oneHundredFiftyThreeEU_1103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 73978211) ^ 36989105 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 73978211) ^ 14795642 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 73978211) ^ 3893590 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 73978211) ^ 209570 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 73978211) ^ 67070 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_75436789 : Nat.Prime 75436789 := by
  apply lucas_primality 75436789 (10 : ZMod 75436789)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (103, 1), (8719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (103, 1), (8719, 1)] : List FactorBlock).map factorBlockValue).prod) = 75436789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_103
      · exact prime_oneHundredFiftyThreeEU_8719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 75436789) ^ 37718394 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (10 : ZMod 75436789) ^ 25145596 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (10 : ZMod 75436789) ^ 10776684 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (10 : ZMod 75436789) ^ 732396 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (10 : ZMod 75436789) ^ 8652 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_76821071 : Nat.Prime 76821071 := by
  apply lucas_primality 76821071 (13 : ZMod 76821071)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7682107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7682107, 1)] : List FactorBlock).map factorBlockValue).prod) = 76821071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_7682107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 76821071) ^ 38410535 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (13 : ZMod 76821071) ^ 15364214 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (13 : ZMod 76821071) ^ 10 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_82529879 : Nat.Prime 82529879 := by
  apply lucas_primality 82529879 (11 : ZMod 82529879)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (89, 1), (5869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (89, 1), (5869, 1)] : List FactorBlock).map factorBlockValue).prod) = 82529879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_79
      · exact prime_oneHundredFiftyThreeEU_89
      · exact prime_oneHundredFiftyThreeEU_5869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 82529879) ^ 41264939 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 82529879) ^ 1044682 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 82529879) ^ 927302 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 82529879) ^ 14062 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_103221763 : Nat.Prime 103221763 := by
  apply lucas_primality 103221763 (2 : ZMod 103221763)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (1181, 1), (2081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (1181, 1), (2081, 1)] : List FactorBlock).map factorBlockValue).prod) = 103221763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_1181
      · exact prime_oneHundredFiftyThreeEU_2081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 103221763) ^ 51610881 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 103221763) ^ 34407254 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 103221763) ^ 14745966 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 103221763) ^ 87402 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 103221763) ^ 49602 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_107999813 : Nat.Prime 107999813 := by
  apply lucas_primality 107999813 (2 : ZMod 107999813)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (241, 1), (4871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (241, 1), (4871, 1)] : List FactorBlock).map factorBlockValue).prod) = 107999813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_23
      · exact prime_oneHundredFiftyThreeEU_241
      · exact prime_oneHundredFiftyThreeEU_4871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 107999813) ^ 53999906 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 107999813) ^ 4695644 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 107999813) ^ 448132 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 107999813) ^ 22172 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_122513389 : Nat.Prime 122513389 := by
  apply lucas_primality 122513389 (2 : ZMod 122513389)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (10209449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (10209449, 1)] : List FactorBlock).map factorBlockValue).prod) = 122513389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_10209449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 122513389) ^ 61256694 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 122513389) ^ 40837796 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 122513389) ^ 12 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_129867629 : Nat.Prime 129867629 := by
  apply lucas_primality 129867629 (2 : ZMod 129867629)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (2951537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (2951537, 1)] : List FactorBlock).map factorBlockValue).prod) = 129867629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_11
      · exact prime_oneHundredFiftyThreeEU_2951537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 129867629) ^ 64933814 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 129867629) ^ 11806148 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 129867629) ^ 44 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_131433079 : Nat.Prime 131433079 := by
  apply lucas_primality 131433079 (17 : ZMod 131433079)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (223, 1), (14033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (223, 1), (14033, 1)] : List FactorBlock).map factorBlockValue).prod) = 131433079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_223
      · exact prime_oneHundredFiftyThreeEU_14033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 131433079) ^ 65716539 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (17 : ZMod 131433079) ^ 43811026 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (17 : ZMod 131433079) ^ 18776154 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (17 : ZMod 131433079) ^ 589386 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (17 : ZMod 131433079) ^ 9366 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_139568171 : Nat.Prime 139568171 := by
  apply lucas_primality 139568171 (2 : ZMod 139568171)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (284833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (284833, 1)] : List FactorBlock).map factorBlockValue).prod) = 139568171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_284833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 139568171) ^ 69784085 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 139568171) ^ 27913634 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 139568171) ^ 19938310 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 139568171) ^ 490 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_140647657 : Nat.Prime 140647657 := by
  apply lucas_primality 140647657 (5 : ZMod 140647657)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (37, 1), (149, 1), (1063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (37, 1), (149, 1), (1063, 1)] : List FactorBlock).map factorBlockValue).prod) = 140647657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_37
      · exact prime_oneHundredFiftyThreeEU_149
      · exact prime_oneHundredFiftyThreeEU_1063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 140647657) ^ 70323828 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 140647657) ^ 46882552 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 140647657) ^ 3801288 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 140647657) ^ 943944 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 140647657) ^ 132312 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_147580427 : Nat.Prime 147580427 := by
  apply lucas_primality 147580427 (2 : ZMod 147580427)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (307, 1), (34337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (307, 1), (34337, 1)] : List FactorBlock).map factorBlockValue).prod) = 147580427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_307
      · exact prime_oneHundredFiftyThreeEU_34337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 147580427) ^ 73790213 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 147580427) ^ 21082918 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 147580427) ^ 480718 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 147580427) ^ 4298 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_153642143 : Nat.Prime 153642143 := by
  apply lucas_primality 153642143 (5 : ZMod 153642143)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (76821071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (76821071, 1)] : List FactorBlock).map factorBlockValue).prod) = 153642143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_76821071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 153642143) ^ 76821071 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 153642143) ^ 2 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_155196169 : Nat.Prime 155196169 := by
  apply lucas_primality 155196169 (13 : ZMod 155196169)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (29, 1), (31, 1), (7193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (29, 1), (31, 1), (7193, 1)] : List FactorBlock).map factorBlockValue).prod) = 155196169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_29
      · exact prime_oneHundredFiftyThreeEU_31
      · exact prime_oneHundredFiftyThreeEU_7193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 155196169) ^ 77598084 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (13 : ZMod 155196169) ^ 51732056 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (13 : ZMod 155196169) ^ 5351592 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (13 : ZMod 155196169) ^ 5006328 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (13 : ZMod 155196169) ^ 21576 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_177462421 : Nat.Prime 177462421 := by
  apply lucas_primality 177462421 (7 : ZMod 177462421)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (61, 1), (48487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (61, 1), (48487, 1)] : List FactorBlock).map factorBlockValue).prod) = 177462421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_61
      · exact prime_oneHundredFiftyThreeEU_48487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 177462421) ^ 88731210 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 177462421) ^ 59154140 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 177462421) ^ 35492484 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 177462421) ^ 2909220 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 177462421) ^ 3660 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_204603907 : Nat.Prime 204603907 := by
  apply lucas_primality 204603907 (7 : ZMod 204603907)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 2), (23, 1), (31, 1), (283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 2), (23, 1), (31, 1), (283, 1)] : List FactorBlock).map factorBlockValue).prod) = 204603907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_13
      · exact prime_oneHundredFiftyThreeEU_23
      · exact prime_oneHundredFiftyThreeEU_31
      · exact prime_oneHundredFiftyThreeEU_283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 204603907) ^ 102301953 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 204603907) ^ 68201302 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 204603907) ^ 15738762 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 204603907) ^ 8895822 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 204603907) ^ 6600126 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 204603907) ^ 722982 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_212514941 : Nat.Prime 212514941 := by
  apply lucas_primality 212514941 (2 : ZMod 212514941)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (23, 1), (41999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (23, 1), (41999, 1)] : List FactorBlock).map factorBlockValue).prod) = 212514941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_11
      · exact prime_oneHundredFiftyThreeEU_23
      · exact prime_oneHundredFiftyThreeEU_41999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 212514941) ^ 106257470 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 212514941) ^ 42502988 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 212514941) ^ 19319540 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 212514941) ^ 9239780 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 212514941) ^ 5060 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_218739679 : Nat.Prime 218739679 := by
  apply lucas_primality 218739679 (6 : ZMod 218739679)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (36456613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (36456613, 1)] : List FactorBlock).map factorBlockValue).prod) = 218739679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_36456613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 218739679) ^ 109369839 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 218739679) ^ 72913226 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 218739679) ^ 6 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_231692401 : Nat.Prime 231692401 := by
  apply lucas_primality 231692401 (11 : ZMod 231692401)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (5, 2), (7151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (5, 2), (7151, 1)] : List FactorBlock).map factorBlockValue).prod) = 231692401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_7151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 231692401) ^ 115846200 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 231692401) ^ 77230800 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 231692401) ^ 46338480 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 231692401) ^ 32400 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_236802743 : Nat.Prime 236802743 := by
  apply lucas_primality 236802743 (5 : ZMod 236802743)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (1069, 1), (10069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (1069, 1), (10069, 1)] : List FactorBlock).map factorBlockValue).prod) = 236802743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_11
      · exact prime_oneHundredFiftyThreeEU_1069
      · exact prime_oneHundredFiftyThreeEU_10069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 236802743) ^ 118401371 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 236802743) ^ 21527522 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 236802743) ^ 221518 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 236802743) ^ 23518 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_240339023 : Nat.Prime 240339023 := by
  apply lucas_primality 240339023 (7 : ZMod 240339023)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (11, 1), (113, 1), (1973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (11, 1), (113, 1), (1973, 1)] : List FactorBlock).map factorBlockValue).prod) = 240339023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_11
      · exact prime_oneHundredFiftyThreeEU_113
      · exact prime_oneHundredFiftyThreeEU_1973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 240339023) ^ 120169511 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 240339023) ^ 34334146 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 240339023) ^ 21849002 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 240339023) ^ 2126894 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 240339023) ^ 121814 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_272706869 : Nat.Prime 272706869 := by
  apply lucas_primality 272706869 (2 : ZMod 272706869)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (101, 1), (96431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (101, 1), (96431, 1)] : List FactorBlock).map factorBlockValue).prod) = 272706869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_101
      · exact prime_oneHundredFiftyThreeEU_96431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 272706869) ^ 136353434 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 272706869) ^ 38958124 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 272706869) ^ 2700068 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 272706869) ^ 2828 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_273126599 : Nat.Prime 273126599 := by
  apply lucas_primality 273126599 (7 : ZMod 273126599)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (10853, 1), (12583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (10853, 1), (12583, 1)] : List FactorBlock).map factorBlockValue).prod) = 273126599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_10853
      · exact prime_oneHundredFiftyThreeEU_12583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 273126599) ^ 136563299 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 273126599) ^ 25166 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 273126599) ^ 21706 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_275924861 : Nat.Prime 275924861 := by
  apply lucas_primality 275924861 (2 : ZMod 275924861)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (641, 1), (21523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (641, 1), (21523, 1)] : List FactorBlock).map factorBlockValue).prod) = 275924861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_641
      · exact prime_oneHundredFiftyThreeEU_21523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 275924861) ^ 137962430 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 275924861) ^ 55184972 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 275924861) ^ 430460 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 275924861) ^ 12820 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_307259593 : Nat.Prime 307259593 := by
  apply lucas_primality 307259593 (15 : ZMod 307259593)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (12802483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (12802483, 1)] : List FactorBlock).map factorBlockValue).prod) = 307259593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_12802483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (15 : ZMod 307259593) ^ 153629796 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (15 : ZMod 307259593) ^ 102419864 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (15 : ZMod 307259593) ^ 24 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_414065633 : Nat.Prime 414065633 := by
  apply lucas_primality 414065633 (3 : ZMod 414065633)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (19, 1), (197, 1), (3457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (19, 1), (197, 1), (3457, 1)] : List FactorBlock).map factorBlockValue).prod) = 414065633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_19
      · exact prime_oneHundredFiftyThreeEU_197
      · exact prime_oneHundredFiftyThreeEU_3457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 414065633) ^ 207032816 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 414065633) ^ 21792928 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 414065633) ^ 2101856 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 414065633) ^ 119776 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_440482171 : Nat.Prime 440482171 := by
  apply lucas_primality 440482171 (2 : ZMod 440482171)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (631, 1), (23269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (631, 1), (23269, 1)] : List FactorBlock).map factorBlockValue).prod) = 440482171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_631
      · exact prime_oneHundredFiftyThreeEU_23269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 440482171) ^ 220241085 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 440482171) ^ 146827390 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 440482171) ^ 88096434 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 440482171) ^ 698070 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 440482171) ^ 18930 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_458839891 : Nat.Prime 458839891 := by
  apply lucas_primality 458839891 (10 : ZMod 458839891)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 6), (5, 1), (113, 1), (557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 6), (5, 1), (113, 1), (557, 1)] : List FactorBlock).map factorBlockValue).prod) = 458839891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_113
      · exact prime_oneHundredFiftyThreeEU_557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 458839891) ^ 229419945 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (10 : ZMod 458839891) ^ 152946630 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (10 : ZMod 458839891) ^ 91767978 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (10 : ZMod 458839891) ^ 4060530 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (10 : ZMod 458839891) ^ 823770 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_470002843 : Nat.Prime 470002843 := by
  apply lucas_primality 470002843 (2 : ZMod 470002843)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (31, 1), (49547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (31, 1), (49547, 1)] : List FactorBlock).map factorBlockValue).prod) = 470002843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_17
      · exact prime_oneHundredFiftyThreeEU_31
      · exact prime_oneHundredFiftyThreeEU_49547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 470002843) ^ 235001421 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 470002843) ^ 156667614 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 470002843) ^ 27647226 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 470002843) ^ 15161382 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 470002843) ^ 9486 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_602551073 : Nat.Prime 602551073 := by
  apply lucas_primality 602551073 (3 : ZMod 602551073)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (977, 1), (19273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (977, 1), (19273, 1)] : List FactorBlock).map factorBlockValue).prod) = 602551073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_977
      · exact prime_oneHundredFiftyThreeEU_19273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 602551073) ^ 301275536 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 602551073) ^ 616736 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 602551073) ^ 31264 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_614836631 : Nat.Prime 614836631 := by
  apply lucas_primality 614836631 (13 : ZMod 614836631)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (61483663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (61483663, 1)] : List FactorBlock).map factorBlockValue).prod) = 614836631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_61483663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 614836631) ^ 307418315 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (13 : ZMod 614836631) ^ 122967326 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (13 : ZMod 614836631) ^ 10 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_640433267 : Nat.Prime 640433267 := by
  apply lucas_primality 640433267 (2 : ZMod 640433267)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) = 640433267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_11
      · exact prime_oneHundredFiftyThreeEU_19
      · exact prime_oneHundredFiftyThreeEU_61
      · exact prime_oneHundredFiftyThreeEU_25117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 640433267) ^ 320216633 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 58221206 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 33707014 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 10498906 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 25498 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_695525527 : Nat.Prime 695525527 := by
  apply lucas_primality 695525527 (5 : ZMod 695525527)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (67, 1), (576721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (67, 1), (576721, 1)] : List FactorBlock).map factorBlockValue).prod) = 695525527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_67
      · exact prime_oneHundredFiftyThreeEU_576721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 695525527) ^ 347762763 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 695525527) ^ 231841842 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 695525527) ^ 10380978 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 695525527) ^ 1206 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_17203
      · exact prime_oneHundredFiftyThreeEU_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_724479211 : Nat.Prime 724479211 := by
  apply lucas_primality 724479211 (10 : ZMod 724479211)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 2), (13, 1), (12637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 2), (13, 1), (12637, 1)] : List FactorBlock).map factorBlockValue).prod) = 724479211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_13
      · exact prime_oneHundredFiftyThreeEU_12637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 724479211) ^ 362239605 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (10 : ZMod 724479211) ^ 241493070 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (10 : ZMod 724479211) ^ 144895842 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (10 : ZMod 724479211) ^ 103497030 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (10 : ZMod 724479211) ^ 55729170 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (10 : ZMod 724479211) ^ 57330 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_868526531 : Nat.Prime 868526531 := by
  apply lucas_primality 868526531 (6 : ZMod 868526531)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37, 1), (2347369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37, 1), (2347369, 1)] : List FactorBlock).map factorBlockValue).prod) = 868526531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_37
      · exact prime_oneHundredFiftyThreeEU_2347369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 868526531) ^ 434263265 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 868526531) ^ 173705306 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 868526531) ^ 23473690 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 868526531) ^ 370 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_906208483 : Nat.Prime 906208483 := by
  apply lucas_primality 906208483 (2 : ZMod 906208483)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (131, 1), (1152937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (131, 1), (1152937, 1)] : List FactorBlock).map factorBlockValue).prod) = 906208483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_131
      · exact prime_oneHundredFiftyThreeEU_1152937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 906208483) ^ 453104241 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 906208483) ^ 302069494 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 906208483) ^ 6917622 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 906208483) ^ 786 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_1059348967 : Nat.Prime 1059348967 := by
  apply lucas_primality 1059348967 (3 : ZMod 1059348967)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (13581397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (13581397, 1)] : List FactorBlock).map factorBlockValue).prod) = 1059348967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_13
      · exact prime_oneHundredFiftyThreeEU_13581397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1059348967) ^ 529674483 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1059348967) ^ 353116322 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1059348967) ^ 81488382 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1059348967) ^ 78 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_1174361849 : Nat.Prime 1174361849 := by
  apply lucas_primality 1174361849 (3 : ZMod 1174361849)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (619, 1), (21559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (619, 1), (21559, 1)] : List FactorBlock).map factorBlockValue).prod) = 1174361849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_11
      · exact prime_oneHundredFiftyThreeEU_619
      · exact prime_oneHundredFiftyThreeEU_21559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1174361849) ^ 587180924 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1174361849) ^ 106760168 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1174361849) ^ 1897192 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1174361849) ^ 54472 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_1267755761 : Nat.Prime 1267755761 := by
  apply lucas_primality 1267755761 (6 : ZMod 1267755761)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (53, 1), (298999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (53, 1), (298999, 1)] : List FactorBlock).map factorBlockValue).prod) = 1267755761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_53
      · exact prime_oneHundredFiftyThreeEU_298999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1267755761) ^ 633877880 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 1267755761) ^ 253551152 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 1267755761) ^ 23919920 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 1267755761) ^ 4240 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_1381588001 : Nat.Prime 1381588001 := by
  apply lucas_primality 1381588001 (3 : ZMod 1381588001)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 3), (13, 1), (163, 2)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 3), (13, 1), (163, 2)] : List FactorBlock).map factorBlockValue).prod) = 1381588001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_13
      · exact prime_oneHundredFiftyThreeEU_163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1381588001) ^ 690794000 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1381588001) ^ 276317600 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1381588001) ^ 106276000 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1381588001) ^ 8476000 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_1410034981 : Nat.Prime 1410034981 := by
  apply lucas_primality 1410034981 (2 : ZMod 1410034981)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (103, 1), (151, 1), (1511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (103, 1), (151, 1), (1511, 1)] : List FactorBlock).map factorBlockValue).prod) = 1410034981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_103
      · exact prime_oneHundredFiftyThreeEU_151
      · exact prime_oneHundredFiftyThreeEU_1511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1410034981) ^ 705017490 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1410034981) ^ 470011660 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1410034981) ^ 282006996 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1410034981) ^ 13689660 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1410034981) ^ 9337980 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1410034981) ^ 933180 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_1511628841 : Nat.Prime 1511628841 := by
  apply lucas_primality 1511628841 (11 : ZMod 1511628841)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (149, 1), (28181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (149, 1), (28181, 1)] : List FactorBlock).map factorBlockValue).prod) = 1511628841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_149
      · exact prime_oneHundredFiftyThreeEU_28181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1511628841) ^ 755814420 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 1511628841) ^ 503876280 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 1511628841) ^ 302325768 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 1511628841) ^ 10145160 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 1511628841) ^ 53640 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_1842596761 : Nat.Prime 1842596761 := by
  apply lucas_primality 1842596761 (7 : ZMod 1842596761)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (3079, 1), (4987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (3079, 1), (4987, 1)] : List FactorBlock).map factorBlockValue).prod) = 1842596761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_3079
      · exact prime_oneHundredFiftyThreeEU_4987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1842596761) ^ 921298380 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 1842596761) ^ 614198920 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 1842596761) ^ 368519352 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 1842596761) ^ 598440 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 1842596761) ^ 369480 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_2201703901 : Nat.Prime 2201703901 := by
  apply lucas_primality 2201703901 (7 : ZMod 2201703901)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (11, 2), (131, 1), (463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (11, 2), (131, 1), (463, 1)] : List FactorBlock).map factorBlockValue).prod) = 2201703901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_11
      · exact prime_oneHundredFiftyThreeEU_131
      · exact prime_oneHundredFiftyThreeEU_463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2201703901) ^ 1100851950 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 2201703901) ^ 733901300 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 2201703901) ^ 440340780 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 2201703901) ^ 200154900 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 2201703901) ^ 16806900 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 2201703901) ^ 4755300 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_2429747653 : Nat.Prime 2429747653 := by
  apply lucas_primality 2429747653 (14 : ZMod 2429747653)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (131, 1), (1545641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (131, 1), (1545641, 1)] : List FactorBlock).map factorBlockValue).prod) = 2429747653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_131
      · exact prime_oneHundredFiftyThreeEU_1545641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 2429747653) ^ 1214873826 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (14 : ZMod 2429747653) ^ 809915884 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (14 : ZMod 2429747653) ^ 18547692 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (14 : ZMod 2429747653) ^ 1572 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_2431500893 : Nat.Prime 2431500893 := by
  apply lucas_primality 2431500893 (2 : ZMod 2431500893)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7867, 1), (77269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7867, 1), (77269, 1)] : List FactorBlock).map factorBlockValue).prod) = 2431500893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_7867
      · exact prime_oneHundredFiftyThreeEU_77269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2431500893) ^ 1215750446 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2431500893) ^ 309076 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2431500893) ^ 31468 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_2609522327 : Nat.Prime 2609522327 := by
  apply lucas_primality 2609522327 (5 : ZMod 2609522327)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (229, 1), (138967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (229, 1), (138967, 1)] : List FactorBlock).map factorBlockValue).prod) = 2609522327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_41
      · exact prime_oneHundredFiftyThreeEU_229
      · exact prime_oneHundredFiftyThreeEU_138967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2609522327) ^ 1304761163 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2609522327) ^ 63646886 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2609522327) ^ 11395294 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2609522327) ^ 18778 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_2855540719 : Nat.Prime 2855540719 := by
  apply lucas_primality 2855540719 (3 : ZMod 2855540719)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1571, 1), (100981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1571, 1), (100981, 1)] : List FactorBlock).map factorBlockValue).prod) = 2855540719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_1571
      · exact prime_oneHundredFiftyThreeEU_100981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2855540719) ^ 1427770359 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2855540719) ^ 951846906 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2855540719) ^ 1817658 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2855540719) ^ 28278 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_3292064693 : Nat.Prime 3292064693 := by
  apply lucas_primality 3292064693 (2 : ZMod 3292064693)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (43, 1), (761, 1), (3593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (43, 1), (761, 1), (3593, 1)] : List FactorBlock).map factorBlockValue).prod) = 3292064693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_43
      · exact prime_oneHundredFiftyThreeEU_761
      · exact prime_oneHundredFiftyThreeEU_3593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3292064693) ^ 1646032346 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3292064693) ^ 470294956 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3292064693) ^ 76559644 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3292064693) ^ 4325972 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3292064693) ^ 916244 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_3660700717 : Nat.Prime 3660700717 := by
  apply lucas_primality 3660700717 (2 : ZMod 3660700717)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 5), (3766153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 5), (3766153, 1)] : List FactorBlock).map factorBlockValue).prod) = 3660700717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_3766153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3660700717) ^ 1830350358 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3660700717) ^ 1220233572 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3660700717) ^ 972 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_3866459153 : Nat.Prime 3866459153 := by
  apply lucas_primality 3866459153 (5 : ZMod 3866459153)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (37, 1), (6531181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (37, 1), (6531181, 1)] : List FactorBlock).map factorBlockValue).prod) = 3866459153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_37
      · exact prime_oneHundredFiftyThreeEU_6531181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3866459153) ^ 1933229576 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3866459153) ^ 104498896 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3866459153) ^ 592 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_3948289019 : Nat.Prime 3948289019 := by
  apply lucas_primality 3948289019 (2 : ZMod 3948289019)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (79, 1), (727, 1), (929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (79, 1), (727, 1), (929, 1)] : List FactorBlock).map factorBlockValue).prod) = 3948289019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_37
      · exact prime_oneHundredFiftyThreeEU_79
      · exact prime_oneHundredFiftyThreeEU_727
      · exact prime_oneHundredFiftyThreeEU_929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3948289019) ^ 1974144509 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3948289019) ^ 106710514 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3948289019) ^ 49978342 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3948289019) ^ 5430934 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3948289019) ^ 4250042 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_4041774067 : Nat.Prime 4041774067 := by
  apply lucas_primality 4041774067 (2 : ZMod 4041774067)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (61239001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (61239001, 1)] : List FactorBlock).map factorBlockValue).prod) = 4041774067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_11
      · exact prime_oneHundredFiftyThreeEU_61239001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4041774067) ^ 2020887033 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4041774067) ^ 1347258022 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4041774067) ^ 367434006 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4041774067) ^ 66 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_4167405481 : Nat.Prime 4167405481 := by
  apply lucas_primality 4167405481 (11 : ZMod 4167405481)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (271, 1), (18307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (271, 1), (18307, 1)] : List FactorBlock).map factorBlockValue).prod) = 4167405481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_271
      · exact prime_oneHundredFiftyThreeEU_18307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 4167405481) ^ 2083702740 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 4167405481) ^ 1389135160 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 4167405481) ^ 833481096 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 4167405481) ^ 595343640 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 4167405481) ^ 15377880 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 4167405481) ^ 227640 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_4575287663 : Nat.Prime 4575287663 := by
  apply lucas_primality 4575287663 (5 : ZMod 4575287663)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (41, 1), (47, 1), (107923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (41, 1), (47, 1), (107923, 1)] : List FactorBlock).map factorBlockValue).prod) = 4575287663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_11
      · exact prime_oneHundredFiftyThreeEU_41
      · exact prime_oneHundredFiftyThreeEU_47
      · exact prime_oneHundredFiftyThreeEU_107923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4575287663) ^ 2287643831 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 4575287663) ^ 415935242 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 4575287663) ^ 111592382 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 4575287663) ^ 97346546 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 4575287663) ^ 42394 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_4699903823 : Nat.Prime 4699903823 := by
  apply lucas_primality 4699903823 (5 : ZMod 4699903823)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (283, 1), (8303717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (283, 1), (8303717, 1)] : List FactorBlock).map factorBlockValue).prod) = 4699903823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_283
      · exact prime_oneHundredFiftyThreeEU_8303717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 4699903823) ^ 2349951911 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 4699903823) ^ 16607434 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 4699903823) ^ 566 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_5126804671 : Nat.Prime 5126804671 := by
  apply lucas_primality 5126804671 (7 : ZMod 5126804671)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (1823, 1), (7211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (1823, 1), (7211, 1)] : List FactorBlock).map factorBlockValue).prod) = 5126804671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_13
      · exact prime_oneHundredFiftyThreeEU_1823
      · exact prime_oneHundredFiftyThreeEU_7211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 5126804671) ^ 2563402335 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 5126804671) ^ 1708934890 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 5126804671) ^ 1025360934 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 5126804671) ^ 394369590 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 5126804671) ^ 2812290 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 5126804671) ^ 710970 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_31
      · exact prime_oneHundredFiftyThreeEU_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_7974779347 : Nat.Prime 7974779347 := by
  apply lucas_primality 7974779347 (2 : ZMod 7974779347)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (79, 1), (207709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (79, 1), (207709, 1)] : List FactorBlock).map factorBlockValue).prod) = 7974779347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_79
      · exact prime_oneHundredFiftyThreeEU_207709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7974779347) ^ 3987389673 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7974779347) ^ 2658259782 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7974779347) ^ 100946574 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7974779347) ^ 38394 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_8603960009 : Nat.Prime 8603960009 := by
  apply lucas_primality 8603960009 (11 : ZMod 8603960009)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (153642143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (153642143, 1)] : List FactorBlock).map factorBlockValue).prod) = 8603960009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_153642143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 8603960009) ^ 4301980004 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 8603960009) ^ 1229137144 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 8603960009) ^ 56 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_8923633783 : Nat.Prime 8923633783 := by
  apply lucas_primality 8923633783 (5 : ZMod 8923633783)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (433, 1), (541, 1), (907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (433, 1), (541, 1), (907, 1)] : List FactorBlock).map factorBlockValue).prod) = 8923633783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_433
      · exact prime_oneHundredFiftyThreeEU_541
      · exact prime_oneHundredFiftyThreeEU_907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 8923633783) ^ 4461816891 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 8923633783) ^ 2974544594 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 8923633783) ^ 1274804826 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 8923633783) ^ 20608854 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 8923633783) ^ 16494702 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 8923633783) ^ 9838626 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_9420813119 : Nat.Prime 9420813119 := by
  apply lucas_primality 9420813119 (7 : ZMod 9420813119)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (26783, 1), (175873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (26783, 1), (175873, 1)] : List FactorBlock).map factorBlockValue).prod) = 9420813119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_26783
      · exact prime_oneHundredFiftyThreeEU_175873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 9420813119) ^ 4710406559 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 9420813119) ^ 351746 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 9420813119) ^ 53566 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_10593489671 : Nat.Prime 10593489671 := by
  apply lucas_primality 10593489671 (7 : ZMod 10593489671)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1059348967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1059348967, 1)] : List FactorBlock).map factorBlockValue).prod) = 10593489671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_1059348967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 10593489671) ^ 5296744835 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 10593489671) ^ 2118697934 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 10593489671) ^ 10 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_11507896481 : Nat.Prime 11507896481 := by
  apply lucas_primality 11507896481 (3 : ZMod 11507896481)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (71924353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (71924353, 1)] : List FactorBlock).map factorBlockValue).prod) = 11507896481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_71924353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 11507896481) ^ 5753948240 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 11507896481) ^ 2301579296 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 11507896481) ^ 160 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_14190278693 : Nat.Prime 14190278693 := by
  apply lucas_primality 14190278693 (2 : ZMod 14190278693)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (271, 1), (770039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (271, 1), (770039, 1)] : List FactorBlock).map factorBlockValue).prod) = 14190278693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_17
      · exact prime_oneHundredFiftyThreeEU_271
      · exact prime_oneHundredFiftyThreeEU_770039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14190278693) ^ 7095139346 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 14190278693) ^ 834722276 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 14190278693) ^ 52362652 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 14190278693) ^ 18428 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_17370530621 : Nat.Prime 17370530621 := by
  apply lucas_primality 17370530621 (2 : ZMod 17370530621)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (868526531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (868526531, 1)] : List FactorBlock).map factorBlockValue).prod) = 17370530621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_868526531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 17370530621) ^ 8685265310 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 17370530621) ^ 3474106124 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 17370530621) ^ 20 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_18430972757 : Nat.Prime 18430972757 := by
  apply lucas_primality 18430972757 (2 : ZMod 18430972757)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (17, 1), (4597, 1), (8423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (17, 1), (4597, 1), (8423, 1)] : List FactorBlock).map factorBlockValue).prod) = 18430972757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_17
      · exact prime_oneHundredFiftyThreeEU_4597
      · exact prime_oneHundredFiftyThreeEU_8423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18430972757) ^ 9215486378 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 18430972757) ^ 2632996108 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 18430972757) ^ 1084174868 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 18430972757) ^ 4009348 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 18430972757) ^ 2188172 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_20118575063 : Nat.Prime 20118575063 := by
  apply lucas_primality 20118575063 (5 : ZMod 20118575063)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (107, 1), (1217, 1), (77249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (107, 1), (1217, 1), (77249, 1)] : List FactorBlock).map factorBlockValue).prod) = 20118575063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_107
      · exact prime_oneHundredFiftyThreeEU_1217
      · exact prime_oneHundredFiftyThreeEU_77249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 20118575063) ^ 10059287531 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 20118575063) ^ 188024066 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 20118575063) ^ 16531286 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 20118575063) ^ 260438 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_21201849661 : Nat.Prime 21201849661 := by
  apply lucas_primality 21201849661 (7 : ZMod 21201849661)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (373, 1), (947357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (373, 1), (947357, 1)] : List FactorBlock).map factorBlockValue).prod) = 21201849661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_373
      · exact prime_oneHundredFiftyThreeEU_947357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 21201849661) ^ 10600924830 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 21201849661) ^ 7067283220 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 21201849661) ^ 4240369932 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 21201849661) ^ 56841420 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 21201849661) ^ 22380 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_23046330287 : Nat.Prime 23046330287 := by
  apply lucas_primality 23046330287 (7 : ZMod 23046330287)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (173, 1), (1583, 1), (6011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (173, 1), (1583, 1), (6011, 1)] : List FactorBlock).map factorBlockValue).prod) = 23046330287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_173
      · exact prime_oneHundredFiftyThreeEU_1583
      · exact prime_oneHundredFiftyThreeEU_6011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 23046330287) ^ 11523165143 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 23046330287) ^ 3292332898 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 23046330287) ^ 133215782 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 23046330287) ^ 14558642 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 23046330287) ^ 3834026 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_24250644403 : Nat.Prime 24250644403 := by
  apply lucas_primality 24250644403 (2 : ZMod 24250644403)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4041774067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4041774067, 1)] : List FactorBlock).map factorBlockValue).prod) = 24250644403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_4041774067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 24250644403) ^ 12125322201 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 24250644403) ^ 8083548134 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 24250644403) ^ 6 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_25790344861 : Nat.Prime 25790344861 := by
  apply lucas_primality 25790344861 (2 : ZMod 25790344861)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (61405583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (61405583, 1)] : List FactorBlock).map factorBlockValue).prod) = 25790344861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_61405583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 25790344861) ^ 12895172430 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 25790344861) ^ 8596781620 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 25790344861) ^ 5158068972 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 25790344861) ^ 3684334980 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 25790344861) ^ 420 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_29816588057 : Nat.Prime 29816588057 := by
  apply lucas_primality 29816588057 (3 : ZMod 29816588057)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (40433, 1), (92179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (40433, 1), (92179, 1)] : List FactorBlock).map factorBlockValue).prod) = 29816588057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_40433
      · exact prime_oneHundredFiftyThreeEU_92179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 29816588057) ^ 14908294028 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 29816588057) ^ 737432 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 29816588057) ^ 323464 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_31789660873 : Nat.Prime 31789660873 := by
  apply lucas_primality 31789660873 (5 : ZMod 31789660873)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1831, 1), (723413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1831, 1), (723413, 1)] : List FactorBlock).map factorBlockValue).prod) = 31789660873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_1831
      · exact prime_oneHundredFiftyThreeEU_723413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 31789660873) ^ 15894830436 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 31789660873) ^ 10596553624 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 31789660873) ^ 17361912 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 31789660873) ^ 43944 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_34282794137 : Nat.Prime 34282794137 := by
  apply lucas_primality 34282794137 (3 : ZMod 34282794137)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (367, 1), (11676701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (367, 1), (11676701, 1)] : List FactorBlock).map factorBlockValue).prod) = 34282794137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_367
      · exact prime_oneHundredFiftyThreeEU_11676701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 34282794137) ^ 17141397068 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 34282794137) ^ 93413608 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 34282794137) ^ 2936 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_38125454137 : Nat.Prime 38125454137 := by
  apply lucas_primality 38125454137 (15 : ZMod 38125454137)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (11, 1), (2447, 1), (8431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (11, 1), (2447, 1), (8431, 1)] : List FactorBlock).map factorBlockValue).prod) = 38125454137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_11
      · exact prime_oneHundredFiftyThreeEU_2447
      · exact prime_oneHundredFiftyThreeEU_8431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 38125454137) ^ 19062727068 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (15 : ZMod 38125454137) ^ 12708484712 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (15 : ZMod 38125454137) ^ 5446493448 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (15 : ZMod 38125454137) ^ 3465950376 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (15 : ZMod 38125454137) ^ 15580488 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (15 : ZMod 38125454137) ^ 4522056 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_40237150127 : Nat.Prime 40237150127 := by
  apply lucas_primality 40237150127 (5 : ZMod 40237150127)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (20118575063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (20118575063, 1)] : List FactorBlock).map factorBlockValue).prod) = 40237150127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_20118575063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 40237150127) ^ 20118575063 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 40237150127) ^ 2 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_41812652839 : Nat.Prime 41812652839 := by
  apply lucas_primality 41812652839 (6 : ZMod 41812652839)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (17, 1), (37266179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (17, 1), (37266179, 1)] : List FactorBlock).map factorBlockValue).prod) = 41812652839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_11
      · exact prime_oneHundredFiftyThreeEU_17
      · exact prime_oneHundredFiftyThreeEU_37266179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 41812652839) ^ 20906326419 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 41812652839) ^ 13937550946 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 41812652839) ^ 3801150258 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 41812652839) ^ 2459567814 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 41812652839) ^ 1122 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_48437485823 : Nat.Prime 48437485823 := by
  apply lucas_primality 48437485823 (5 : ZMod 48437485823)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (2201703901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (2201703901, 1)] : List FactorBlock).map factorBlockValue).prod) = 48437485823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_11
      · exact prime_oneHundredFiftyThreeEU_2201703901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 48437485823) ^ 24218742911 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 48437485823) ^ 4403407802 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 48437485823) ^ 22 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_52081102133 : Nat.Prime 52081102133 := by
  apply lucas_primality 52081102133 (2 : ZMod 52081102133)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (139, 1), (163, 1), (12227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (139, 1), (163, 1), (12227, 1)] : List FactorBlock).map factorBlockValue).prod) = 52081102133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_47
      · exact prime_oneHundredFiftyThreeEU_139
      · exact prime_oneHundredFiftyThreeEU_163
      · exact prime_oneHundredFiftyThreeEU_12227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 52081102133) ^ 26040551066 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 52081102133) ^ 1108108556 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 52081102133) ^ 374684188 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 52081102133) ^ 319515964 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 52081102133) ^ 4259516 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_62887767799 : Nat.Prime 62887767799 := by
  apply lucas_primality 62887767799 (6 : ZMod 62887767799)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (127, 1), (82529879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (127, 1), (82529879, 1)] : List FactorBlock).map factorBlockValue).prod) = 62887767799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_127
      · exact prime_oneHundredFiftyThreeEU_82529879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 62887767799) ^ 31443883899 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 62887767799) ^ 20962589266 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 62887767799) ^ 495179274 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 62887767799) ^ 762 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_67582939393 : Nat.Prime 67582939393 := by
  apply lucas_primality 67582939393 (11 : ZMod 67582939393)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 2), (107, 1), (274139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 2), (107, 1), (274139, 1)] : List FactorBlock).map factorBlockValue).prod) = 67582939393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_107
      · exact prime_oneHundredFiftyThreeEU_274139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 67582939393) ^ 33791469696 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 67582939393) ^ 22527646464 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 67582939393) ^ 631616256 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 67582939393) ^ 246528 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_76953079939 : Nat.Prime 76953079939 := by
  apply lucas_primality 76953079939 (2 : ZMod 76953079939)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (19, 1), (419, 1), (230149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (19, 1), (419, 1), (230149, 1)] : List FactorBlock).map factorBlockValue).prod) = 76953079939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_19
      · exact prime_oneHundredFiftyThreeEU_419
      · exact prime_oneHundredFiftyThreeEU_230149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 76953079939) ^ 38476539969 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 76953079939) ^ 25651026646 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 76953079939) ^ 10993297134 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 76953079939) ^ 4050162102 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 76953079939) ^ 183658902 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 76953079939) ^ 334362 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_85733832857 : Nat.Prime 85733832857 := by
  apply lucas_primality 85733832857 (3 : ZMod 85733832857)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (29, 1), (1063, 1), (49663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (29, 1), (1063, 1), (49663, 1)] : List FactorBlock).map factorBlockValue).prod) = 85733832857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_29
      · exact prime_oneHundredFiftyThreeEU_1063
      · exact prime_oneHundredFiftyThreeEU_49663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 85733832857) ^ 42866916428 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 85733832857) ^ 12247690408 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 85733832857) ^ 2956339064 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 85733832857) ^ 80652712 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 85733832857) ^ 1726312 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_86702463293 : Nat.Prime 86702463293 := by
  apply lucas_primality 86702463293 (2 : ZMod 86702463293)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (293, 1), (73978211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (293, 1), (73978211, 1)] : List FactorBlock).map factorBlockValue).prod) = 86702463293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_293
      · exact prime_oneHundredFiftyThreeEU_73978211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 86702463293) ^ 43351231646 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 86702463293) ^ 295912844 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 86702463293) ^ 1172 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_112891744211 : Nat.Prime 112891744211 := by
  apply lucas_primality 112891744211 (2 : ZMod 112891744211)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (107, 1), (137, 1), (110017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (107, 1), (137, 1), (110017, 1)] : List FactorBlock).map factorBlockValue).prod) = 112891744211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_107
      · exact prime_oneHundredFiftyThreeEU_137
      · exact prime_oneHundredFiftyThreeEU_110017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 112891744211) ^ 56445872105 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 112891744211) ^ 22578348842 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 112891744211) ^ 16127392030 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 112891744211) ^ 1055063030 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 112891744211) ^ 824027330 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 112891744211) ^ 1026130 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_114221628761 : Nat.Prime 114221628761 := by
  apply lucas_primality 114221628761 (3 : ZMod 114221628761)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (2855540719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (2855540719, 1)] : List FactorBlock).map factorBlockValue).prod) = 114221628761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_2855540719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 114221628761) ^ 57110814380 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 114221628761) ^ 22844325752 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 114221628761) ^ 40 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_121175790187 : Nat.Prime 121175790187 := by
  apply lucas_primality 121175790187 (2 : ZMod 121175790187)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (17, 1), (107999813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (17, 1), (107999813, 1)] : List FactorBlock).map factorBlockValue).prod) = 121175790187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_11
      · exact prime_oneHundredFiftyThreeEU_17
      · exact prime_oneHundredFiftyThreeEU_107999813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 121175790187) ^ 60587895093 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 121175790187) ^ 40391930062 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 121175790187) ^ 11015980926 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 121175790187) ^ 7127987658 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 121175790187) ^ 1122 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_130321365301 : Nat.Prime 130321365301 := by
  apply lucas_primality 130321365301 (10 : ZMod 130321365301)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (7, 2), (59, 1), (50087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (7, 2), (59, 1), (50087, 1)] : List FactorBlock).map factorBlockValue).prod) = 130321365301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_59
      · exact prime_oneHundredFiftyThreeEU_50087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 130321365301) ^ 65160682650 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (10 : ZMod 130321365301) ^ 43440455100 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (10 : ZMod 130321365301) ^ 26064273060 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (10 : ZMod 130321365301) ^ 18617337900 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (10 : ZMod 130321365301) ^ 2208836700 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (10 : ZMod 130321365301) ^ 2601900 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_136917622189 : Nat.Prime 136917622189 := by
  apply lucas_primality 136917622189 (6 : ZMod 136917622189)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (1267755761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (1267755761, 1)] : List FactorBlock).map factorBlockValue).prod) = 136917622189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_1267755761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 136917622189) ^ 68458811094 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 136917622189) ^ 45639207396 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 136917622189) ^ 108 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_146914610617 : Nat.Prime 146914610617 := by
  apply lucas_primality 146914610617 (5 : ZMod 146914610617)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (1609, 1), (1268167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (1609, 1), (1268167, 1)] : List FactorBlock).map factorBlockValue).prod) = 146914610617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_1609
      · exact prime_oneHundredFiftyThreeEU_1268167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 146914610617) ^ 73457305308 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 146914610617) ^ 48971536872 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 146914610617) ^ 91308024 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 146914610617) ^ 115848 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_159135798509 : Nat.Prime 159135798509 := by
  apply lucas_primality 159135798509 (2 : ZMod 159135798509)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (53, 1), (4723, 1), (9349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (53, 1), (4723, 1), (9349, 1)] : List FactorBlock).map factorBlockValue).prod) = 159135798509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_17
      · exact prime_oneHundredFiftyThreeEU_53
      · exact prime_oneHundredFiftyThreeEU_4723
      · exact prime_oneHundredFiftyThreeEU_9349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 159135798509) ^ 79567899254 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 159135798509) ^ 9360929324 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 159135798509) ^ 3002562236 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 159135798509) ^ 33693796 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 159135798509) ^ 17021692 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_184564968157 : Nat.Prime 184564968157 := by
  apply lucas_primality 184564968157 (2 : ZMod 184564968157)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5126804671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5126804671, 1)] : List FactorBlock).map factorBlockValue).prod) = 184564968157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5126804671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 184564968157) ^ 92282484078 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 184564968157) ^ 61521656052 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 184564968157) ^ 36 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_194739564727 : Nat.Prime 194739564727 := by
  apply lucas_primality 194739564727 (5 : ZMod 194739564727)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (167, 1), (2203, 1), (4201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (167, 1), (2203, 1), (4201, 1)] : List FactorBlock).map factorBlockValue).prod) = 194739564727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_167
      · exact prime_oneHundredFiftyThreeEU_2203
      · exact prime_oneHundredFiftyThreeEU_4201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 194739564727) ^ 97369782363 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 194739564727) ^ 64913188242 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 194739564727) ^ 27819937818 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 194739564727) ^ 1166105178 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 194739564727) ^ 88397442 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 194739564727) ^ 46355526 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_195066570779 : Nat.Prime 195066570779 := by
  apply lucas_primality 195066570779 (2 : ZMod 195066570779)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (241, 1), (6343, 1), (63803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (241, 1), (6343, 1), (63803, 1)] : List FactorBlock).map factorBlockValue).prod) = 195066570779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_241
      · exact prime_oneHundredFiftyThreeEU_6343
      · exact prime_oneHundredFiftyThreeEU_63803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 195066570779) ^ 97533285389 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 195066570779) ^ 809404858 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 195066570779) ^ 30753046 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 195066570779) ^ 3057326 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_211843929377 : Nat.Prime 211843929377 := by
  apply lucas_primality 211843929377 (3 : ZMod 211843929377)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (9677, 1), (684109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (9677, 1), (684109, 1)] : List FactorBlock).map factorBlockValue).prod) = 211843929377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_9677
      · exact prime_oneHundredFiftyThreeEU_684109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 211843929377) ^ 105921964688 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 211843929377) ^ 21891488 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 211843929377) ^ 309664 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_233717500609 : Nat.Prime 233717500609 := by
  apply lucas_primality 233717500609 (7 : ZMod 233717500609)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (331, 1), (3677579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (331, 1), (3677579, 1)] : List FactorBlock).map factorBlockValue).prod) = 233717500609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_331
      · exact prime_oneHundredFiftyThreeEU_3677579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 233717500609) ^ 116858750304 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 233717500609) ^ 77905833536 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 233717500609) ^ 706095168 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 233717500609) ^ 63552 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_243364641461 : Nat.Prime 243364641461 := by
  apply lucas_primality 243364641461 (2 : ZMod 243364641461)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) = 243364641461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_19
      · exact prime_oneHundredFiftyThreeEU_640433267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 243364641461) ^ 121682320730 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 48672928292 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 12808665340 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 380 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_252836652197 : Nat.Prime 252836652197 := by
  apply lucas_primality 252836652197 (2 : ZMod 252836652197)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (263, 1), (240339023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (263, 1), (240339023, 1)] : List FactorBlock).map factorBlockValue).prod) = 252836652197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_263
      · exact prime_oneHundredFiftyThreeEU_240339023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 252836652197) ^ 126418326098 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 252836652197) ^ 961356092 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 252836652197) ^ 1052 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_253295570287 : Nat.Prime 253295570287 := by
  apply lucas_primality 253295570287 (3 : ZMod 253295570287)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (11, 1), (23, 1), (563, 1), (3659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (11, 1), (23, 1), (563, 1), (3659, 1)] : List FactorBlock).map factorBlockValue).prod) = 253295570287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_11
      · exact prime_oneHundredFiftyThreeEU_23
      · exact prime_oneHundredFiftyThreeEU_563
      · exact prime_oneHundredFiftyThreeEU_3659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 253295570287) ^ 126647785143 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 253295570287) ^ 84431856762 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 253295570287) ^ 23026870026 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 253295570287) ^ 11012850882 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 253295570287) ^ 449903322 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 253295570287) ^ 69225354 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_263713587191 : Nat.Prime 263713587191 := by
  apply lucas_primality 263713587191 (13 : ZMod 263713587191)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (12923, 1), (2040653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (12923, 1), (2040653, 1)] : List FactorBlock).map factorBlockValue).prod) = 263713587191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_12923
      · exact prime_oneHundredFiftyThreeEU_2040653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 263713587191) ^ 131856793595 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (13 : ZMod 263713587191) ^ 52742717438 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (13 : ZMod 263713587191) ^ 20406530 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (13 : ZMod 263713587191) ^ 129230 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_282379165919 : Nat.Prime 282379165919 := by
  apply lucas_primality 282379165919 (7 : ZMod 282379165919)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2683, 1), (52623773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2683, 1), (52623773, 1)] : List FactorBlock).map factorBlockValue).prod) = 282379165919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_2683
      · exact prime_oneHundredFiftyThreeEU_52623773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 282379165919) ^ 141189582959 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 282379165919) ^ 105247546 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 282379165919) ^ 5366 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_307812319757 : Nat.Prime 307812319757 := by
  apply lucas_primality 307812319757 (2 : ZMod 307812319757)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (76953079939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (76953079939, 1)] : List FactorBlock).map factorBlockValue).prod) = 307812319757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_76953079939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 307812319757) ^ 153906159878 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 307812319757) ^ 4 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_352853743199 : Nat.Prime 352853743199 := by
  apply lucas_primality 352853743199 (11 : ZMod 352853743199)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 2), (19, 1), (37, 1), (179, 1), (11587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 2), (19, 1), (37, 1), (179, 1), (11587, 1)] : List FactorBlock).map factorBlockValue).prod) = 352853743199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_11
      · exact prime_oneHundredFiftyThreeEU_19
      · exact prime_oneHundredFiftyThreeEU_37
      · exact prime_oneHundredFiftyThreeEU_179
      · exact prime_oneHundredFiftyThreeEU_11587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 352853743199) ^ 176426871599 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 352853743199) ^ 32077613018 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 352853743199) ^ 18571249642 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 352853743199) ^ 9536587654 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 352853743199) ^ 1971249962 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 352853743199) ^ 30452554 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_498749984489 : Nat.Prime 498749984489 := by
  apply lucas_primality 498749984489 (6 : ZMod 498749984489)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (41, 1), (2543, 1), (12203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (41, 1), (2543, 1), (12203, 1)] : List FactorBlock).map factorBlockValue).prod) = 498749984489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_41
      · exact prime_oneHundredFiftyThreeEU_2543
      · exact prime_oneHundredFiftyThreeEU_12203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 498749984489) ^ 249374992244 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 498749984489) ^ 71249997784 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 498749984489) ^ 12164633768 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 498749984489) ^ 196126616 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 498749984489) ^ 40871096 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_510047838721 : Nat.Prime 510047838721 := by
  apply lucas_primality 510047838721 (13 : ZMod 510047838721)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 2), (5, 1), (7, 1), (3162499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 2), (5, 1), (7, 1), (3162499, 1)] : List FactorBlock).map factorBlockValue).prod) = 510047838721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_3162499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 510047838721) ^ 255023919360 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (13 : ZMod 510047838721) ^ 170015946240 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (13 : ZMod 510047838721) ^ 102009567744 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (13 : ZMod 510047838721) ^ 72863976960 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (13 : ZMod 510047838721) ^ 161280 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_513077386951 : Nat.Prime 513077386951 := by
  apply lucas_primality 513077386951 (3 : ZMod 513077386951)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (31, 1), (733, 1), (50177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (31, 1), (733, 1), (50177, 1)] : List FactorBlock).map factorBlockValue).prod) = 513077386951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_31
      · exact prime_oneHundredFiftyThreeEU_733
      · exact prime_oneHundredFiftyThreeEU_50177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 513077386951) ^ 256538693475 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 513077386951) ^ 171025795650 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 513077386951) ^ 102615477390 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 513077386951) ^ 16550883450 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 513077386951) ^ 699969150 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 513077386951) ^ 10225350 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_997499968979 : Nat.Prime 997499968979 := by
  apply lucas_primality 997499968979 (2 : ZMod 997499968979)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (498749984489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (498749984489, 1)] : List FactorBlock).map factorBlockValue).prod) = 997499968979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_498749984489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 997499968979) ^ 498749984489 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 997499968979) ^ 2 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_1046860168127 : Nat.Prime 1046860168127 := by
  apply lucas_primality 1046860168127 (5 : ZMod 1046860168127)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (160583, 1), (3259561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (160583, 1), (3259561, 1)] : List FactorBlock).map factorBlockValue).prod) = 1046860168127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_160583
      · exact prime_oneHundredFiftyThreeEU_3259561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1046860168127) ^ 523430084063 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1046860168127) ^ 6519122 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1046860168127) ^ 321166 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_1197990901567 : Nat.Prime 1197990901567 := by
  apply lucas_primality 1197990901567 (5 : ZMod 1197990901567)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (43801, 1), (79973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (43801, 1), (79973, 1)] : List FactorBlock).map factorBlockValue).prod) = 1197990901567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_19
      · exact prime_oneHundredFiftyThreeEU_43801
      · exact prime_oneHundredFiftyThreeEU_79973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1197990901567) ^ 598995450783 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1197990901567) ^ 399330300522 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1197990901567) ^ 63052152714 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1197990901567) ^ 27350766 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1197990901567) ^ 14979942 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_1760857498373 : Nat.Prime 1760857498373 := by
  apply lucas_primality 1760857498373 (2 : ZMod 1760857498373)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (62887767799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (62887767799, 1)] : List FactorBlock).map factorBlockValue).prod) = 1760857498373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_62887767799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1760857498373) ^ 880428749186 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1760857498373) ^ 251551071196 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1760857498373) ^ 28 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_1844200269517 : Nat.Prime 1844200269517 := by
  apply lucas_primality 1844200269517 (2 : ZMod 1844200269517)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (241, 1), (57971843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (241, 1), (57971843, 1)] : List FactorBlock).map factorBlockValue).prod) = 1844200269517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_11
      · exact prime_oneHundredFiftyThreeEU_241
      · exact prime_oneHundredFiftyThreeEU_57971843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1844200269517) ^ 922100134758 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1844200269517) ^ 614733423172 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1844200269517) ^ 167654569956 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1844200269517) ^ 7652283276 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1844200269517) ^ 31812 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_1985492195413 : Nat.Prime 1985492195413 := by
  apply lucas_primality 1985492195413 (2 : ZMod 1985492195413)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (47, 1), (2083, 1), (153641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (47, 1), (2083, 1), (153641, 1)] : List FactorBlock).map factorBlockValue).prod) = 1985492195413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_11
      · exact prime_oneHundredFiftyThreeEU_47
      · exact prime_oneHundredFiftyThreeEU_2083
      · exact prime_oneHundredFiftyThreeEU_153641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1985492195413) ^ 992746097706 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1985492195413) ^ 661830731804 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1985492195413) ^ 180499290492 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1985492195413) ^ 42244514796 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1985492195413) ^ 953188764 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1985492195413) ^ 12922932 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_2173293146033 : Nat.Prime 2173293146033 := by
  apply lucas_primality 2173293146033 (3 : ZMod 2173293146033)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (17, 2), (470002843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (17, 2), (470002843, 1)] : List FactorBlock).map factorBlockValue).prod) = 2173293146033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_17
      · exact prime_oneHundredFiftyThreeEU_470002843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2173293146033) ^ 1086646573016 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2173293146033) ^ 127840773296 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2173293146033) ^ 4624 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_2345784575419 : Nat.Prime 2345784575419 := by
  apply lucas_primality 2345784575419 (2 : ZMod 2345784575419)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (130321365301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (130321365301, 1)] : List FactorBlock).map factorBlockValue).prod) = 2345784575419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_130321365301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2345784575419) ^ 1172892287709 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2345784575419) ^ 781928191806 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2345784575419) ^ 18 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_2887024441709 : Nat.Prime 2887024441709 := by
  apply lucas_primality 2887024441709 (2 : ZMod 2887024441709)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (95723, 1), (685459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (95723, 1), (685459, 1)] : List FactorBlock).map factorBlockValue).prod) = 2887024441709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_11
      · exact prime_oneHundredFiftyThreeEU_95723
      · exact prime_oneHundredFiftyThreeEU_685459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2887024441709) ^ 1443512220854 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2887024441709) ^ 262456767428 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2887024441709) ^ 30160196 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2887024441709) ^ 4211812 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_3162399473593 : Nat.Prime 3162399473593 := by
  apply lucas_primality 3162399473593 (5 : ZMod 3162399473593)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (317, 1), (487, 1), (284509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (317, 1), (487, 1), (284509, 1)] : List FactorBlock).map factorBlockValue).prod) = 3162399473593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_317
      · exact prime_oneHundredFiftyThreeEU_487
      · exact prime_oneHundredFiftyThreeEU_284509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3162399473593) ^ 1581199736796 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3162399473593) ^ 1054133157864 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3162399473593) ^ 9976023576 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3162399473593) ^ 6493633416 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3162399473593) ^ 11115288 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_3459286272181 : Nat.Prime 3459286272181 := by
  apply lucas_primality 3459286272181 (6 : ZMod 3459286272181)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (2087, 1), (27625669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (2087, 1), (27625669, 1)] : List FactorBlock).map factorBlockValue).prod) = 3459286272181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_2087
      · exact prime_oneHundredFiftyThreeEU_27625669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3459286272181) ^ 1729643136090 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 3459286272181) ^ 1153095424060 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 3459286272181) ^ 691857254436 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 3459286272181) ^ 1657540140 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 3459286272181) ^ 125220 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_3562528142617 : Nat.Prime 3562528142617 := by
  apply lucas_primality 3562528142617 (5 : ZMod 3562528142617)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (167, 2), (787, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (167, 2), (787, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) = 3562528142617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_167
      · exact prime_oneHundredFiftyThreeEU_787
      · exact prime_oneHundredFiftyThreeEU_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3562528142617) ^ 1781264071308 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3562528142617) ^ 1187509380872 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3562528142617) ^ 21332503848 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3562528142617) ^ 4526719368 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3562528142617) ^ 526767432 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_3662228970263 : Nat.Prime 3662228970263 := by
  apply lucas_primality 3662228970263 (5 : ZMod 3662228970263)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (25790344861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (25790344861, 1)] : List FactorBlock).map factorBlockValue).prod) = 3662228970263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_71
      · exact prime_oneHundredFiftyThreeEU_25790344861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3662228970263) ^ 1831114485131 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3662228970263) ^ 51580689722 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3662228970263) ^ 142 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_3687111941479 : Nat.Prime 3687111941479 := by
  apply lucas_primality 3687111941479 (3 : ZMod 3687111941479)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (17, 1), (37, 1), (139568171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (17, 1), (37, 1), (139568171, 1)] : List FactorBlock).map factorBlockValue).prod) = 3687111941479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_17
      · exact prime_oneHundredFiftyThreeEU_37
      · exact prime_oneHundredFiftyThreeEU_139568171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3687111941479) ^ 1843555970739 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687111941479) ^ 1229037313826 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687111941479) ^ 526730277354 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687111941479) ^ 216888937734 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687111941479) ^ 99651674094 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687111941479) ^ 26418 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_4041154484167 : Nat.Prime 4041154484167 := by
  apply lucas_primality 4041154484167 (3 : ZMod 4041154484167)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (277, 1), (2431500893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (277, 1), (2431500893, 1)] : List FactorBlock).map factorBlockValue).prod) = 4041154484167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_277
      · exact prime_oneHundredFiftyThreeEU_2431500893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4041154484167) ^ 2020577242083 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 4041154484167) ^ 1347051494722 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 4041154484167) ^ 14589005358 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 4041154484167) ^ 1662 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_4052729124593 : Nat.Prime 4052729124593 := by
  apply lucas_primality 4052729124593 (3 : ZMod 4052729124593)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (253295570287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (253295570287, 1)] : List FactorBlock).map factorBlockValue).prod) = 4052729124593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_253295570287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 4052729124593) ^ 2026364562296 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 4052729124593) ^ 16 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_4303766710267 : Nat.Prime 4303766710267 := by
  apply lucas_primality 4303766710267 (3 : ZMod 4303766710267)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (21013, 1), (34135747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (21013, 1), (34135747, 1)] : List FactorBlock).map factorBlockValue).prod) = 4303766710267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_21013
      · exact prime_oneHundredFiftyThreeEU_34135747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4303766710267) ^ 2151883355133 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 4303766710267) ^ 1434588903422 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 4303766710267) ^ 204814482 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 4303766710267) ^ 126078 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_4310529111817 : Nat.Prime 4310529111817 := by
  apply lucas_primality 4310529111817 (5 : ZMod 4310529111817)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1217, 1), (147580427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1217, 1), (147580427, 1)] : List FactorBlock).map factorBlockValue).prod) = 4310529111817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_1217
      · exact prime_oneHundredFiftyThreeEU_147580427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4310529111817) ^ 2155264555908 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 4310529111817) ^ 1436843037272 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 4310529111817) ^ 3541930248 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 4310529111817) ^ 29208 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_4667461964617 : Nat.Prime 4667461964617 := by
  apply lucas_primality 4667461964617 (5 : ZMod 4667461964617)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (59, 1), (197, 1), (1521103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (59, 1), (197, 1), (1521103, 1)] : List FactorBlock).map factorBlockValue).prod) = 4667461964617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_11
      · exact prime_oneHundredFiftyThreeEU_59
      · exact prime_oneHundredFiftyThreeEU_197
      · exact prime_oneHundredFiftyThreeEU_1521103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4667461964617) ^ 2333730982308 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 4667461964617) ^ 1555820654872 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 4667461964617) ^ 424314724056 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 4667461964617) ^ 79109524824 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 4667461964617) ^ 23692700328 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 4667461964617) ^ 3068472 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_4948309299701 : Nat.Prime 4948309299701 := by
  apply lucas_primality 4948309299701 (7 : ZMod 4948309299701)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (13, 1), (73, 1), (52142353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (13, 1), (73, 1), (52142353, 1)] : List FactorBlock).map factorBlockValue).prod) = 4948309299701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_13
      · exact prime_oneHundredFiftyThreeEU_73
      · exact prime_oneHundredFiftyThreeEU_52142353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4948309299701) ^ 2474154649850 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 4948309299701) ^ 989661859940 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 4948309299701) ^ 380639176900 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 4948309299701) ^ 67785058900 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 4948309299701) ^ 94900 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_5582877536501 : Nat.Prime 5582877536501 := by
  apply lucas_primality 5582877536501 (2 : ZMod 5582877536501)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 3), (11, 1), (29, 1), (35002367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 3), (11, 1), (29, 1), (35002367, 1)] : List FactorBlock).map factorBlockValue).prod) = 5582877536501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_11
      · exact prime_oneHundredFiftyThreeEU_29
      · exact prime_oneHundredFiftyThreeEU_35002367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5582877536501) ^ 2791438768250 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 5582877536501) ^ 1116575507300 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 5582877536501) ^ 507534321500 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 5582877536501) ^ 192513018500 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 5582877536501) ^ 159500 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_5988063355277 : Nat.Prime 5988063355277 := by
  apply lucas_primality 5988063355277 (2 : ZMod 5988063355277)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (139, 1), (6029, 1), (41543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (139, 1), (6029, 1), (41543, 1)] : List FactorBlock).map factorBlockValue).prod) = 5988063355277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_43
      · exact prime_oneHundredFiftyThreeEU_139
      · exact prime_oneHundredFiftyThreeEU_6029
      · exact prime_oneHundredFiftyThreeEU_41543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5988063355277) ^ 2994031677638 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 5988063355277) ^ 139257287332 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 5988063355277) ^ 43079592484 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 5988063355277) ^ 993210044 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 5988063355277) ^ 144141332 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_6276995419813 : Nat.Prime 6276995419813 := by
  apply lucas_primality 6276995419813 (2 : ZMod 6276995419813)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (40237150127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (40237150127, 1)] : List FactorBlock).map factorBlockValue).prod) = 6276995419813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_13
      · exact prime_oneHundredFiftyThreeEU_40237150127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6276995419813) ^ 3138497709906 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 6276995419813) ^ 2092331806604 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 6276995419813) ^ 482845801524 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 6276995419813) ^ 156 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_6874705481557 : Nat.Prime 6874705481557 := by
  apply lucas_primality 6874705481557 (5 : ZMod 6874705481557)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (52081102133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (52081102133, 1)] : List FactorBlock).map factorBlockValue).prod) = 6874705481557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_11
      · exact prime_oneHundredFiftyThreeEU_52081102133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6874705481557) ^ 3437352740778 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 6874705481557) ^ 2291568493852 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 6874705481557) ^ 624973225596 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 6874705481557) ^ 132 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_6880433178221 : Nat.Prime 6880433178221 := by
  apply lucas_primality 6880433178221 (2 : ZMod 6880433178221)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (179, 1), (4177, 1), (65731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (179, 1), (4177, 1), (65731, 1)] : List FactorBlock).map factorBlockValue).prod) = 6880433178221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_179
      · exact prime_oneHundredFiftyThreeEU_4177
      · exact prime_oneHundredFiftyThreeEU_65731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6880433178221) ^ 3440216589110 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 6880433178221) ^ 1376086635644 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 6880433178221) ^ 982919025460 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 6880433178221) ^ 38438174180 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 6880433178221) ^ 1647218860 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 6880433178221) ^ 104675620 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_10123592834743 : Nat.Prime 10123592834743 := by
  apply lucas_primality 10123592834743 (5 : ZMod 10123592834743)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (359, 1), (4699903823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (359, 1), (4699903823, 1)] : List FactorBlock).map factorBlockValue).prod) = 10123592834743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_359
      · exact prime_oneHundredFiftyThreeEU_4699903823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 10123592834743) ^ 5061796417371 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 10123592834743) ^ 3374530944914 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 10123592834743) ^ 28199422938 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 10123592834743) ^ 2154 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_11165755073003 : Nat.Prime 11165755073003 := by
  apply lucas_primality 11165755073003 (2 : ZMod 11165755073003)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5582877536501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5582877536501, 1)] : List FactorBlock).map factorBlockValue).prod) = 11165755073003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_5582877536501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 11165755073003) ^ 5582877536501 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 11165755073003) ^ 2 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_14305552217941 : Nat.Prime 14305552217941 := by
  apply lucas_primality 14305552217941 (2 : ZMod 14305552217941)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (6427, 1), (37097537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (6427, 1), (37097537, 1)] : List FactorBlock).map factorBlockValue).prod) = 14305552217941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_6427
      · exact prime_oneHundredFiftyThreeEU_37097537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14305552217941) ^ 7152776108970 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 14305552217941) ^ 4768517405980 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 14305552217941) ^ 2861110443588 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 14305552217941) ^ 2225852220 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 14305552217941) ^ 385620 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_16922629075381 : Nat.Prime 16922629075381 := by
  apply lucas_primality 16922629075381 (2 : ZMod 16922629075381)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (17, 1), (157, 1), (15096281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (17, 1), (157, 1), (15096281, 1)] : List FactorBlock).map factorBlockValue).prod) = 16922629075381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_17
      · exact prime_oneHundredFiftyThreeEU_157
      · exact prime_oneHundredFiftyThreeEU_15096281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16922629075381) ^ 8461314537690 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 16922629075381) ^ 5640876358460 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 16922629075381) ^ 3384525815076 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 16922629075381) ^ 2417518439340 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 16922629075381) ^ 995448769140 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 16922629075381) ^ 107787446340 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 16922629075381) ^ 1120980 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_21076922361559 : Nat.Prime 21076922361559 := by
  apply lucas_primality 21076922361559 (6 : ZMod 21076922361559)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (293, 1), (4733, 1), (361871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (293, 1), (4733, 1), (361871, 1)] : List FactorBlock).map factorBlockValue).prod) = 21076922361559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_293
      · exact prime_oneHundredFiftyThreeEU_4733
      · exact prime_oneHundredFiftyThreeEU_361871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 21076922361559) ^ 10538461180779 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 21076922361559) ^ 7025640787186 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 21076922361559) ^ 3010988908794 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 21076922361559) ^ 71934888606 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 21076922361559) ^ 4453184526 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 21076922361559) ^ 58244298 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_25959084996967 : Nat.Prime 25959084996967 := by
  apply lucas_primality 25959084996967 (11 : ZMod 25959084996967)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (59, 1), (3947, 1), (1688987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (59, 1), (3947, 1), (1688987, 1)] : List FactorBlock).map factorBlockValue).prod) = 25959084996967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_11
      · exact prime_oneHundredFiftyThreeEU_59
      · exact prime_oneHundredFiftyThreeEU_3947
      · exact prime_oneHundredFiftyThreeEU_1688987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 25959084996967) ^ 12979542498483 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 25959084996967) ^ 8653028332322 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 25959084996967) ^ 2359916817906 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 25959084996967) ^ 439984491474 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 25959084996967) ^ 6576915378 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 25959084996967) ^ 15369618 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_33902056613179 : Nat.Prime 33902056613179 := by
  apply lucas_primality 33902056613179 (2 : ZMod 33902056613179)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (13, 1), (219533, 1), (219983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (13, 1), (219533, 1), (219983, 1)] : List FactorBlock).map factorBlockValue).prod) = 33902056613179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_13
      · exact prime_oneHundredFiftyThreeEU_219533
      · exact prime_oneHundredFiftyThreeEU_219983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 33902056613179) ^ 16951028306589 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 33902056613179) ^ 11300685537726 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 33902056613179) ^ 2607850508706 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 33902056613179) ^ 154428066 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 33902056613179) ^ 154112166 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_40604292994541 : Nat.Prime 40604292994541 := by
  apply lucas_primality 40604292994541 (10 : ZMod 40604292994541)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (184564968157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (184564968157, 1)] : List FactorBlock).map factorBlockValue).prod) = 40604292994541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_11
      · exact prime_oneHundredFiftyThreeEU_184564968157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 40604292994541) ^ 20302146497270 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (10 : ZMod 40604292994541) ^ 8120858598908 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (10 : ZMod 40604292994541) ^ 3691299363140 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (10 : ZMod 40604292994541) ^ 220 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_45752552594669 : Nat.Prime 45752552594669 := by
  apply lucas_primality 45752552594669 (2 : ZMod 45752552594669)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) = 45752552594669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_47
      · exact prime_oneHundredFiftyThreeEU_243364641461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 45752552594669) ^ 22876276297334 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 973458565844 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 188 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_76961608042651 : Nat.Prime 76961608042651 := by
  apply lucas_primality 76961608042651 (2 : ZMod 76961608042651)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (513077386951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (513077386951, 1)] : List FactorBlock).map factorBlockValue).prod) = 76961608042651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_513077386951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 76961608042651) ^ 38480804021325 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 76961608042651) ^ 25653869347550 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 76961608042651) ^ 15392321608530 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 76961608042651) ^ 150 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_88044049761617 : Nat.Prime 88044049761617 := by
  apply lucas_primality 88044049761617 (3 : ZMod 88044049761617)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (71, 1), (577, 1), (10332431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (71, 1), (577, 1), (10332431, 1)] : List FactorBlock).map factorBlockValue).prod) = 88044049761617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_13
      · exact prime_oneHundredFiftyThreeEU_71
      · exact prime_oneHundredFiftyThreeEU_577
      · exact prime_oneHundredFiftyThreeEU_10332431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 88044049761617) ^ 44022024880808 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 88044049761617) ^ 6772619212432 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 88044049761617) ^ 1240057038896 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 88044049761617) ^ 152589341008 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 88044049761617) ^ 8521136 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_113993486613649 : Nat.Prime 113993486613649 := by
  apply lucas_primality 113993486613649 (7 : ZMod 113993486613649)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (19, 1), (317, 1), (131433079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (19, 1), (317, 1), (131433079, 1)] : List FactorBlock).map factorBlockValue).prod) = 113993486613649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_19
      · exact prime_oneHundredFiftyThreeEU_317
      · exact prime_oneHundredFiftyThreeEU_131433079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 113993486613649) ^ 56996743306824 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 113993486613649) ^ 37997828871216 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 113993486613649) ^ 5999657190192 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 113993486613649) ^ 359600904144 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 113993486613649) ^ 867312 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_167380778992597 : Nat.Prime 167380778992597 := by
  apply lucas_primality 167380778992597 (2 : ZMod 167380778992597)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (1481, 1), (724479211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (1481, 1), (724479211, 1)] : List FactorBlock).map factorBlockValue).prod) = 167380778992597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_13
      · exact prime_oneHundredFiftyThreeEU_1481
      · exact prime_oneHundredFiftyThreeEU_724479211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 167380778992597) ^ 83690389496298 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 167380778992597) ^ 55793592997532 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 167380778992597) ^ 12875444537892 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 167380778992597) ^ 113018756916 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 167380778992597) ^ 231036 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_178320081482093 : Nat.Prime 178320081482093 := by
  apply lucas_primality 178320081482093 (2 : ZMod 178320081482093)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (4052729124593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (4052729124593, 1)] : List FactorBlock).map factorBlockValue).prod) = 178320081482093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_11
      · exact prime_oneHundredFiftyThreeEU_4052729124593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 178320081482093) ^ 89160040741046 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 178320081482093) ^ 16210916498372 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 178320081482093) ^ 44 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_182548096187377 : Nat.Prime 182548096187377 := by
  apply lucas_primality 182548096187377 (5 : ZMod 182548096187377)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (41, 1), (100699, 1), (921143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (41, 1), (100699, 1), (921143, 1)] : List FactorBlock).map factorBlockValue).prod) = 182548096187377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_41
      · exact prime_oneHundredFiftyThreeEU_100699
      · exact prime_oneHundredFiftyThreeEU_921143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 182548096187377) ^ 91274048093688 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 182548096187377) ^ 60849365395792 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 182548096187377) ^ 4452392589936 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 182548096187377) ^ 1812809424 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 182548096187377) ^ 198175632 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_252193983968743 : Nat.Prime 252193983968743 := by
  apply lucas_primality 252193983968743 (6 : ZMod 252193983968743)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (53, 1), (251, 1), (509, 1), (6207491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (53, 1), (251, 1), (509, 1), (6207491, 1)] : List FactorBlock).map factorBlockValue).prod) = 252193983968743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_53
      · exact prime_oneHundredFiftyThreeEU_251
      · exact prime_oneHundredFiftyThreeEU_509
      · exact prime_oneHundredFiftyThreeEU_6207491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 252193983968743) ^ 126096991984371 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 252193983968743) ^ 84064661322914 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 252193983968743) ^ 4758377056014 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 252193983968743) ^ 1004756908242 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 252193983968743) ^ 495469516638 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 252193983968743) ^ 40627362 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_293504456834027 : Nat.Prime 293504456834027 := by
  apply lucas_primality 293504456834027 (2 : ZMod 293504456834027)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (9049, 1), (108217, 1), (149861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (9049, 1), (108217, 1), (149861, 1)] : List FactorBlock).map factorBlockValue).prod) = 293504456834027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_9049
      · exact prime_oneHundredFiftyThreeEU_108217
      · exact prime_oneHundredFiftyThreeEU_149861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 293504456834027) ^ 146752228417013 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 293504456834027) ^ 32435015674 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 293504456834027) ^ 2712184378 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 293504456834027) ^ 1958511266 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_366020420757353 : Nat.Prime 366020420757353 := by
  apply lucas_primality 366020420757353 (3 : ZMod 366020420757353)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) = 366020420757353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_45752552594669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 366020420757353) ^ 183010210378676 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 366020420757353) ^ 8 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_528613798600369 : Nat.Prime 528613798600369 := by
  apply lucas_primality 528613798600369 (7 : ZMod 528613798600369)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (13, 1), (282379165919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (13, 1), (282379165919, 1)] : List FactorBlock).map factorBlockValue).prod) = 528613798600369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_13
      · exact prime_oneHundredFiftyThreeEU_282379165919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 528613798600369) ^ 264306899300184 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 528613798600369) ^ 176204599533456 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 528613798600369) ^ 40662599892336 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 528613798600369) ^ 1872 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_562988298100561 : Nat.Prime 562988298100561 := by
  apply lucas_primality 562988298100561 (13 : ZMod 562988298100561)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (2345784575419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (2345784575419, 1)] : List FactorBlock).map factorBlockValue).prod) = 562988298100561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_2345784575419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 562988298100561) ^ 281494149050280 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (13 : ZMod 562988298100561) ^ 187662766033520 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (13 : ZMod 562988298100561) ^ 112597659620112 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (13 : ZMod 562988298100561) ^ 240 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_586759241213917 : Nat.Prime 586759241213917 := by
  apply lucas_primality 586759241213917 (5 : ZMod 586759241213917)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (227, 1), (599, 1), (6469, 1), (55589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (227, 1), (599, 1), (6469, 1), (55589, 1)] : List FactorBlock).map factorBlockValue).prod) = 586759241213917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_227
      · exact prime_oneHundredFiftyThreeEU_599
      · exact prime_oneHundredFiftyThreeEU_6469
      · exact prime_oneHundredFiftyThreeEU_55589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 586759241213917) ^ 293379620606958 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 586759241213917) ^ 195586413737972 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 586759241213917) ^ 2584842472308 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 586759241213917) ^ 979564676484 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 586759241213917) ^ 90703237164 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 586759241213917) ^ 10555312044 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_777594629002747 : Nat.Prime 777594629002747 := by
  apply lucas_primality 777594629002747 (2 : ZMod 777594629002747)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (9491, 1), (440482171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (9491, 1), (440482171, 1)] : List FactorBlock).map factorBlockValue).prod) = 777594629002747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_31
      · exact prime_oneHundredFiftyThreeEU_9491
      · exact prime_oneHundredFiftyThreeEU_440482171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 777594629002747) ^ 388797314501373 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 777594629002747) ^ 259198209667582 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 777594629002747) ^ 25083697709766 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 777594629002747) ^ 81929683806 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 777594629002747) ^ 1765326 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_819960879280973 : Nat.Prime 819960879280973 := by
  apply lucas_primality 819960879280973 (2 : ZMod 819960879280973)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (13, 1), (79, 1), (167, 1), (5039, 1), (21563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (13, 1), (79, 1), (167, 1), (5039, 1), (21563, 1)] : List FactorBlock).map factorBlockValue).prod) = 819960879280973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_11
      · exact prime_oneHundredFiftyThreeEU_13
      · exact prime_oneHundredFiftyThreeEU_79
      · exact prime_oneHundredFiftyThreeEU_167
      · exact prime_oneHundredFiftyThreeEU_5039
      · exact prime_oneHundredFiftyThreeEU_21563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 819960879280973) ^ 409980439640486 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 819960879280973) ^ 74541898116452 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 819960879280973) ^ 63073913790844 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 819960879280973) ^ 10379251636468 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 819960879280973) ^ 4909945384916 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 819960879280973) ^ 162722936948 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 819960879280973) ^ 38026289444 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_829722028640579 : Nat.Prime 829722028640579 := by
  apply lucas_primality 829722028640579 (2 : ZMod 829722028640579)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (14305552217941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (14305552217941, 1)] : List FactorBlock).map factorBlockValue).prod) = 829722028640579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_29
      · exact prime_oneHundredFiftyThreeEU_14305552217941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 829722028640579) ^ 414861014320289 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 829722028640579) ^ 28611104435882 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 829722028640579) ^ 58 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_866934580455847 : Nat.Prime 866934580455847 := by
  apply lucas_primality 866934580455847 (3 : ZMod 866934580455847)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (6880433178221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (6880433178221, 1)] : List FactorBlock).map factorBlockValue).prod) = 866934580455847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_6880433178221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 866934580455847) ^ 433467290227923 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 866934580455847) ^ 288978193485282 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 866934580455847) ^ 123847797207978 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 866934580455847) ^ 126 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_905648437261739 : Nat.Prime 905648437261739 := by
  apply lucas_primality 905648437261739 (2 : ZMod 905648437261739)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 2), (109, 1), (11507896481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 2), (109, 1), (11507896481, 1)] : List FactorBlock).map factorBlockValue).prod) = 905648437261739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_19
      · exact prime_oneHundredFiftyThreeEU_109
      · exact prime_oneHundredFiftyThreeEU_11507896481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 905648437261739) ^ 452824218630869 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 905648437261739) ^ 47665707224302 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 905648437261739) ^ 8308701259282 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 905648437261739) ^ 78698 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_1261196422592861 : Nat.Prime 1261196422592861 := by
  apply lucas_primality 1261196422592861 (2 : ZMod 1261196422592861)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (3511, 1), (1381588001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (3511, 1), (1381588001, 1)] : List FactorBlock).map factorBlockValue).prod) = 1261196422592861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_13
      · exact prime_oneHundredFiftyThreeEU_3511
      · exact prime_oneHundredFiftyThreeEU_1381588001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1261196422592861) ^ 630598211296430 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1261196422592861) ^ 252239284518572 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1261196422592861) ^ 97015109430220 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1261196422592861) ^ 359212880260 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1261196422592861) ^ 912860 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_1452722104942727 : Nat.Prime 1452722104942727 := by
  apply lucas_primality 1452722104942727 (5 : ZMod 1452722104942727)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (197, 1), (3687111941479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (197, 1), (3687111941479, 1)] : List FactorBlock).map factorBlockValue).prod) = 1452722104942727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_197
      · exact prime_oneHundredFiftyThreeEU_3687111941479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1452722104942727) ^ 726361052471363 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1452722104942727) ^ 7374223882958 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1452722104942727) ^ 394 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_1644289884531667 : Nat.Prime 1644289884531667 := by
  apply lucas_primality 1644289884531667 (2 : ZMod 1644289884531667)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (334973, 1), (272706869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (334973, 1), (272706869, 1)] : List FactorBlock).map factorBlockValue).prod) = 1644289884531667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_334973
      · exact prime_oneHundredFiftyThreeEU_272706869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1644289884531667) ^ 822144942265833 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1644289884531667) ^ 548096628177222 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1644289884531667) ^ 4908723642 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1644289884531667) ^ 6029514 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_1674491817624371 : Nat.Prime 1674491817624371 := by
  apply lucas_primality 1674491817624371 (2 : ZMod 1674491817624371)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (577, 1), (58937, 1), (4924013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (577, 1), (58937, 1), (4924013, 1)] : List FactorBlock).map factorBlockValue).prod) = 1674491817624371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_577
      · exact prime_oneHundredFiftyThreeEU_58937
      · exact prime_oneHundredFiftyThreeEU_4924013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1674491817624371) ^ 837245908812185 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1674491817624371) ^ 334898363524874 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1674491817624371) ^ 2902065541810 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1674491817624371) ^ 28411555010 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1674491817624371) ^ 340066490 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_2307426364027793 : Nat.Prime 2307426364027793 := by
  apply lucas_primality 2307426364027793 (3 : ZMod 2307426364027793)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (19, 1), (769, 1), (1410034981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (19, 1), (769, 1), (1410034981, 1)] : List FactorBlock).map factorBlockValue).prod) = 2307426364027793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_19
      · exact prime_oneHundredFiftyThreeEU_769
      · exact prime_oneHundredFiftyThreeEU_1410034981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2307426364027793) ^ 1153713182013896 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2307426364027793) ^ 329632337718256 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2307426364027793) ^ 121443492843568 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2307426364027793) ^ 3000554439568 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2307426364027793) ^ 1636432 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_2642915032645219 : Nat.Prime 2642915032645219 := by
  apply lucas_primality 2642915032645219 (2 : ZMod 2642915032645219)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (109, 1), (4041154484167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (109, 1), (4041154484167, 1)] : List FactorBlock).map factorBlockValue).prod) = 2642915032645219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_109
      · exact prime_oneHundredFiftyThreeEU_4041154484167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2642915032645219) ^ 1321457516322609 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2642915032645219) ^ 880971677548406 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2642915032645219) ^ 24246926905002 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2642915032645219) ^ 654 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_2667785546635751 : Nat.Prime 2667785546635751 := by
  apply lucas_primality 2667785546635751 (22 : ZMod 2667785546635751)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (97, 1), (228797, 1), (480827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (97, 1), (228797, 1), (480827, 1)] : List FactorBlock).map factorBlockValue).prod) = 2667785546635751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_97
      · exact prime_oneHundredFiftyThreeEU_228797
      · exact prime_oneHundredFiftyThreeEU_480827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 2667785546635751) ^ 1333892773317875 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (22 : ZMod 2667785546635751) ^ 533557109327150 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (22 : ZMod 2667785546635751) ^ 27502943779750 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (22 : ZMod 2667785546635751) ^ 11660054750 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (22 : ZMod 2667785546635751) ^ 5548327250 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_3880197367063769 : Nat.Prime 3880197367063769 := by
  apply lucas_primality 3880197367063769 (3 : ZMod 3880197367063769)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (263, 1), (1844200269517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (263, 1), (1844200269517, 1)] : List FactorBlock).map factorBlockValue).prod) = 3880197367063769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_263
      · exact prime_oneHundredFiftyThreeEU_1844200269517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3880197367063769) ^ 1940098683531884 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3880197367063769) ^ 14753602156136 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3880197367063769) ^ 2104 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_8868662603515027 : Nat.Prime 8868662603515027 := by
  apply lucas_primality 8868662603515027 (11 : ZMod 8868662603515027)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (47, 1), (59, 1), (3119, 1), (4382047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (47, 1), (59, 1), (3119, 1), (4382047, 1)] : List FactorBlock).map factorBlockValue).prod) = 8868662603515027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_13
      · exact prime_oneHundredFiftyThreeEU_47
      · exact prime_oneHundredFiftyThreeEU_59
      · exact prime_oneHundredFiftyThreeEU_3119
      · exact prime_oneHundredFiftyThreeEU_4382047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 8868662603515027) ^ 4434331301757513 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 8868662603515027) ^ 2956220867838342 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 8868662603515027) ^ 682204815655002 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 8868662603515027) ^ 188694949010958 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 8868662603515027) ^ 150316315313814 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 8868662603515027) ^ 2843431421454 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 8868662603515027) ^ 2023862958 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_10069300792568977 : Nat.Prime 10069300792568977 := by
  apply lucas_primality 10069300792568977 (5 : ZMod 10069300792568977)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 2), (1187, 1), (46919, 1), (76871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 2), (1187, 1), (46919, 1), (76871, 1)] : List FactorBlock).map factorBlockValue).prod) = 10069300792568977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_1187
      · exact prime_oneHundredFiftyThreeEU_46919
      · exact prime_oneHundredFiftyThreeEU_76871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 10069300792568977) ^ 5034650396284488 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 10069300792568977) ^ 3356433597522992 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 10069300792568977) ^ 1438471541795568 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 10069300792568977) ^ 8482982976048 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 10069300792568977) ^ 214610302704 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 10069300792568977) ^ 130989590256 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_12915132858396127 : Nat.Prime 12915132858396127 := by
  apply lucas_primality 12915132858396127 (7 : ZMod 12915132858396127)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (41, 1), (83, 1), (1721, 1), (122513389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (41, 1), (83, 1), (1721, 1), (122513389, 1)] : List FactorBlock).map factorBlockValue).prod) = 12915132858396127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_41
      · exact prime_oneHundredFiftyThreeEU_83
      · exact prime_oneHundredFiftyThreeEU_1721
      · exact prime_oneHundredFiftyThreeEU_122513389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 12915132858396127) ^ 6457566429198063 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 12915132858396127) ^ 4305044286132042 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 12915132858396127) ^ 315003240448686 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 12915132858396127) ^ 155604010342122 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 12915132858396127) ^ 7504435129806 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 12915132858396127) ^ 105418134 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_13949245335884777 : Nat.Prime 13949245335884777 := by
  apply lucas_primality 13949245335884777 (3 : ZMod 13949245335884777)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (263, 1), (11003, 1), (602551073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (263, 1), (11003, 1), (602551073, 1)] : List FactorBlock).map factorBlockValue).prod) = 13949245335884777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_263
      · exact prime_oneHundredFiftyThreeEU_11003
      · exact prime_oneHundredFiftyThreeEU_602551073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 13949245335884777) ^ 6974622667942388 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 13949245335884777) ^ 53038955649752 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 13949245335884777) ^ 1267767457592 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 13949245335884777) ^ 23150312 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_14592010719718489 : Nat.Prime 14592010719718489 := by
  apply lucas_primality 14592010719718489 (11 : ZMod 14592010719718489)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 2), (563747, 1), (22010179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 2), (563747, 1), (22010179, 1)] : List FactorBlock).map factorBlockValue).prod) = 14592010719718489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_563747
      · exact prime_oneHundredFiftyThreeEU_22010179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 14592010719718489) ^ 7296005359859244 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 14592010719718489) ^ 4864003573239496 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 14592010719718489) ^ 2084572959959784 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 14592010719718489) ^ 25883970504 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 14592010719718489) ^ 662966472 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_17199000483384449 : Nat.Prime 17199000483384449 := by
  apply lucas_primality 17199000483384449 (3 : ZMod 17199000483384449)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (614279, 1), (218739679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (614279, 1), (218739679, 1)] : List FactorBlock).map factorBlockValue).prod) = 17199000483384449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_614279
      · exact prime_oneHundredFiftyThreeEU_218739679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 17199000483384449) ^ 8599500241692224 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 17199000483384449) ^ 27998678912 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 17199000483384449) ^ 78627712 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_18708723398918219 : Nat.Prime 18708723398918219 := by
  apply lucas_primality 18708723398918219 (2 : ZMod 18708723398918219)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12487, 1), (242173, 1), (3093359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12487, 1), (242173, 1), (3093359, 1)] : List FactorBlock).map factorBlockValue).prod) = 18708723398918219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_12487
      · exact prime_oneHundredFiftyThreeEU_242173
      · exact prime_oneHundredFiftyThreeEU_3093359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 18708723398918219) ^ 9354361699459109 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 18708723398918219) ^ 1498256058214 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 18708723398918219) ^ 77253547666 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 18708723398918219) ^ 6048028502 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_32736500018324309 : Nat.Prime 32736500018324309 := by
  apply lucas_primality 32736500018324309 (2 : ZMod 32736500018324309)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (61, 2), (110119, 1), (19973323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (61, 2), (110119, 1), (19973323, 1)] : List FactorBlock).map factorBlockValue).prod) = 32736500018324309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_61
      · exact prime_oneHundredFiftyThreeEU_110119
      · exact prime_oneHundredFiftyThreeEU_19973323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32736500018324309) ^ 16368250009162154 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 32736500018324309) ^ 536663934726628 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 32736500018324309) ^ 297282939532 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 32736500018324309) ^ 1639011196 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_36532893612773123 : Nat.Prime 36532893612773123 := by
  apply lucas_primality 36532893612773123 (2 : ZMod 36532893612773123)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (151, 1), (49787, 1), (2429747653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (151, 1), (49787, 1), (2429747653, 1)] : List FactorBlock).map factorBlockValue).prod) = 36532893612773123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_151
      · exact prime_oneHundredFiftyThreeEU_49787
      · exact prime_oneHundredFiftyThreeEU_2429747653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 36532893612773123) ^ 18266446806386561 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 36532893612773123) ^ 241939692799822 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 36532893612773123) ^ 733783791206 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 36532893612773123) ^ 15035674 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_88451082786507737 : Nat.Prime 88451082786507737 := by
  apply lucas_primality 88451082786507737 (3 : ZMod 88451082786507737)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (311, 1), (108011, 1), (11349763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (311, 1), (108011, 1), (11349763, 1)] : List FactorBlock).map factorBlockValue).prod) = 88451082786507737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_29
      · exact prime_oneHundredFiftyThreeEU_311
      · exact prime_oneHundredFiftyThreeEU_108011
      · exact prime_oneHundredFiftyThreeEU_11349763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 88451082786507737) ^ 44225541393253868 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 88451082786507737) ^ 3050037337465784 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 88451082786507737) ^ 284408626323176 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 88451082786507737) ^ 818908099976 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 88451082786507737) ^ 7793209672 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_129965791298926081 : Nat.Prime 129965791298926081 := by
  apply lucas_primality 129965791298926081 (29 : ZMod 129965791298926081)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 1), (5, 1), (16922629075381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 1), (5, 1), (16922629075381, 1)] : List FactorBlock).map factorBlockValue).prod) = 129965791298926081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_16922629075381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (29 : ZMod 129965791298926081) ^ 64982895649463040 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (29 : ZMod 129965791298926081) ^ 43321930432975360 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (29 : ZMod 129965791298926081) ^ 25993158259785216 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (29 : ZMod 129965791298926081) ^ 7680 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_179015947322826907 : Nat.Prime 179015947322826907 := by
  apply lucas_primality 179015947322826907 (2 : ZMod 179015947322826907)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5009, 1), (1985492195413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5009, 1), (1985492195413, 1)] : List FactorBlock).map factorBlockValue).prod) = 179015947322826907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5009
      · exact prime_oneHundredFiftyThreeEU_1985492195413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 179015947322826907) ^ 89507973661413453 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 179015947322826907) ^ 59671982440942302 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 179015947322826907) ^ 35738859517434 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 179015947322826907) ^ 90162 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_280756657691039723 : Nat.Prime 280756657691039723 := by
  apply lucas_primality 280756657691039723 (2 : ZMod 280756657691039723)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (41, 1), (596257, 1), (155196169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (41, 1), (596257, 1), (155196169, 1)] : List FactorBlock).map factorBlockValue).prod) = 280756657691039723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_37
      · exact prime_oneHundredFiftyThreeEU_41
      · exact prime_oneHundredFiftyThreeEU_596257
      · exact prime_oneHundredFiftyThreeEU_155196169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 280756657691039723) ^ 140378328845519861 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 280756657691039723) ^ 7588017775433506 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 280756657691039723) ^ 6847723358318042 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 280756657691039723) ^ 470865176746 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 280756657691039723) ^ 1809043738 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_343207110292651133 : Nat.Prime 343207110292651133 := by
  apply lucas_primality 343207110292651133 (2 : ZMod 343207110292651133)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (41, 1), (373, 1), (510047838721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (41, 1), (373, 1), (510047838721, 1)] : List FactorBlock).map factorBlockValue).prod) = 343207110292651133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_11
      · exact prime_oneHundredFiftyThreeEU_41
      · exact prime_oneHundredFiftyThreeEU_373
      · exact prime_oneHundredFiftyThreeEU_510047838721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 343207110292651133) ^ 171603555146325566 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 343207110292651133) ^ 31200646390241012 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 343207110292651133) ^ 8370905129089052 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 343207110292651133) ^ 920126301052684 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 343207110292651133) ^ 672892 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_433739769425541289 : Nat.Prime 433739769425541289 := by
  apply lucas_primality 433739769425541289 (22 : ZMod 433739769425541289)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (19, 1), (765727, 1), (414065633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (19, 1), (765727, 1), (414065633, 1)] : List FactorBlock).map factorBlockValue).prod) = 433739769425541289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_19
      · exact prime_oneHundredFiftyThreeEU_765727
      · exact prime_oneHundredFiftyThreeEU_414065633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 433739769425541289) ^ 216869884712770644 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (22 : ZMod 433739769425541289) ^ 144579923141847096 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (22 : ZMod 433739769425541289) ^ 22828408917133752 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (22 : ZMod 433739769425541289) ^ 566441785944 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (22 : ZMod 433739769425541289) ^ 1047514536 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_446570538165885137 : Nat.Prime 446570538165885137 := by
  apply lucas_primality 446570538165885137 (3 : ZMod 446570538165885137)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (331, 1), (433, 1), (194739564727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (331, 1), (433, 1), (194739564727, 1)] : List FactorBlock).map factorBlockValue).prod) = 446570538165885137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_331
      · exact prime_oneHundredFiftyThreeEU_433
      · exact prime_oneHundredFiftyThreeEU_194739564727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 446570538165885137) ^ 223285269082942568 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 446570538165885137) ^ 1349155704428656 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 446570538165885137) ^ 1031340734794192 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 446570538165885137) ^ 2293168 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_491922215272605121 : Nat.Prime 491922215272605121 := by
  apply lucas_primality 491922215272605121 (29 : ZMod 491922215272605121)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (19, 1), (193, 1), (353, 1), (1553, 1), (254899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (19, 1), (193, 1), (353, 1), (1553, 1), (254899, 1)] : List FactorBlock).map factorBlockValue).prod) = 491922215272605121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_19
      · exact prime_oneHundredFiftyThreeEU_193
      · exact prime_oneHundredFiftyThreeEU_353
      · exact prime_oneHundredFiftyThreeEU_1553
      · exact prime_oneHundredFiftyThreeEU_254899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 491922215272605121) ^ 245961107636302560 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (29 : ZMod 491922215272605121) ^ 163974071757535040 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (29 : ZMod 491922215272605121) ^ 98384443054521024 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (29 : ZMod 491922215272605121) ^ 25890642909084480 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (29 : ZMod 491922215272605121) ^ 2548819768251840 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (29 : ZMod 491922215272605121) ^ 1393547352047040 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (29 : ZMod 491922215272605121) ^ 316756094831040 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (29 : ZMod 491922215272605121) ^ 1929871106880 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_583680428788739561 : Nat.Prime 583680428788739561 := by
  apply lucas_primality 583680428788739561 (6 : ZMod 583680428788739561)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (14592010719718489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (14592010719718489, 1)] : List FactorBlock).map factorBlockValue).prod) = 583680428788739561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_14592010719718489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 583680428788739561) ^ 291840214394369780 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 583680428788739561) ^ 116736085757747912 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 583680428788739561) ^ 40 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_615155913718803313 : Nat.Prime 615155913718803313 := by
  apply lucas_primality 615155913718803313 (10 : ZMod 615155913718803313)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (59, 1), (73, 1), (941329, 1), (3161023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (59, 1), (73, 1), (941329, 1), (3161023, 1)] : List FactorBlock).map factorBlockValue).prod) = 615155913718803313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_59
      · exact prime_oneHundredFiftyThreeEU_73
      · exact prime_oneHundredFiftyThreeEU_941329
      · exact prime_oneHundredFiftyThreeEU_3161023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 615155913718803313) ^ 307577956859401656 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (10 : ZMod 615155913718803313) ^ 205051971239601104 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (10 : ZMod 615155913718803313) ^ 10426371418962768 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (10 : ZMod 615155913718803313) ^ 8426793338613744 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (10 : ZMod 615155913718803313) ^ 653497250928 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (10 : ZMod 615155913718803313) ^ 194606592144 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_622239869447863171 : Nat.Prime 622239869447863171 := by
  apply lucas_primality 622239869447863171 (2 : ZMod 622239869447863171)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (17, 1), (19, 1), (107, 1), (85733832857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (17, 1), (19, 1), (107, 1), (85733832857, 1)] : List FactorBlock).map factorBlockValue).prod) = 622239869447863171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_17
      · exact prime_oneHundredFiftyThreeEU_19
      · exact prime_oneHundredFiftyThreeEU_107
      · exact prime_oneHundredFiftyThreeEU_85733832857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 622239869447863171) ^ 311119934723931585 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 622239869447863171) ^ 207413289815954390 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 622239869447863171) ^ 124447973889572634 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 622239869447863171) ^ 88891409921123310 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 622239869447863171) ^ 36602345261639010 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 622239869447863171) ^ 32749466813045430 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 622239869447863171) ^ 5815325882690310 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 622239869447863171) ^ 7257810 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_646209123146981599 : Nat.Prime 646209123146981599 := by
  apply lucas_primality 646209123146981599 (15 : ZMod 646209123146981599)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (552127, 1), (195066570779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (552127, 1), (195066570779, 1)] : List FactorBlock).map factorBlockValue).prod) = 646209123146981599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_552127
      · exact prime_oneHundredFiftyThreeEU_195066570779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 646209123146981599) ^ 323104561573490799 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (15 : ZMod 646209123146981599) ^ 215403041048993866 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (15 : ZMod 646209123146981599) ^ 1170399424674 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (15 : ZMod 646209123146981599) ^ 3312762 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_2656574897467719719 : Nat.Prime 2656574897467719719 := by
  apply lucas_primality 2656574897467719719 (7 : ZMod 2656574897467719719)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (37, 1), (42323, 1), (121175790187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (37, 1), (42323, 1), (121175790187, 1)] : List FactorBlock).map factorBlockValue).prod) = 2656574897467719719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_37
      · exact prime_oneHundredFiftyThreeEU_42323
      · exact prime_oneHundredFiftyThreeEU_121175790187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2656574897467719719) ^ 1328287448733859859 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 2656574897467719719) ^ 379510699638245674 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 2656574897467719719) ^ 71799321553181614 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 2656574897467719719) ^ 62769059316866 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 2656574897467719719) ^ 21923314 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_5370478419684807211 : Nat.Prime 5370478419684807211 := by
  apply lucas_primality 5370478419684807211 (2 : ZMod 5370478419684807211)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (179015947322826907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (179015947322826907, 1)] : List FactorBlock).map factorBlockValue).prod) = 5370478419684807211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_179015947322826907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5370478419684807211) ^ 2685239209842403605 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 5370478419684807211) ^ 1790159473228269070 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 5370478419684807211) ^ 1074095683936961442 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 5370478419684807211) ^ 30 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_6658771846286753917 : Nat.Prime 6658771846286753917 := by
  apply lucas_primality 6658771846286753917 (2 : ZMod 6658771846286753917)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (283, 1), (1873, 1), (1046860168127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (283, 1), (1873, 1), (1046860168127, 1)] : List FactorBlock).map factorBlockValue).prod) = 6658771846286753917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_283
      · exact prime_oneHundredFiftyThreeEU_1873
      · exact prime_oneHundredFiftyThreeEU_1046860168127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6658771846286753917) ^ 3329385923143376958 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 6658771846286753917) ^ 2219590615428917972 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 6658771846286753917) ^ 23529229138822452 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 6658771846286753917) ^ 3555137130959292 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 6658771846286753917) ^ 6360708 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_6844668155500488517 : Nat.Prime 6844668155500488517 := by
  apply lucas_primality 6844668155500488517 (5 : ZMod 6844668155500488517)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 2), (3880197367063769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 2), (3880197367063769, 1)] : List FactorBlock).map factorBlockValue).prod) = 6844668155500488517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_3880197367063769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6844668155500488517) ^ 3422334077750244258 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 6844668155500488517) ^ 2281556051833496172 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 6844668155500488517) ^ 977809736500069788 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 6844668155500488517) ^ 1764 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_8108655896759637073 : Nat.Prime 8108655896759637073 := by
  apply lucas_primality 8108655896759637073 (5 : ZMod 8108655896759637073)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (4877, 1), (4948309299701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (4877, 1), (4948309299701, 1)] : List FactorBlock).map factorBlockValue).prod) = 8108655896759637073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_4877
      · exact prime_oneHundredFiftyThreeEU_4948309299701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 8108655896759637073) ^ 4054327948379818536 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 8108655896759637073) ^ 2702885298919879024 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 8108655896759637073) ^ 1158379413822805296 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 8108655896759637073) ^ 1662631924699536 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 8108655896759637073) ^ 1638672 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_10827953699639743921 : Nat.Prime 10827953699639743921 := by
  apply lucas_primality 10827953699639743921 (13 : ZMod 10827953699639743921)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (11, 1), (257, 1), (1999, 1), (5519, 1), (1446559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (11, 1), (257, 1), (1999, 1), (5519, 1), (1446559, 1)] : List FactorBlock).map factorBlockValue).prod) = 10827953699639743921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_11
      · exact prime_oneHundredFiftyThreeEU_257
      · exact prime_oneHundredFiftyThreeEU_1999
      · exact prime_oneHundredFiftyThreeEU_5519
      · exact prime_oneHundredFiftyThreeEU_1446559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 10827953699639743921) ^ 5413976849819871960 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (13 : ZMod 10827953699639743921) ^ 3609317899879914640 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (13 : ZMod 10827953699639743921) ^ 2165590739927948784 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (13 : ZMod 10827953699639743921) ^ 984359427239976720 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (13 : ZMod 10827953699639743921) ^ 42132115562800560 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (13 : ZMod 10827953699639743921) ^ 5416685192416080 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (13 : ZMod 10827953699639743921) ^ 1961941239289680 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (13 : ZMod 10827953699639743921) ^ 7485317708880 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_12144713543915156093 : Nat.Prime 12144713543915156093 := by
  apply lucas_primality 12144713543915156093 (2 : ZMod 12144713543915156093)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (433739769425541289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (433739769425541289, 1)] : List FactorBlock).map factorBlockValue).prod) = 12144713543915156093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_433739769425541289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 12144713543915156093) ^ 6072356771957578046 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 12144713543915156093) ^ 1734959077702165156 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 12144713543915156093) ^ 28 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_14733701218282151909 : Nat.Prime 14733701218282151909 := by
  apply lucas_primality 14733701218282151909 (2 : ZMod 14733701218282151909)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (4259, 1), (9859, 1), (7974779347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (4259, 1), (9859, 1), (7974779347, 1)] : List FactorBlock).map factorBlockValue).prod) = 14733701218282151909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_11
      · exact prime_oneHundredFiftyThreeEU_4259
      · exact prime_oneHundredFiftyThreeEU_9859
      · exact prime_oneHundredFiftyThreeEU_7974779347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14733701218282151909) ^ 7366850609141075954 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 14733701218282151909) ^ 1339427383480195628 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 14733701218282151909) ^ 3459427381611212 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 14733701218282151909) ^ 1494441750510412 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 14733701218282151909) ^ 1847537164 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_17768221546474086847 : Nat.Prime 17768221546474086847 := by
  apply lucas_primality 17768221546474086847 (3 : ZMod 17768221546474086847)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (71, 1), (10008491, 1), (4167405481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (71, 1), (10008491, 1), (4167405481, 1)] : List FactorBlock).map factorBlockValue).prod) = 17768221546474086847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_71
      · exact prime_oneHundredFiftyThreeEU_10008491
      · exact prime_oneHundredFiftyThreeEU_4167405481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 17768221546474086847) ^ 8884110773237043423 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 17768221546474086847) ^ 5922740515491362282 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 17768221546474086847) ^ 250256641499635026 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 17768221546474086847) ^ 1775314734906 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 17768221546474086847) ^ 4263617166 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_17775058921576688827 : Nat.Prime 17775058921576688827 := by
  apply lucas_primality 17775058921576688827 (5 : ZMod 17775058921576688827)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 6), (23, 1), (115853, 1), (4575287663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 6), (23, 1), (115853, 1), (4575287663, 1)] : List FactorBlock).map factorBlockValue).prod) = 17775058921576688827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_23
      · exact prime_oneHundredFiftyThreeEU_115853
      · exact prime_oneHundredFiftyThreeEU_4575287663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 17775058921576688827) ^ 8887529460788344413 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 17775058921576688827) ^ 5925019640525562942 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 17775058921576688827) ^ 772828648764203862 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 17775058921576688827) ^ 153427696491042 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 17775058921576688827) ^ 3885014502 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_18093855448115484773 : Nat.Prime 18093855448115484773 := by
  apply lucas_primality 18093855448115484773 (2 : ZMod 18093855448115484773)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (646209123146981599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (646209123146981599, 1)] : List FactorBlock).map factorBlockValue).prod) = 18093855448115484773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_646209123146981599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 18093855448115484773) ^ 9046927724057742386 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 18093855448115484773) ^ 2584836492587926396 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 18093855448115484773) ^ 28 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_41565487955259148373 : Nat.Prime 41565487955259148373 := by
  apply lucas_primality 41565487955259148373 (2 : ZMod 41565487955259148373)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (53, 1), (107, 1), (181, 1), (10123592834743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (53, 1), (107, 1), (181, 1), (10123592834743, 1)] : List FactorBlock).map factorBlockValue).prod) = 41565487955259148373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_53
      · exact prime_oneHundredFiftyThreeEU_107
      · exact prime_oneHundredFiftyThreeEU_181
      · exact prime_oneHundredFiftyThreeEU_10123592834743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 41565487955259148373) ^ 20782743977629574186 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 41565487955259148373) ^ 784254489721870724 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 41565487955259148373) ^ 388462504254758396 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 41565487955259148373) ^ 229643579863310212 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 41565487955259148373) ^ 4105804 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_42175048333700274353 : Nat.Prime 42175048333700274353 := by
  apply lucas_primality 42175048333700274353 (3 : ZMod 42175048333700274353)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (37, 1), (661, 1), (7639153, 1), (14108707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (37, 1), (661, 1), (7639153, 1), (14108707, 1)] : List FactorBlock).map factorBlockValue).prod) = 42175048333700274353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_37
      · exact prime_oneHundredFiftyThreeEU_661
      · exact prime_oneHundredFiftyThreeEU_7639153
      · exact prime_oneHundredFiftyThreeEU_14108707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 42175048333700274353) ^ 21087524166850137176 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 42175048333700274353) ^ 1139866171181088496 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 42175048333700274353) ^ 63804914271861232 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 42175048333700274353) ^ 5520906353584 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 42175048333700274353) ^ 2989292238736 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_74343867354410825099 : Nat.Prime 74343867354410825099 := by
  apply lucas_primality 74343867354410825099 (2 : ZMod 74343867354410825099)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (103, 1), (4099, 1), (88044049761617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (103, 1), (4099, 1), (88044049761617, 1)] : List FactorBlock).map factorBlockValue).prod) = 74343867354410825099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_103
      · exact prime_oneHundredFiftyThreeEU_4099
      · exact prime_oneHundredFiftyThreeEU_88044049761617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 74343867354410825099) ^ 37171933677205412549 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 74343867354410825099) ^ 721785119945736166 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 74343867354410825099) ^ 18137074250893102 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 74343867354410825099) ^ 844394 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_92677915656529465343 : Nat.Prime 92677915656529465343 := by
  apply lucas_primality 92677915656529465343 (5 : ZMod 92677915656529465343)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (599, 1), (21481, 1), (211843929377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (599, 1), (21481, 1), (211843929377, 1)] : List FactorBlock).map factorBlockValue).prod) = 92677915656529465343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_17
      · exact prime_oneHundredFiftyThreeEU_599
      · exact prime_oneHundredFiftyThreeEU_21481
      · exact prime_oneHundredFiftyThreeEU_211843929377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 92677915656529465343) ^ 46338957828264732671 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 92677915656529465343) ^ 5451642097442909726 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 92677915656529465343) ^ 154721061196209458 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 92677915656529465343) ^ 4314413465691982 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 92677915656529465343) ^ 437482046 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_256223811061086791179 : Nat.Prime 256223811061086791179 := by
  apply lucas_primality 256223811061086791179 (2 : ZMod 256223811061086791179)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) = 256223811061086791179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_17
      · exact prime_oneHundredFiftyThreeEU_6863
      · exact prime_oneHundredFiftyThreeEU_366020420757353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 256223811061086791179) ^ 128111905530543395589 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 85407937020362263726 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 15071988885946281834 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 37334082917250006 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 700026 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_390359874745593903637 : Nat.Prime 390359874745593903637 := by
  apply lucas_primality 390359874745593903637 (2 : ZMod 390359874745593903637)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13697, 1), (674117, 1), (1174361849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13697, 1), (674117, 1), (1174361849, 1)] : List FactorBlock).map factorBlockValue).prod) = 390359874745593903637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_13697
      · exact prime_oneHundredFiftyThreeEU_674117
      · exact prime_oneHundredFiftyThreeEU_1174361849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 390359874745593903637) ^ 195179937372796951818 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 390359874745593903637) ^ 130119958248531301212 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 390359874745593903637) ^ 28499662316243988 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 390359874745593903637) ^ 579068432847108 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 390359874745593903637) ^ 332401699764 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_464037582103899526753 : Nat.Prime 464037582103899526753 := by
  apply lucas_primality 464037582103899526753 (10 : ZMod 464037582103899526753)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (691, 1), (2423, 1), (2887024441709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (691, 1), (2423, 1), (2887024441709, 1)] : List FactorBlock).map factorBlockValue).prod) = 464037582103899526753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_691
      · exact prime_oneHundredFiftyThreeEU_2423
      · exact prime_oneHundredFiftyThreeEU_2887024441709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 464037582103899526753) ^ 232018791051949763376 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (10 : ZMod 464037582103899526753) ^ 154679194034633175584 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (10 : ZMod 464037582103899526753) ^ 671544981337047072 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (10 : ZMod 464037582103899526753) ^ 191513653365208224 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (10 : ZMod 464037582103899526753) ^ 160732128 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_1037281285622657708491 : Nat.Prime 1037281285622657708491 := by
  apply lucas_primality 1037281285622657708491 (2 : ZMod 1037281285622657708491)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (13, 1), (56093, 1), (4310529111817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (13, 1), (56093, 1), (4310529111817, 1)] : List FactorBlock).map factorBlockValue).prod) = 1037281285622657708491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_11
      · exact prime_oneHundredFiftyThreeEU_13
      · exact prime_oneHundredFiftyThreeEU_56093
      · exact prime_oneHundredFiftyThreeEU_4310529111817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1037281285622657708491) ^ 518640642811328854245 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1037281285622657708491) ^ 345760428540885902830 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1037281285622657708491) ^ 207456257124531541698 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1037281285622657708491) ^ 94298298692968882590 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1037281285622657708491) ^ 79790868124819823730 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1037281285622657708491) ^ 18492169889694930 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1037281285622657708491) ^ 240638970 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_1198578932331615705061 : Nat.Prime 1198578932331615705061 := by
  apply lucas_primality 1198578932331615705061 (2 : ZMod 1198578932331615705061)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (6658771846286753917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (6658771846286753917, 1)] : List FactorBlock).map factorBlockValue).prod) = 1198578932331615705061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_6658771846286753917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1198578932331615705061) ^ 599289466165807852530 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1198578932331615705061) ^ 399526310777205235020 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1198578932331615705061) ^ 239715786466323141012 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1198578932331615705061) ^ 180 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_1252193736375132378829 : Nat.Prime 1252193736375132378829 := by
  apply lucas_primality 1252193736375132378829 (2 : ZMod 1252193736375132378829)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (11, 2), (13, 1), (109303, 1), (86702463293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (11, 2), (13, 1), (109303, 1), (86702463293, 1)] : List FactorBlock).map factorBlockValue).prod) = 1252193736375132378829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_11
      · exact prime_oneHundredFiftyThreeEU_13
      · exact prime_oneHundredFiftyThreeEU_109303
      · exact prime_oneHundredFiftyThreeEU_86702463293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1252193736375132378829) ^ 626096868187566189414 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1252193736375132378829) ^ 417397912125044126276 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1252193736375132378829) ^ 178884819482161768404 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1252193736375132378829) ^ 113835794215921125348 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1252193736375132378829) ^ 96322595105779413756 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1252193736375132378829) ^ 11456169879830676 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1252193736375132378829) ^ 14442423996 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_2334900312219571567777 : Nat.Prime 2334900312219571567777 := by
  apply lucas_primality 2334900312219571567777 (5 : ZMod 2334900312219571567777)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (1736981, 1), (4667461964617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (1736981, 1), (4667461964617, 1)] : List FactorBlock).map factorBlockValue).prod) = 2334900312219571567777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_1736981
      · exact prime_oneHundredFiftyThreeEU_4667461964617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2334900312219571567777) ^ 1167450156109785783888 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2334900312219571567777) ^ 778300104073190522592 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2334900312219571567777) ^ 1344229045809696 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2334900312219571567777) ^ 500250528 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_2813618332621299169817 : Nat.Prime 2813618332621299169817 := by
  apply lucas_primality 2813618332621299169817 (3 : ZMod 2813618332621299169817)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (61, 1), (2273, 1), (22469, 1), (112891744211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (61, 1), (2273, 1), (22469, 1), (112891744211, 1)] : List FactorBlock).map factorBlockValue).prod) = 2813618332621299169817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_61
      · exact prime_oneHundredFiftyThreeEU_2273
      · exact prime_oneHundredFiftyThreeEU_22469
      · exact prime_oneHundredFiftyThreeEU_112891744211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2813618332621299169817) ^ 1406809166310649584908 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2813618332621299169817) ^ 46124890698709822456 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2813618332621299169817) ^ 1237843525130355992 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2813618332621299169817) ^ 125222232080702264 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2813618332621299169817) ^ 24923154056 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_2916008306114041495759 : Nat.Prime 2916008306114041495759 := by
  apply lucas_primality 2916008306114041495759 (3 : ZMod 2916008306114041495759)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (43, 1), (163, 1), (3437719, 1), (695525527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (43, 1), (163, 1), (3437719, 1), (695525527, 1)] : List FactorBlock).map factorBlockValue).prod) = 2916008306114041495759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_29
      · exact prime_oneHundredFiftyThreeEU_43
      · exact prime_oneHundredFiftyThreeEU_163
      · exact prime_oneHundredFiftyThreeEU_3437719
      · exact prime_oneHundredFiftyThreeEU_695525527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2916008306114041495759) ^ 1458004153057020747879 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2916008306114041495759) ^ 972002768704680498586 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2916008306114041495759) ^ 100552010555656603302 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2916008306114041495759) ^ 67814146653814918506 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2916008306114041495759) ^ 17889621509902095066 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2916008306114041495759) ^ 848239284861282 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2916008306114041495759) ^ 4192525209954 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_3074685732733041494149 : Nat.Prime 3074685732733041494149 := by
  apply lucas_primality 3074685732733041494149 (2 : ZMod 3074685732733041494149)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) = 3074685732733041494149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_256223811061086791179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3074685732733041494149) ^ 1537342866366520747074 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 1024895244244347164716 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 12 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_5614410452457018199843 : Nat.Prime 5614410452457018199843 := by
  apply lucas_primality 5614410452457018199843 (3 : ZMod 5614410452457018199843)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (19, 1), (37, 1), (71, 1), (101, 1), (6874705481557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (19, 1), (37, 1), (71, 1), (101, 1), (6874705481557, 1)] : List FactorBlock).map factorBlockValue).prod) = 5614410452457018199843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_19
      · exact prime_oneHundredFiftyThreeEU_37
      · exact prime_oneHundredFiftyThreeEU_71
      · exact prime_oneHundredFiftyThreeEU_101
      · exact prime_oneHundredFiftyThreeEU_6874705481557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5614410452457018199843) ^ 2807205226228509099921 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 5614410452457018199843) ^ 1871470150819006066614 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 5614410452457018199843) ^ 295495286971422010518 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 5614410452457018199843) ^ 151740823039378870266 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 5614410452457018199843) ^ 79076203555732650702 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 5614410452457018199843) ^ 55588222301554635642 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 5614410452457018199843) ^ 816676506 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_9053071540272876705469 : Nat.Prime 9053071540272876705469 := by
  apply lucas_primality 9053071540272876705469 (6 : ZMod 9053071540272876705469)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (3948289019, 1), (17370530621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (3948289019, 1), (17370530621, 1)] : List FactorBlock).map factorBlockValue).prod) = 9053071540272876705469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_11
      · exact prime_oneHundredFiftyThreeEU_3948289019
      · exact prime_oneHundredFiftyThreeEU_17370530621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 9053071540272876705469) ^ 4526535770136438352734 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 9053071540272876705469) ^ 3017690513424292235156 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 9053071540272876705469) ^ 823006503661170609588 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 9053071540272876705469) ^ 2292910041972 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 9053071540272876705469) ^ 521174150508 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_11326947571685218147231 : Nat.Prime 11326947571685218147231 := by
  apply lucas_primality 11326947571685218147231 (3 : ZMod 11326947571685218147231)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (41, 1), (57868189, 1), (159135798509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (41, 1), (57868189, 1), (159135798509, 1)] : List FactorBlock).map factorBlockValue).prod) = 11326947571685218147231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_41
      · exact prime_oneHundredFiftyThreeEU_57868189
      · exact prime_oneHundredFiftyThreeEU_159135798509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11326947571685218147231) ^ 5663473785842609073615 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 11326947571685218147231) ^ 3775649190561739382410 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 11326947571685218147231) ^ 2265389514337043629446 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 11326947571685218147231) ^ 276267013943541906030 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 11326947571685218147231) ^ 195737032166070 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 11326947571685218147231) ^ 71177872470 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_31929943405877625702499 : Nat.Prime 31929943405877625702499 := by
  apply lucas_primality 31929943405877625702499 (14 : ZMod 31929943405877625702499)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (167267, 1), (1674491817624371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (167267, 1), (1674491817624371, 1)] : List FactorBlock).map factorBlockValue).prod) = 31929943405877625702499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_19
      · exact prime_oneHundredFiftyThreeEU_167267
      · exact prime_oneHundredFiftyThreeEU_1674491817624371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 31929943405877625702499) ^ 15964971702938812851249 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (14 : ZMod 31929943405877625702499) ^ 10643314468625875234166 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (14 : ZMod 31929943405877625702499) ^ 1680523337151453984342 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (14 : ZMod 31929943405877625702499) ^ 190892067209178294 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (14 : ZMod 31929943405877625702499) ^ 19068438 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_33188673502746444555329 : Nat.Prime 33188673502746444555329 := by
  apply lucas_primality 33188673502746444555329 (3 : ZMod 33188673502746444555329)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (185723, 1), (45991931, 1), (60710329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (185723, 1), (45991931, 1), (60710329, 1)] : List FactorBlock).map factorBlockValue).prod) = 33188673502746444555329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_185723
      · exact prime_oneHundredFiftyThreeEU_45991931
      · exact prime_oneHundredFiftyThreeEU_60710329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 33188673502746444555329) ^ 16594336751373222277664 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 33188673502746444555329) ^ 178699856790739136 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 33188673502746444555329) ^ 721619483703488 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 33188673502746444555329) ^ 546672601671232 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_33335944120492101516949 : Nat.Prime 33335944120492101516949 := by
  apply lucas_primality 33335944120492101516949 (6 : ZMod 33335944120492101516949)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (159013, 1), (30237821, 1), (44443171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (159013, 1), (30237821, 1), (44443171, 1)] : List FactorBlock).map factorBlockValue).prod) = 33335944120492101516949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_13
      · exact prime_oneHundredFiftyThreeEU_159013
      · exact prime_oneHundredFiftyThreeEU_30237821
      · exact prime_oneHundredFiftyThreeEU_44443171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 33335944120492101516949) ^ 16667972060246050758474 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 33335944120492101516949) ^ 11111981373497367172316 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 33335944120492101516949) ^ 2564303393884007808996 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 33335944120492101516949) ^ 209642885301780996 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 33335944120492101516949) ^ 1102458544234788 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 33335944120492101516949) ^ 750080234384988 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_46705832861954421551531 : Nat.Prime 46705832861954421551531 := by
  apply lucas_primality 46705832861954421551531 (2 : ZMod 46705832861954421551531)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (317, 1), (14733701218282151909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (317, 1), (14733701218282151909, 1)] : List FactorBlock).map factorBlockValue).prod) = 46705832861954421551531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_317
      · exact prime_oneHundredFiftyThreeEU_14733701218282151909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 46705832861954421551531) ^ 23352916430977210775765 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 46705832861954421551531) ^ 9341166572390884310306 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 46705832861954421551531) ^ 147337012182821519090 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 46705832861954421551531) ^ 3170 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_78334371920792006198453 : Nat.Prime 78334371920792006198453 := by
  apply lucas_primality 78334371920792006198453 (2 : ZMod 78334371920792006198453)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (13, 1), (1033, 1), (6359, 1), (5583499, 1), (5867531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (13, 1), (1033, 1), (6359, 1), (5583499, 1), (5867531, 1)] : List FactorBlock).map factorBlockValue).prod) = 78334371920792006198453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_13
      · exact prime_oneHundredFiftyThreeEU_1033
      · exact prime_oneHundredFiftyThreeEU_6359
      · exact prime_oneHundredFiftyThreeEU_5583499
      · exact prime_oneHundredFiftyThreeEU_5867531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 78334371920792006198453) ^ 39167185960396003099226 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 78334371920792006198453) ^ 11190624560113143742636 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 78334371920792006198453) ^ 6025720916984000476804 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 78334371920792006198453) ^ 75831918606768641044 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 78334371920792006198453) ^ 12318662041325995628 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 78334371920792006198453) ^ 14029620480059548 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 78334371920792006198453) ^ 13350482838657692 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_113225170033351484527733 : Nat.Prime 113225170033351484527733 := by
  apply lucas_primality 113225170033351484527733 (2 : ZMod 113225170033351484527733)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (61, 1), (464037582103899526753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (61, 1), (464037582103899526753, 1)] : List FactorBlock).map factorBlockValue).prod) = 113225170033351484527733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_61
      · exact prime_oneHundredFiftyThreeEU_464037582103899526753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 113225170033351484527733) ^ 56612585016675742263866 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 113225170033351484527733) ^ 1856150328415598107012 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 113225170033351484527733) ^ 244 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_124382568716388360003547 : Nat.Prime 124382568716388360003547 := by
  apply lucas_primality 124382568716388360003547 (2 : ZMod 124382568716388360003547)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (137, 1), (1221503, 1), (2173293146033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (137, 1), (1221503, 1), (2173293146033, 1)] : List FactorBlock).map factorBlockValue).prod) = 124382568716388360003547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_19
      · exact prime_oneHundredFiftyThreeEU_137
      · exact prime_oneHundredFiftyThreeEU_1221503
      · exact prime_oneHundredFiftyThreeEU_2173293146033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 124382568716388360003547) ^ 62191284358194180001773 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 124382568716388360003547) ^ 41460856238796120001182 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 124382568716388360003547) ^ 6546450985073071579134 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 124382568716388360003547) ^ 907901961433491678858 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 124382568716388360003547) ^ 101827477064230182 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 124382568716388360003547) ^ 57232301562 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_267288710947712854891471 : Nat.Prime 267288710947712854891471 := by
  apply lucas_primality 267288710947712854891471 (6 : ZMod 267288710947712854891471)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (79, 1), (5370478419684807211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (79, 1), (5370478419684807211, 1)] : List FactorBlock).map factorBlockValue).prod) = 267288710947712854891471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_79
      · exact prime_oneHundredFiftyThreeEU_5370478419684807211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 267288710947712854891471) ^ 133644355473856427445735 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 267288710947712854891471) ^ 89096236982570951630490 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 267288710947712854891471) ^ 53457742189542570978294 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 267288710947712854891471) ^ 38184101563958979270210 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 267288710947712854891471) ^ 3383401404401428542930 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (6 : ZMod 267288710947712854891471) ^ 49770 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_326085558654121941097051 : Nat.Prime 326085558654121941097051 := by
  apply lucas_primality 326085558654121941097051 (2 : ZMod 326085558654121941097051)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (179, 1), (12144713543915156093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (179, 1), (12144713543915156093, 1)] : List FactorBlock).map factorBlockValue).prod) = 326085558654121941097051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_179
      · exact prime_oneHundredFiftyThreeEU_12144713543915156093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 326085558654121941097051) ^ 163042779327060970548525 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 326085558654121941097051) ^ 108695186218040647032350 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 326085558654121941097051) ^ 65217111730824388219410 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 326085558654121941097051) ^ 1821707031587273413950 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 326085558654121941097051) ^ 26850 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_642901738938483904639033 : Nat.Prime 642901738938483904639033 := by
  apply lucas_primality 642901738938483904639033 (11 : ZMod 642901738938483904639033)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (13, 2), (43, 1), (97, 1), (32363, 1), (77557, 1), (2162911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (13, 2), (43, 1), (97, 1), (32363, 1), (77557, 1), (2162911, 1)] : List FactorBlock).map factorBlockValue).prod) = 642901738938483904639033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_13
      · exact prime_oneHundredFiftyThreeEU_43
      · exact prime_oneHundredFiftyThreeEU_97
      · exact prime_oneHundredFiftyThreeEU_32363
      · exact prime_oneHundredFiftyThreeEU_77557
      · exact prime_oneHundredFiftyThreeEU_2162911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 642901738938483904639033) ^ 321450869469241952319516 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 642901738938483904639033) ^ 214300579646161301546344 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 642901738938483904639033) ^ 91843105562640557805576 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 642901738938483904639033) ^ 49453979918344915741464 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 642901738938483904639033) ^ 14951203231127532666024 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 642901738938483904639033) ^ 6627852978747256748856 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 642901738938483904639033) ^ 19865331982155050664 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 642901738938483904639033) ^ 8289409581836377176 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (11 : ZMod 642901738938483904639033) ^ 297239109209063112 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_1494586651582541489648993 : Nat.Prime 1494586651582541489648993 := by
  apply lucas_primality 1494586651582541489648993 (3 : ZMod 1494586651582541489648993)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (46705832861954421551531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (46705832861954421551531, 1)] : List FactorBlock).map factorBlockValue).prod) = 1494586651582541489648993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_46705832861954421551531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1494586651582541489648993) ^ 747293325791270744824496 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1494586651582541489648993) ^ 32 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_2017295281122940529611883 : Nat.Prime 2017295281122940529611883 := by
  apply lucas_primality 2017295281122940529611883 (2 : ZMod 2017295281122940529611883)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (103, 1), (1171, 1), (491922215272605121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (103, 1), (1171, 1), (491922215272605121, 1)] : List FactorBlock).map factorBlockValue).prod) = 2017295281122940529611883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_17
      · exact prime_oneHundredFiftyThreeEU_103
      · exact prime_oneHundredFiftyThreeEU_1171
      · exact prime_oneHundredFiftyThreeEU_491922215272605121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2017295281122940529611883) ^ 1008647640561470264805941 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2017295281122940529611883) ^ 118664428301349442918346 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2017295281122940529611883) ^ 19585391078863500287494 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2017295281122940529611883) ^ 1722711597884663133742 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2017295281122940529611883) ^ 4100842 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_8486363277866846418448901 : Nat.Prime 8486363277866846418448901 := by
  apply lucas_primality 8486363277866846418448901 (10 : ZMod 8486363277866846418448901)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (652969, 1), (129965791298926081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (652969, 1), (129965791298926081, 1)] : List FactorBlock).map factorBlockValue).prod) = 8486363277866846418448901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_652969
      · exact prime_oneHundredFiftyThreeEU_129965791298926081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 8486363277866846418448901) ^ 4243181638933423209224450 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (10 : ZMod 8486363277866846418448901) ^ 1697272655573369283689780 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (10 : ZMod 8486363277866846418448901) ^ 12996579129892608100 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (10 : ZMod 8486363277866846418448901) ^ 65296900 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_13898335249153425386802791 : Nat.Prime 13898335249153425386802791 := by
  apply lucas_primality 13898335249153425386802791 (7 : ZMod 13898335249153425386802791)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (157, 1), (347, 1), (2689, 1), (64577, 1), (146914610617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (157, 1), (347, 1), (2689, 1), (64577, 1), (146914610617, 1)] : List FactorBlock).map factorBlockValue).prod) = 13898335249153425386802791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_157
      · exact prime_oneHundredFiftyThreeEU_347
      · exact prime_oneHundredFiftyThreeEU_2689
      · exact prime_oneHundredFiftyThreeEU_64577
      · exact prime_oneHundredFiftyThreeEU_146914610617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 13898335249153425386802791) ^ 6949167624576712693401395 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 13898335249153425386802791) ^ 2779667049830685077360558 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 13898335249153425386802791) ^ 88524428338556849597470 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 13898335249153425386802791) ^ 40052839334736096215570 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 13898335249153425386802791) ^ 5168588787338573963110 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 13898335249153425386802791) ^ 215221135220797271270 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 13898335249153425386802791) ^ 94601450398870 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_28840375202125610875197437 : Nat.Prime 28840375202125610875197437 := by
  apply lucas_primality 28840375202125610875197437 (2 : ZMod 28840375202125610875197437)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (83, 1), (4801, 1), (18093855448115484773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (83, 1), (4801, 1), (18093855448115484773, 1)] : List FactorBlock).map factorBlockValue).prod) = 28840375202125610875197437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_83
      · exact prime_oneHundredFiftyThreeEU_4801
      · exact prime_oneHundredFiftyThreeEU_18093855448115484773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 28840375202125610875197437) ^ 14420187601062805437598718 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 28840375202125610875197437) ^ 347474400025609769580692 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 28840375202125610875197437) ^ 6007160008774340944636 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 28840375202125610875197437) ^ 1593932 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_81738288869286864622339957 : Nat.Prime 81738288869286864622339957 := by
  apply lucas_primality 81738288869286864622339957 (5 : ZMod 81738288869286864622339957)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5683, 1), (1198578932331615705061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5683, 1), (1198578932331615705061, 1)] : List FactorBlock).map factorBlockValue).prod) = 81738288869286864622339957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5683
      · exact prime_oneHundredFiftyThreeEU_1198578932331615705061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 81738288869286864622339957) ^ 40869144434643432311169978 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 81738288869286864622339957) ^ 27246096289762288207446652 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 81738288869286864622339957) ^ 14382947187979388460732 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 81738288869286864622339957) ^ 68196 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_237073175973436214166760583 : Nat.Prime 237073175973436214166760583 := by
  apply lucas_primality 237073175973436214166760583 (5 : ZMod 237073175973436214166760583)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (953, 1), (124382568716388360003547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (953, 1), (124382568716388360003547, 1)] : List FactorBlock).map factorBlockValue).prod) = 237073175973436214166760583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_953
      · exact prime_oneHundredFiftyThreeEU_124382568716388360003547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 237073175973436214166760583) ^ 118536587986718107083380291 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 237073175973436214166760583) ^ 248765137432776720007094 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 237073175973436214166760583) ^ 1906 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_238322573475272505150511627 : Nat.Prime 238322573475272505150511627 := by
  apply lucas_primality 238322573475272505150511627 (2 : ZMod 238322573475272505150511627)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (59, 1), (263, 1), (1129, 1), (4556173, 1), (18430972757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (59, 1), (263, 1), (1129, 1), (4556173, 1), (18430972757, 1)] : List FactorBlock).map factorBlockValue).prod) = 238322573475272505150511627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_59
      · exact prime_oneHundredFiftyThreeEU_263
      · exact prime_oneHundredFiftyThreeEU_1129
      · exact prime_oneHundredFiftyThreeEU_4556173
      · exact prime_oneHundredFiftyThreeEU_18430972757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 238322573475272505150511627) ^ 119161286737636252575255813 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 238322573475272505150511627) ^ 79440857825090835050170542 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 238322573475272505150511627) ^ 4039365652123262799161214 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 238322573475272505150511627) ^ 906169480894572262929702 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 238322573475272505150511627) ^ 211091739127787869929594 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 238322573475272505150511627) ^ 52307621654241949362 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 238322573475272505150511627) ^ 12930547758786018 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_264841629967396532077947767 : Nat.Prime 264841629967396532077947767 := by
  apply lucas_primality 264841629967396532077947767 (5 : ZMod 264841629967396532077947767)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (11, 1), (7504733, 1), (32736500018324309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (11, 1), (7504733, 1), (32736500018324309, 1)] : List FactorBlock).map factorBlockValue).prod) = 264841629967396532077947767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_11
      · exact prime_oneHundredFiftyThreeEU_7504733
      · exact prime_oneHundredFiftyThreeEU_32736500018324309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 264841629967396532077947767) ^ 132420814983698266038973883 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 264841629967396532077947767) ^ 37834518566770933153992538 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 264841629967396532077947767) ^ 24076511815217866552540706 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 264841629967396532077947767) ^ 35289947019753605102 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (5 : ZMod 264841629967396532077947767) ^ 8090102174 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_274070959496563380923088371 : Nat.Prime 274070959496563380923088371 := by
  apply lucas_primality 274070959496563380923088371 (2 : ZMod 274070959496563380923088371)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (61, 1), (307259593, 1), (76961608042651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (61, 1), (307259593, 1), (76961608042651, 1)] : List FactorBlock).map factorBlockValue).prod) = 274070959496563380923088371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_19
      · exact prime_oneHundredFiftyThreeEU_61
      · exact prime_oneHundredFiftyThreeEU_307259593
      · exact prime_oneHundredFiftyThreeEU_76961608042651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 274070959496563380923088371) ^ 137035479748281690461544185 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 274070959496563380923088371) ^ 54814191899312676184617674 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 274070959496563380923088371) ^ 14424787341924388469636230 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 274070959496563380923088371) ^ 4492966549123989851198170 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 274070959496563380923088371) ^ 891985037214325090 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 274070959496563380923088371) ^ 3561138682870 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_339374921703061597390691041 : Nat.Prime 339374921703061597390691041 := by
  apply lucas_primality 339374921703061597390691041 (7 : ZMod 339374921703061597390691041)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (41, 1), (1847, 1), (2169397, 1), (4303766710267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (41, 1), (1847, 1), (2169397, 1), (4303766710267, 1)] : List FactorBlock).map factorBlockValue).prod) = 339374921703061597390691041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_41
      · exact prime_oneHundredFiftyThreeEU_1847
      · exact prime_oneHundredFiftyThreeEU_2169397
      · exact prime_oneHundredFiftyThreeEU_4303766710267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 339374921703061597390691041) ^ 169687460851530798695345520 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 339374921703061597390691041) ^ 113124973901020532463563680 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 339374921703061597390691041) ^ 67874984340612319478138208 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 339374921703061597390691041) ^ 8277437114708819448553440 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 339374921703061597390691041) ^ 183743866650276988300320 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 339374921703061597390691041) ^ 156437444000826772320 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 339374921703061597390691041) ^ 78855324777120 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_347859294745638137325458317 : Nat.Prime 347859294745638137325458317 := by
  apply lucas_primality 347859294745638137325458317 (2 : ZMod 347859294745638137325458317)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (41, 2), (1847, 1), (2169397, 1), (4303766710267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (41, 2), (1847, 1), (2169397, 1), (4303766710267, 1)] : List FactorBlock).map factorBlockValue).prod) = 347859294745638137325458317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_41
      · exact prime_oneHundredFiftyThreeEU_1847
      · exact prime_oneHundredFiftyThreeEU_2169397
      · exact prime_oneHundredFiftyThreeEU_4303766710267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 347859294745638137325458317) ^ 173929647372819068662729158 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 347859294745638137325458317) ^ 115953098248546045775152772 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 347859294745638137325458317) ^ 8484373042576539934767276 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 347859294745638137325458317) ^ 188337463316533913007828 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 347859294745638137325458317) ^ 160348380100847441628 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 347859294745638137325458317) ^ 80826707896548 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_1706479559129545579332437027 : Nat.Prime 1706479559129545579332437027 := by
  apply lucas_primality 1706479559129545579332437027 (2 : ZMod 1706479559129545579332437027)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (599, 1), (67582939393, 1), (21076922361559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (599, 1), (67582939393, 1), (21076922361559, 1)] : List FactorBlock).map factorBlockValue).prod) = 1706479559129545579332437027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_599
      · exact prime_oneHundredFiftyThreeEU_67582939393
      · exact prime_oneHundredFiftyThreeEU_21076922361559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1706479559129545579332437027) ^ 853239779564772789666218513 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1706479559129545579332437027) ^ 2848880733104416659987374 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1706479559129545579332437027) ^ 25250152989147682 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1706479559129545579332437027) ^ 80964361392814 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_2032436328850919454036385673 : Nat.Prime 2032436328850919454036385673 := by
  apply lucas_primality 2032436328850919454036385673 (3 : ZMod 2032436328850919454036385673)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (19, 1), (20611, 1), (92677915656529465343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (19, 1), (20611, 1), (92677915656529465343, 1)] : List FactorBlock).map factorBlockValue).prod) = 2032436328850919454036385673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_19
      · exact prime_oneHundredFiftyThreeEU_20611
      · exact prime_oneHundredFiftyThreeEU_92677915656529465343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2032436328850919454036385673) ^ 1016218164425459727018192836 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2032436328850919454036385673) ^ 290348046978702779148055096 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2032436328850919454036385673) ^ 106970333097416813370336088 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2032436328850919454036385673) ^ 98609302258547351124952 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2032436328850919454036385673) ^ 21930104 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_2205936991069900383039491767 : Nat.Prime 2205936991069900383039491767 := by
  apply lucas_primality 2205936991069900383039491767 (3 : ZMod 2205936991069900383039491767)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23509, 1), (114221628761, 1), (136917622189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23509, 1), (114221628761, 1), (136917622189, 1)] : List FactorBlock).map factorBlockValue).prod) = 2205936991069900383039491767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_23509
      · exact prime_oneHundredFiftyThreeEU_114221628761
      · exact prime_oneHundredFiftyThreeEU_136917622189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2205936991069900383039491767) ^ 1102968495534950191519745883 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2205936991069900383039491767) ^ 735312330356633461013163922 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2205936991069900383039491767) ^ 93833722875064885066974 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2205936991069900383039491767) ^ 19312778280247206 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2205936991069900383039491767) ^ 16111417623254094 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_2289706750224453562142257277 : Nat.Prime 2289706750224453562142257277 := by
  apply lucas_primality 2289706750224453562142257277 (2 : ZMod 2289706750224453562142257277)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (383, 1), (1494586651582541489648993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (383, 1), (1494586651582541489648993, 1)] : List FactorBlock).map factorBlockValue).prod) = 2289706750224453562142257277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_383
      · exact prime_oneHundredFiftyThreeEU_1494586651582541489648993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2289706750224453562142257277) ^ 1144853375112226781071128638 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2289706750224453562142257277) ^ 5978346606330165958595972 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2289706750224453562142257277) ^ 1532 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_4760179822835048194979955917 : Nat.Prime 4760179822835048194979955917 := by
  apply lucas_primality 4760179822835048194979955917 (2 : ZMod 4760179822835048194979955917)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (89, 1), (20611, 1), (92677915656529465343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (89, 1), (20611, 1), (92677915656529465343, 1)] : List FactorBlock).map factorBlockValue).prod) = 4760179822835048194979955917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_89
      · exact prime_oneHundredFiftyThreeEU_20611
      · exact prime_oneHundredFiftyThreeEU_92677915656529465343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4760179822835048194979955917) ^ 2380089911417524097489977958 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4760179822835048194979955917) ^ 680025688976435456425707988 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4760179822835048194979955917) ^ 53485166548708406685168044 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4760179822835048194979955917) ^ 230953365816071427634756 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4760179822835048194979955917) ^ 51362612 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_8222128784896901427692651129 : Nat.Prime 8222128784896901427692651129 := by
  apply lucas_primality 8222128784896901427692651129 (3 : ZMod 8222128784896901427692651129)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3660700717, 1), (280756657691039723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3660700717, 1), (280756657691039723, 1)] : List FactorBlock).map factorBlockValue).prod) = 8222128784896901427692651129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3660700717
      · exact prime_oneHundredFiftyThreeEU_280756657691039723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 8222128784896901427692651129) ^ 4111064392448450713846325564 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 8222128784896901427692651129) ^ 2246053261528317784 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (3 : ZMod 8222128784896901427692651129) ^ 29285605736 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_60295611089243943803079441611 : Nat.Prime 60295611089243943803079441611 := by
  apply lucas_primality 60295611089243943803079441611 (2 : ZMod 60295611089243943803079441611)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7541, 1), (252836652197, 1), (3162399473593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7541, 1), (252836652197, 1), (3162399473593, 1)] : List FactorBlock).map factorBlockValue).prod) = 60295611089243943803079441611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_5
      · exact prime_oneHundredFiftyThreeEU_7541
      · exact prime_oneHundredFiftyThreeEU_252836652197
      · exact prime_oneHundredFiftyThreeEU_3162399473593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 60295611089243943803079441611) ^ 30147805544621971901539720805 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 60295611089243943803079441611) ^ 12059122217848788760615888322 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 60295611089243943803079441611) ^ 7995704958128092269338210 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 60295611089243943803079441611) ^ 238476544303648130 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 60295611089243943803079441611) ^ 19066411942175770 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_180886833267731831409238324813 : Nat.Prime 180886833267731831409238324813 := by
  apply lucas_primality 180886833267731831409238324813 (2 : ZMod 180886833267731831409238324813)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (41, 1), (23509, 1), (114221628761, 1), (136917622189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (41, 1), (23509, 1), (114221628761, 1), (136917622189, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_3
      · exact prime_oneHundredFiftyThreeEU_41
      · exact prime_oneHundredFiftyThreeEU_23509
      · exact prime_oneHundredFiftyThreeEU_114221628761
      · exact prime_oneHundredFiftyThreeEU_136917622189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 180886833267731831409238324813) ^ 90443416633865915704619162406 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 180886833267731831409238324813) ^ 60295611089243943803079441604 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 180886833267731831409238324813) ^ 4411873982139800766078983532 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 180886833267731831409238324813) ^ 7694365275755320575491868 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 180886833267731831409238324813) ^ 1583647818980270892 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (2 : ZMod 180886833267731831409238324813) ^ 1321136245106835708 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyThreeEU_180886833267731831409238324823 : Nat.Prime 180886833267731831409238324823 := by
  apply lucas_primality 180886833267731831409238324823 (7 : ZMod 180886833267731831409238324823)
  · rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (39623, 1), (326085558654121941097051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (39623, 1), (326085558654121941097051, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyThreeEU_2
      · exact prime_oneHundredFiftyThreeEU_7
      · exact prime_oneHundredFiftyThreeEU_39623
      · exact prime_oneHundredFiftyThreeEU_326085558654121941097051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 180886833267731831409238324823) ^ 90443416633865915704619162411 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 180886833267731831409238324823) ^ 25840976181104547344176903546 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 180886833267731831409238324823) ^ 4565197821157707175358714 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide
    · change (7 : ZMod 180886833267731831409238324823) ^ 554722 ≠ 1
      rw [← oneHundredFiftyThreeEUFastPow_eq_pow]
      decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324800 : Nat.totient 180886833267731831409238324800 = 45398783408065799221592064000 := by
  rw [← show ((([(2, 6), (3, 2), (5, 2), (17, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324800 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_3, prime_oneHundredFiftyThreeEU_5, prime_oneHundredFiftyThreeEU_17, prime_oneHundredFiftyThreeEU_171401, prime_oneHundredFiftyThreeEU_714027719, prime_oneHundredFiftyThreeEU_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324801 : Nat.totient 180886833267731831409238324801 = 136894791267634594625674518528 := by
  rw [← show ((([(7, 1), (13, 1), (23, 1), (72617, 1), (3866459153, 1), (307812319757, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324801 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_7, prime_oneHundredFiftyThreeEU_13, prime_oneHundredFiftyThreeEU_23, prime_oneHundredFiftyThreeEU_72617, prime_oneHundredFiftyThreeEU_3866459153, prime_oneHundredFiftyThreeEU_307812319757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324802 : Nat.totient 180886833267731831409238324802 = 90354326038717514802805687680 := by
  rw [← show ((([(2, 1), (1429, 1), (4027, 1), (26927, 1), (583680428788739561, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324802 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_1429, prime_oneHundredFiftyThreeEU_4027, prime_oneHundredFiftyThreeEU_26927, prime_oneHundredFiftyThreeEU_583680428788739561]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324803 : Nat.totient 180886833267731831409238324803 = 120453717931389814495945725216 := by
  rw [← show ((([(3, 1), (877, 1), (41812652839, 1), (1644289884531667, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324803 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_3, prime_oneHundredFiftyThreeEU_877, prime_oneHundredFiftyThreeEU_41812652839, prime_oneHundredFiftyThreeEU_1644289884531667]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324804 : Nat.totient 180886833267731831409238324804 = 89065407741106812451162731264 := by
  rw [← show ((([(2, 2), (79, 1), (383, 1), (1494586651582541489648993, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324804 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_79, prime_oneHundredFiftyThreeEU_383, prime_oneHundredFiftyThreeEU_1494586651582541489648993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324805 : Nat.totient 180886833267731831409238324805 = 127174510981460387421548582400 := by
  rw [← show ((([(5, 1), (11, 1), (31, 1), (937, 1), (113225170033351484527733, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324805 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_5, prime_oneHundredFiftyThreeEU_11, prime_oneHundredFiftyThreeEU_31, prime_oneHundredFiftyThreeEU_937, prime_oneHundredFiftyThreeEU_113225170033351484527733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324806 : Nat.totient 180886833267731831409238324806 = 60248690888618104967826864000 := by
  rw [← show ((([(2, 1), (3, 1), (2131, 1), (6421, 1), (9511, 1), (20747, 1), (11165755073003, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324806 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_3, prime_oneHundredFiftyThreeEU_2131, prime_oneHundredFiftyThreeEU_6421, prime_oneHundredFiftyThreeEU_9511, prime_oneHundredFiftyThreeEU_20747, prime_oneHundredFiftyThreeEU_11165755073003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324807 : Nat.totient 180886833267731831409238324807 = 178682845641875551821496458240 := by
  rw [← show ((([(107, 1), (349, 1), (8603960009, 1), (562988298100561, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324807 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_107, prime_oneHundredFiftyThreeEU_349, prime_oneHundredFiftyThreeEU_8603960009, prime_oneHundredFiftyThreeEU_562988298100561]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324808 : Nat.totient 180886833267731831409238324808 = 72614051453347643823038737920 := by
  rw [← show ((([(2, 3), (7, 1), (19, 1), (89, 1), (20611, 1), (92677915656529465343, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324808 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_7, prime_oneHundredFiftyThreeEU_19, prime_oneHundredFiftyThreeEU_89, prime_oneHundredFiftyThreeEU_20611, prime_oneHundredFiftyThreeEU_92677915656529465343]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324809 : Nat.totient 180886833267731831409238324809 = 118315913613094389426059629440 := by
  rw [← show ((([(3, 3), (53, 1), (47582281, 1), (2656574897467719719, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324809 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_3, prime_oneHundredFiftyThreeEU_53, prime_oneHundredFiftyThreeEU_47582281, prime_oneHundredFiftyThreeEU_2656574897467719719]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324810 : Nat.totient 180886833267731831409238324810 = 69654275296475154343251379200 := by
  rw [← show ((([(2, 1), (5, 1), (47, 1), (61, 1), (778091, 1), (8108655896759637073, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324810 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_5, prime_oneHundredFiftyThreeEU_47, prime_oneHundredFiftyThreeEU_61, prime_oneHundredFiftyThreeEU_778091, prime_oneHundredFiftyThreeEU_8108655896759637073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324811 : Nat.totient 180886833267731831409238324811 = 180881307872474584998306241152 := by
  rw [← show ((([(64063, 1), (66949, 1), (42175048333700274353, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324811 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_64063, prime_oneHundredFiftyThreeEU_66949, prime_oneHundredFiftyThreeEU_42175048333700274353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324812 : Nat.totient 180886833267731831409238324812 = 58822484194976070108975206400 := by
  rw [← show ((([(2, 2), (3, 1), (41, 1), (23509, 1), (114221628761, 1), (136917622189, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324812 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_3, prime_oneHundredFiftyThreeEU_41, prime_oneHundredFiftyThreeEU_23509, prime_oneHundredFiftyThreeEU_114221628761, prime_oneHundredFiftyThreeEU_136917622189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324813 : Nat.totient 180886833267731831409238324813 = 180886833267731831409238324812 := by
  rw [← show ((([(180886833267731831409238324813, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324813 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_180886833267731831409238324813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324814 : Nat.totient 180886833267731831409238324814 = 81229846120555580122892181120 := by
  rw [← show ((([(2, 1), (13, 1), (37, 1), (21201849661, 1), (8868662603515027, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324814 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_13, prime_oneHundredFiftyThreeEU_37, prime_oneHundredFiftyThreeEU_21201849661, prime_oneHundredFiftyThreeEU_8868662603515027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324815 : Nat.totient 180886833267731831409238324815 = 79839705718171291104767251200 := by
  rw [← show ((([(3, 1), (5, 1), (7, 2), (29, 1), (8486363277866846418448901, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324815 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_3, prime_oneHundredFiftyThreeEU_5, prime_oneHundredFiftyThreeEU_7, prime_oneHundredFiftyThreeEU_29, prime_oneHundredFiftyThreeEU_8486363277866846418448901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324816 : Nat.totient 180886833267731831409238324816 = 82221287826508481368787276160 := by
  rw [← show ((([(2, 4), (11, 1), (3660700717, 1), (280756657691039723, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324816 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_11, prime_oneHundredFiftyThreeEU_3660700717, prime_oneHundredFiftyThreeEU_280756657691039723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324817 : Nat.totient 180886833267731831409238324817 = 165891224517218538324360634368 := by
  rw [← show ((([(17, 2), (73, 1), (83, 1), (906208483, 1), (113993486613649, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324817 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_17, prime_oneHundredFiftyThreeEU_73, prime_oneHundredFiftyThreeEU_83, prime_oneHundredFiftyThreeEU_906208483, prime_oneHundredFiftyThreeEU_113993486613649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324818 : Nat.totient 180886833267731831409238324818 = 60294336577829340345868308768 := by
  rw [← show ((([(2, 1), (3, 2), (47317, 1), (273126599, 1), (777594629002747, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324818 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_3, prime_oneHundredFiftyThreeEU_47317, prime_oneHundredFiftyThreeEU_273126599, prime_oneHundredFiftyThreeEU_777594629002747]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324819 : Nat.totient 180886833267731831409238324819 = 180846247988409211281653562240 := by
  rw [← show ((([(4457, 1), (458839891, 1), (88451082786507737, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324819 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_4457, prime_oneHundredFiftyThreeEU_458839891, prime_oneHundredFiftyThreeEU_88451082786507737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324820 : Nat.totient 180886833267731831409238324820 = 71583206216368063366184914944 := by
  rw [← show ((([(2, 2), (5, 1), (97, 1), (2797, 1), (33335944120492101516949, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324820 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_5, prime_oneHundredFiftyThreeEU_97, prime_oneHundredFiftyThreeEU_2797, prime_oneHundredFiftyThreeEU_33335944120492101516949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324821 : Nat.totient 180886833267731831409238324821 = 119917525763135253908643009408 := by
  rw [← show ((([(3, 1), (179, 1), (49213049, 1), (6844668155500488517, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324821 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_3, prime_oneHundredFiftyThreeEU_179, prime_oneHundredFiftyThreeEU_49213049, prime_oneHundredFiftyThreeEU_6844668155500488517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324822 : Nat.totient 180886833267731831409238324822 = 77520972029961717300883890600 := by
  rw [← show ((([(2, 1), (7, 1), (39623, 1), (326085558654121941097051, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324822 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_7, prime_oneHundredFiftyThreeEU_39623, prime_oneHundredFiftyThreeEU_326085558654121941097051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324823 : Nat.totient 180886833267731831409238324823 = 180886833267731831409238324822 := by
  rw [← show ((([(180886833267731831409238324823, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324823 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_180886833267731831409238324823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324824 : Nat.totient 180886833267731831409238324824 = 57506339315838547824006163968 := by
  rw [← show ((([(2, 3), (3, 1), (23, 2), (419, 1), (1913, 1), (17775058921576688827, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324824 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_3, prime_oneHundredFiftyThreeEU_23, prime_oneHundredFiftyThreeEU_419, prime_oneHundredFiftyThreeEU_1913, prime_oneHundredFiftyThreeEU_17775058921576688827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324825 : Nat.totient 180886833267731831409238324825 = 144677641335905773626168348480 := by
  rw [← show ((([(5, 2), (4547, 1), (8923633783, 1), (178320081482093, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324825 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_5, prime_oneHundredFiftyThreeEU_4547, prime_oneHundredFiftyThreeEU_8923633783, prime_oneHundredFiftyThreeEU_178320081482093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324826 : Nat.totient 180886833267731831409238324826 = 88339410874580743674286625520 := by
  rw [← show ((([(2, 1), (43, 1), (131783, 1), (614836631, 1), (25959084996967, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324826 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_43, prime_oneHundredFiftyThreeEU_131783, prime_oneHundredFiftyThreeEU_614836631, prime_oneHundredFiftyThreeEU_25959084996967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324827 : Nat.totient 180886833267731831409238324827 = 95869267863466925885952153600 := by
  rw [← show ((([(3, 2), (11, 1), (13, 1), (19, 1), (1094963, 1), (212514941, 1), (31789660873, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324827 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_3, prime_oneHundredFiftyThreeEU_11, prime_oneHundredFiftyThreeEU_13, prime_oneHundredFiftyThreeEU_19, prime_oneHundredFiftyThreeEU_1094963, prime_oneHundredFiftyThreeEU_212514941, prime_oneHundredFiftyThreeEU_31789660873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324828 : Nat.totient 180886833267731831409238324828 = 88936441984908208360214138880 := by
  rw [← show ((([(2, 2), (67, 1), (577, 1), (33487, 1), (10097959, 1), (3459286272181, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324828 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_67, prime_oneHundredFiftyThreeEU_577, prime_oneHundredFiftyThreeEU_33487, prime_oneHundredFiftyThreeEU_10097959, prime_oneHundredFiftyThreeEU_3459286272181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324829 : Nat.totient 180886833267731831409238324829 = 153623418030786666780060857136 := by
  rw [← show ((([(7, 1), (109, 1), (237073175973436214166760583, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324829 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_7, prime_oneHundredFiftyThreeEU_109, prime_oneHundredFiftyThreeEU_237073175973436214166760583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324830 : Nat.totient 180886833267731831409238324830 = 48230092307222645525540490240 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (7541, 1), (252836652197, 1), (3162399473593, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324830 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_3, prime_oneHundredFiftyThreeEU_5, prime_oneHundredFiftyThreeEU_7541, prime_oneHundredFiftyThreeEU_252836652197, prime_oneHundredFiftyThreeEU_3162399473593]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324831 : Nat.totient 180886833267731831409238324831 = 180886821940784259724004208000 := by
  rw [← show ((([(15969601, 1), (11326947571685218147231, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324831 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_15969601, prime_oneHundredFiftyThreeEU_11326947571685218147231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324832 : Nat.totient 180886833267731831409238324832 = 90383079923266289022452545152 := by
  rw [← show ((([(2, 5), (1499, 1), (103221763, 1), (36532893612773123, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324832 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_1499, prime_oneHundredFiftyThreeEU_103221763, prime_oneHundredFiftyThreeEU_36532893612773123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324833 : Nat.totient 180886833267731831409238324833 = 120591222178487887606158883220 := by
  rw [← show ((([(3, 1), (60295611089243943803079441611, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324833 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_3, prime_oneHundredFiftyThreeEU_60295611089243943803079441611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324834 : Nat.totient 180886833267731831409238324834 = 85123215655379912631475427392 := by
  rw [← show ((([(2, 1), (17, 1), (3662228970263, 1), (1452722104942727, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324834 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_17, prime_oneHundredFiftyThreeEU_3662228970263, prime_oneHundredFiftyThreeEU_1452722104942727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324835 : Nat.totient 180886833267731831409238324835 = 144709455359712134642142548800 := by
  rw [← show ((([(5, 1), (12857951, 1), (2813618332621299169817, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324835 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_5, prime_oneHundredFiftyThreeEU_12857951, prime_oneHundredFiftyThreeEU_2813618332621299169817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324836 : Nat.totient 180886833267731831409238324836 = 49814974491124200732728640000 := by
  rw [← show ((([(2, 2), (3, 3), (7, 1), (31, 1), (251, 1), (89597, 1), (343207110292651133, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324836 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_3, prime_oneHundredFiftyThreeEU_7, prime_oneHundredFiftyThreeEU_31, prime_oneHundredFiftyThreeEU_251, prime_oneHundredFiftyThreeEU_89597, prime_oneHundredFiftyThreeEU_343207110292651133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324837 : Nat.totient 180886833267731831409238324837 = 180886565979020883696382756620 := by
  rw [← show ((([(676747, 1), (267288710947712854891471, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324837 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_676747, prime_oneHundredFiftyThreeEU_267288710947712854891471]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324838 : Nat.totient 180886833267731831409238324838 = 82221287848969014276926511280 := by
  rw [← show ((([(2, 1), (11, 1), (8222128784896901427692651129, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324838 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_11, prime_oneHundredFiftyThreeEU_8222128784896901427692651129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324839 : Nat.totient 180886833267731831409238324839 = 119381582807287017446440848000 := by
  rw [← show ((([(3, 1), (101, 1), (7621, 1), (78334371920792006198453, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324839 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_3, prime_oneHundredFiftyThreeEU_101, prime_oneHundredFiftyThreeEU_7621, prime_oneHundredFiftyThreeEU_78334371920792006198453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324840 : Nat.totient 180886833267731831409238324840 = 66788984591162522366487996672 := by
  rw [← show ((([(2, 3), (5, 1), (13, 1), (347859294745638137325458317, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324840 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_5, prime_oneHundredFiftyThreeEU_13, prime_oneHundredFiftyThreeEU_347859294745638137325458317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324841 : Nat.totient 180886833267731831409238324841 = 180805094978862544544615982672 := by
  rw [← show ((([(2213, 1), (81738288869286864622339957, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324841 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2213, prime_oneHundredFiftyThreeEU_81738288869286864622339957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324842 : Nat.totient 180886833267731831409238324842 = 59220134806340447473306096896 := by
  rw [← show ((([(2, 1), (3, 1), (59, 1), (1109, 1), (862973, 1), (204603907, 1), (2609522327, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324842 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_3, prime_oneHundredFiftyThreeEU_59, prime_oneHundredFiftyThreeEU_1109, prime_oneHundredFiftyThreeEU_862973, prime_oneHundredFiftyThreeEU_204603907, prime_oneHundredFiftyThreeEU_2609522327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324843 : Nat.totient 180886833267731831409238324843 = 154117438780134661393306695840 := by
  rw [← show ((([(7, 1), (167, 1), (263713587191, 1), (586759241213917, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324843 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_7, prime_oneHundredFiftyThreeEU_167, prime_oneHundredFiftyThreeEU_263713587191, prime_oneHundredFiftyThreeEU_586759241213917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324844 : Nat.totient 180886833267731831409238324844 = 87211709593506964976180882624 := by
  rw [← show ((([(2, 2), (29, 1), (773, 1), (2017295281122940529611883, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324844 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_29, prime_oneHundredFiftyThreeEU_773, prime_oneHundredFiftyThreeEU_2017295281122940529611883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324845 : Nat.totient 180886833267731831409238324845 = 96472977742377528464105865216 := by
  rw [← show ((([(3, 2), (5, 1), (233717500609, 1), (17199000483384449, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324845 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_3, prime_oneHundredFiftyThreeEU_5, prime_oneHundredFiftyThreeEU_233717500609, prime_oneHundredFiftyThreeEU_17199000483384449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324846 : Nat.totient 180886833267731831409238324846 = 85683236811030867509639206488 := by
  rw [← show ((([(2, 1), (19, 1), (4760179822835048194979955917, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324846 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_19, prime_oneHundredFiftyThreeEU_4760179822835048194979955917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324847 : Nat.totient 180886833267731831409238324847 = 172451615175390525904026377280 := by
  rw [← show ((([(23, 1), (307, 1), (24697, 1), (1037281285622657708491, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324847 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_23, prime_oneHundredFiftyThreeEU_307, prime_oneHundredFiftyThreeEU_24697, prime_oneHundredFiftyThreeEU_1037281285622657708491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324848 : Nat.totient 180886833267731831409238324848 = 60295609899742066131695203264 := by
  rw [← show ((([(2, 4), (3, 1), (50689799, 1), (74343867354410825099, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324848 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_3, prime_oneHundredFiftyThreeEU_50689799, prime_oneHundredFiftyThreeEU_74343867354410825099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324849 : Nat.totient 180886833267731831409238324849 = 164072679218814375828420480000 := by
  rw [← show ((([(11, 1), (457, 1), (16301, 1), (1842596761, 1), (1197990901567, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324849 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_11, prime_oneHundredFiftyThreeEU_457, prime_oneHundredFiftyThreeEU_16301, prime_oneHundredFiftyThreeEU_1842596761, prime_oneHundredFiftyThreeEU_1197990901567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324850 : Nat.totient 180886833267731831409238324850 = 62018342834615481788304680640 := by
  rw [← show ((([(2, 1), (5, 2), (7, 1), (1760857498373, 1), (293504456834027, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324850 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_5, prime_oneHundredFiftyThreeEU_7, prime_oneHundredFiftyThreeEU_1760857498373, prime_oneHundredFiftyThreeEU_293504456834027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324851 : Nat.totient 180886833267731831409238324851 = 110426575569045467468034871296 := by
  rw [← show ((([(3, 1), (17, 1), (37, 1), (31177, 1), (3074685732733041494149, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324851 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_3, prime_oneHundredFiftyThreeEU_17, prime_oneHundredFiftyThreeEU_37, prime_oneHundredFiftyThreeEU_31177, prime_oneHundredFiftyThreeEU_3074685732733041494149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324852 : Nat.totient 180886833267731831409238324852 = 90438579895227823619054766720 := by
  rw [← show ((([(2, 2), (20599, 1), (202747, 1), (10827953699639743921, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324852 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_20599, prime_oneHundredFiftyThreeEU_202747, prime_oneHundredFiftyThreeEU_10827953699639743921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324853 : Nat.totient 180886833267731831409238324853 = 162899962417469566747531699200 := by
  rw [← show ((([(13, 1), (41, 1), (339374921703061597390691041, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324853 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_13, prime_oneHundredFiftyThreeEU_41, prime_oneHundredFiftyThreeEU_339374921703061597390691041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324854 : Nat.totient 180886833267731831409238324854 = 60179571213527255535278286336 := by
  rw [← show ((([(2, 1), (3, 2), (557, 1), (7727, 1), (2334900312219571567777, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324854 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_3, prime_oneHundredFiftyThreeEU_557, prime_oneHundredFiftyThreeEU_7727, prime_oneHundredFiftyThreeEU_2334900312219571567777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324855 : Nat.totient 180886833267731831409238324855 = 141787054753831197196458349440 := by
  rw [← show ((([(5, 1), (71, 1), (197, 1), (887, 1), (2916008306114041495759, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324855 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_5, prime_oneHundredFiftyThreeEU_71, prime_oneHundredFiftyThreeEU_197, prime_oneHundredFiftyThreeEU_887, prime_oneHundredFiftyThreeEU_2916008306114041495759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324856 : Nat.totient 180886833267731831409238324856 = 90442221632845881839901843840 := by
  rw [← show ((([(2, 3), (75709, 1), (236802743, 1), (1261196422592861, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324856 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_75709, prime_oneHundredFiftyThreeEU_236802743, prime_oneHundredFiftyThreeEU_1261196422592861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324857 : Nat.totient 180886833267731831409238324857 = 101164672701875875240377249984 := by
  rw [← show ((([(3, 1), (7, 1), (47, 1), (14190278693, 1), (12915132858396127, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324857 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_3, prime_oneHundredFiftyThreeEU_7, prime_oneHundredFiftyThreeEU_47, prime_oneHundredFiftyThreeEU_14190278693, prime_oneHundredFiftyThreeEU_12915132858396127]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324858 : Nat.totient 180886833267731831409238324858 = 90443416633863214017015913500 := by
  rw [← show ((([(2, 1), (33902056613179, 1), (2667785546635751, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324858 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_33902056613179, prime_oneHundredFiftyThreeEU_2667785546635751]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324859 : Nat.totient 180886833267731831409238324859 = 180886827653321378952187906704 := by
  rw [← show ((([(32218313, 1), (5614410452457018199843, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324859 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_32218313, prime_oneHundredFiftyThreeEU_5614410452457018199843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324860 : Nat.totient 180886833267731831409238324860 = 43851353519450140947694139200 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (11, 1), (274070959496563380923088371, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324860 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_3, prime_oneHundredFiftyThreeEU_5, prime_oneHundredFiftyThreeEU_11, prime_oneHundredFiftyThreeEU_274070959496563380923088371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324861 : Nat.totient 180886833267731831409238324861 = 180621991637764434877160376412 := by
  rw [← show ((([(683, 1), (264841629967396532077947767, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324861 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_683, prime_oneHundredFiftyThreeEU_264841629967396532077947767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324862 : Nat.totient 180886833267731831409238324862 = 88736937074736370125286725352 := by
  rw [← show ((([(2, 1), (53, 1), (1706479559129545579332437027, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324862 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_53, prime_oneHundredFiftyThreeEU_1706479559129545579332437027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324863 : Nat.totient 180886833267731831409238324863 = 120504196981275564243873131136 := by
  rw [← show ((([(3, 5), (1613, 1), (12899, 1), (41269, 1), (866934580455847, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324863 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_3, prime_oneHundredFiftyThreeEU_1613, prime_oneHundredFiftyThreeEU_12899, prime_oneHundredFiftyThreeEU_41269, prime_oneHundredFiftyThreeEU_866934580455847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324864 : Nat.totient 180886833267731831409238324864 = 77522928543313642032530707968 := by
  rw [← show ((([(2, 7), (7, 2), (28840375202125610875197437, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324864 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_7, prime_oneHundredFiftyThreeEU_28840375202125610875197437]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324865 : Nat.totient 180886833267731831409238324865 = 136092498759710341387572919680 := by
  rw [← show ((([(5, 1), (19, 1), (137, 1), (13898335249153425386802791, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324865 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_5, prime_oneHundredFiftyThreeEU_19, prime_oneHundredFiftyThreeEU_137, prime_oneHundredFiftyThreeEU_13898335249153425386802791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324866 : Nat.totient 180886833267731831409238324866 = 55657269885585135423026251584 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (256163, 1), (9053071540272876705469, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324866 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_3, prime_oneHundredFiftyThreeEU_13, prime_oneHundredFiftyThreeEU_256163, prime_oneHundredFiftyThreeEU_9053071540272876705469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324867 : Nat.totient 180886833267731831409238324867 = 173579675612633774167288176000 := by
  rw [← show ((([(31, 1), (131, 1), (1279, 1), (42472741, 1), (819960879280973, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324867 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_31, prime_oneHundredFiftyThreeEU_131, prime_oneHundredFiftyThreeEU_1279, prime_oneHundredFiftyThreeEU_42472741, prime_oneHundredFiftyThreeEU_819960879280973]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324868 : Nat.totient 180886833267731831409238324868 = 85075371052379441368734988800 := by
  rw [← show ((([(2, 2), (17, 1), (2411, 1), (7039, 1), (188911, 1), (829722028640579, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324868 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_17, prime_oneHundredFiftyThreeEU_2411, prime_oneHundredFiftyThreeEU_7039, prime_oneHundredFiftyThreeEU_188911, prime_oneHundredFiftyThreeEU_829722028640579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324869 : Nat.totient 180886833267731831409238324869 = 117105917749681632606151450560 := by
  rw [← show ((([(3, 1), (43, 1), (173, 1), (13026067, 1), (622239869447863171, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324869 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_3, prime_oneHundredFiftyThreeEU_43, prime_oneHundredFiftyThreeEU_173, prime_oneHundredFiftyThreeEU_13026067, prime_oneHundredFiftyThreeEU_622239869447863171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324870 : Nat.totient 180886833267731831409238324870 = 69175327605883691413157671680 := by
  rw [← show ((([(2, 1), (5, 1), (23, 1), (2063, 1), (1511628841, 1), (252193983968743, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324870 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_5, prime_oneHundredFiftyThreeEU_23, prime_oneHundredFiftyThreeEU_2063, prime_oneHundredFiftyThreeEU_1511628841, prime_oneHundredFiftyThreeEU_252193983968743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324871 : Nat.totient 180886833267731831409238324871 = 138456901953036355629346560000 := by
  rw [← show ((([(7, 1), (11, 1), (61, 1), (757, 1), (2207411, 1), (129867629, 1), (177462421, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324871 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_7, prime_oneHundredFiftyThreeEU_11, prime_oneHundredFiftyThreeEU_61, prime_oneHundredFiftyThreeEU_757, prime_oneHundredFiftyThreeEU_2207411, prime_oneHundredFiftyThreeEU_129867629, prime_oneHundredFiftyThreeEU_177462421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324872 : Nat.totient 180886833267731831409238324872 = 60295588895572145529368613120 := by
  rw [← show ((([(2, 3), (3, 2), (2717291, 1), (24250644403, 1), (38125454137, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324872 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_3, prime_oneHundredFiftyThreeEU_2717291, prime_oneHundredFiftyThreeEU_24250644403, prime_oneHundredFiftyThreeEU_38125454137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324873 : Nat.totient 180886833267731831409238324873 = 174187210587188585142226101504 := by
  rw [← show ((([(29, 1), (479, 1), (1787, 1), (43535477, 1), (167380778992597, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324873 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_29, prime_oneHundredFiftyThreeEU_479, prime_oneHundredFiftyThreeEU_1787, prime_oneHundredFiftyThreeEU_43535477, prime_oneHundredFiftyThreeEU_167380778992597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324874 : Nat.totient 180886833267731831409238324874 = 90443416243506040958793566400 := by
  rw [← show ((([(2, 1), (231692401, 1), (390359874745593903637, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324874 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_231692401, prime_oneHundredFiftyThreeEU_390359874745593903637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324875 : Nat.totient 180886833267731831409238324875 = 95611123827744950866387200000 := by
  rw [← show ((([(3, 1), (5, 3), (191, 1), (269, 1), (51429551, 1), (182548096187377, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324875 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_3, prime_oneHundredFiftyThreeEU_5, prime_oneHundredFiftyThreeEU_191, prime_oneHundredFiftyThreeEU_269, prime_oneHundredFiftyThreeEU_51429551, prime_oneHundredFiftyThreeEU_182548096187377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324876 : Nat.totient 180886833267731831409238324876 = 90196976479636047462476862720 := by
  rw [← show ((([(2, 2), (367, 1), (275924861, 1), (446570538165885137, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324876 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_367, prime_oneHundredFiftyThreeEU_275924861, prime_oneHundredFiftyThreeEU_446570538165885137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324877 : Nat.totient 180886833267731831409238324877 = 179372934274402833004303423488 := by
  rw [← show ((([(139, 1), (1097, 1), (3673, 1), (9420813119, 1), (34282794137, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324877 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_139, prime_oneHundredFiftyThreeEU_1097, prime_oneHundredFiftyThreeEU_3673, prime_oneHundredFiftyThreeEU_9420813119, prime_oneHundredFiftyThreeEU_34282794137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324878 : Nat.totient 180886833267731831409238324878 = 51650974229977978637769119232 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (1669, 1), (4194847, 1), (615155913718803313, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324878 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_3, prime_oneHundredFiftyThreeEU_7, prime_oneHundredFiftyThreeEU_1669, prime_oneHundredFiftyThreeEU_4194847, prime_oneHundredFiftyThreeEU_615155913718803313]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324879 : Nat.totient 180886833267731831409238324879 = 166972461477738903002189747136 := by
  rw [← show ((([(13, 1), (997499968979, 1), (13949245335884777, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324879 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_13, prime_oneHundredFiftyThreeEU_997499968979, prime_oneHundredFiftyThreeEU_13949245335884777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324880 : Nat.totient 180886833267731831409238324880 = 72334160451446701078746768384 := by
  rw [← show ((([(2, 4), (5, 1), (3517, 1), (642901738938483904639033, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324880 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_5, prime_oneHundredFiftyThreeEU_3517, prime_oneHundredFiftyThreeEU_642901738938483904639033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324881 : Nat.totient 180886833267731831409238324881 = 119823125219463195533108847456 := by
  rw [← show ((([(3, 2), (157, 1), (48437485823, 1), (2642915032645219, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324881 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_3, prime_oneHundredFiftyThreeEU_157, prime_oneHundredFiftyThreeEU_48437485823, prime_oneHundredFiftyThreeEU_2642915032645219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324882 : Nat.totient 180886833267731831409238324882 = 82220955962233986812478480640 := by
  rw [← show ((([(2, 1), (11, 1), (247739, 1), (33188673502746444555329, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324882 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_11, prime_oneHundredFiftyThreeEU_247739, prime_oneHundredFiftyThreeEU_33188673502746444555329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324883 : Nat.totient 180886833267731831409238324883 = 178597126517507377847096067528 := by
  rw [← show ((([(79, 1), (2289706750224453562142257277, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324883 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_79, prime_oneHundredFiftyThreeEU_2289706750224453562142257277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324884 : Nat.totient 180886833267731831409238324884 = 57119858918095355150707102176 := by
  rw [← show ((([(2, 2), (3, 1), (19, 1), (24847, 1), (31929943405877625702499, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324884 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_3, prime_oneHundredFiftyThreeEU_19, prime_oneHundredFiftyThreeEU_24847, prime_oneHundredFiftyThreeEU_31929943405877625702499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324885 : Nat.totient 180886833267731831409238324885 = 116734817823726398176703606784 := by
  rw [← show ((([(5, 1), (7, 1), (17, 1), (28403, 1), (79847, 1), (5816549, 1), (23046330287, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324885 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_5, prime_oneHundredFiftyThreeEU_7, prime_oneHundredFiftyThreeEU_17, prime_oneHundredFiftyThreeEU_28403, prime_oneHundredFiftyThreeEU_79847, prime_oneHundredFiftyThreeEU_5816549, prime_oneHundredFiftyThreeEU_23046330287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324886 : Nat.totient 180886833267731831409238324886 = 90443404878294256751979610944 := by
  rw [← show ((([(2, 1), (7711703, 1), (3292064693, 1), (3562528142617, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324886 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_7711703, prime_oneHundredFiftyThreeEU_3292064693, prime_oneHundredFiftyThreeEU_3562528142617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324887 : Nat.totient 180886833267731831409238324887 = 120591222178467737028447034752 := by
  rw [← show ((([(3, 1), (5988063355277, 1), (10069300792568977, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324887 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_3, prime_oneHundredFiftyThreeEU_5988063355277, prime_oneHundredFiftyThreeEU_10069300792568977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324888 : Nat.totient 180886833267731831409238324888 = 87795767857444973789880195072 := by
  rw [← show ((([(2, 3), (37, 1), (433, 1), (75436789, 1), (18708723398918219, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324888 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_37, prime_oneHundredFiftyThreeEU_433, prime_oneHundredFiftyThreeEU_75436789, prime_oneHundredFiftyThreeEU_18708723398918219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324889 : Nat.totient 180886833267731831409238324889 = 177942864425858065833507516672 := by
  rw [← show ((([(103, 1), (277, 1), (379, 1), (2543, 1), (1047979, 1), (6276995419813, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324889 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_103, prime_oneHundredFiftyThreeEU_277, prime_oneHundredFiftyThreeEU_379, prime_oneHundredFiftyThreeEU_2543, prime_oneHundredFiftyThreeEU_1047979, prime_oneHundredFiftyThreeEU_6276995419813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324890 : Nat.totient 180886833267731831409238324890 = 47546109414461580233334312960 := by
  rw [← show ((([(2, 1), (3, 3), (5, 1), (73, 1), (1607, 1), (140647657, 1), (40604292994541, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324890 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_3, prime_oneHundredFiftyThreeEU_5, prime_oneHundredFiftyThreeEU_73, prime_oneHundredFiftyThreeEU_1607, prime_oneHundredFiftyThreeEU_140647657, prime_oneHundredFiftyThreeEU_40604292994541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324891 : Nat.totient 180886833267731831409238324891 = 180886800279424814676415645800 := by
  rw [← show ((([(6724951, 1), (29700119, 1), (905648437261739, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324891 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_6724951, prime_oneHundredFiftyThreeEU_29700119, prime_oneHundredFiftyThreeEU_905648437261739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324892 : Nat.totient 180886833267731831409238324892 = 71206026871621575725231311872 := by
  rw [← show ((([(2, 2), (7, 1), (13, 1), (229, 1), (1733, 1), (1252193736375132378829, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324892 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_7, prime_oneHundredFiftyThreeEU_13, prime_oneHundredFiftyThreeEU_229, prime_oneHundredFiftyThreeEU_1733, prime_oneHundredFiftyThreeEU_1252193736375132378829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324893 : Nat.totient 180886833267731831409238324893 = 104861932329119902266225115440 := by
  rw [← show ((([(3, 1), (11, 1), (23, 1), (238322573475272505150511627, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324893 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_3, prime_oneHundredFiftyThreeEU_11, prime_oneHundredFiftyThreeEU_23, prime_oneHundredFiftyThreeEU_238322573475272505150511627]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324894 : Nat.totient 180886833267731831409238324894 = 88237479642796015321579670640 := by
  rw [← show ((([(2, 1), (41, 1), (2205936991069900383039491767, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324894 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_41, prime_oneHundredFiftyThreeEU_2205936991069900383039491767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324895 : Nat.totient 180886833267731831409238324895 = 142549616480628988077882310656 := by
  rw [← show ((([(5, 1), (67, 1), (34418159, 1), (44461057, 1), (352853743199, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324895 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_5, prime_oneHundredFiftyThreeEU_67, prime_oneHundredFiftyThreeEU_34418159, prime_oneHundredFiftyThreeEU_44461057, prime_oneHundredFiftyThreeEU_352853743199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324896 : Nat.totient 180886833267731831409238324896 = 60277081527237392915357773824 := by
  rw [← show ((([(2, 5), (3, 1), (5179, 1), (8753, 1), (41565487955259148373, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324896 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_3, prime_oneHundredFiftyThreeEU_5179, prime_oneHundredFiftyThreeEU_8753, prime_oneHundredFiftyThreeEU_41565487955259148373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324897 : Nat.totient 180886833267731831409238324897 = 178854396938880911955201939136 := by
  rw [← show ((([(89, 1), (2032436328850919454036385673, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324897 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_89, prime_oneHundredFiftyThreeEU_2032436328850919454036385673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324898 : Nat.totient 180886833267731831409238324898 = 87357891112322358312697536000 := by
  rw [← show ((([(2, 1), (31, 1), (521, 1), (10593489671, 1), (528613798600369, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324898 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_31, prime_oneHundredFiftyThreeEU_521, prime_oneHundredFiftyThreeEU_10593489671, prime_oneHundredFiftyThreeEU_528613798600369]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324899 : Nat.totient 180886833267731831409238324899 = 103358829569749135904902348800 := by
  rw [← show ((([(3, 2), (7, 1), (21377, 1), (450301, 1), (10003657, 1), (29816588057, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324899 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_3, prime_oneHundredFiftyThreeEU_7, prime_oneHundredFiftyThreeEU_21377, prime_oneHundredFiftyThreeEU_450301, prime_oneHundredFiftyThreeEU_10003657, prime_oneHundredFiftyThreeEU_29816588057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324900 : Nat.totient 180886833267731831409238324900 = 71482931252541810334743354240 := by
  rw [← show ((([(2, 2), (5, 2), (83, 1), (1226549, 1), (17768221546474086847, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324900 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_2, prime_oneHundredFiftyThreeEU_5, prime_oneHundredFiftyThreeEU_83, prime_oneHundredFiftyThreeEU_1226549, prime_oneHundredFiftyThreeEU_17768221546474086847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyThreeEU_180886833267731831409238324901 : Nat.totient 180886833267731831409238324901 = 176738338156333274537592192768 := by
  rw [← show ((([(59, 1), (239, 1), (523, 1), (10629859, 1), (2307426364027793, 1)] : List FactorBlock).map factorBlockValue).prod) = 180886833267731831409238324901 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyThreeEU_59, prime_oneHundredFiftyThreeEU_239, prime_oneHundredFiftyThreeEU_523, prime_oneHundredFiftyThreeEU_10629859, prime_oneHundredFiftyThreeEU_2307426364027793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredFiftyThreeEU : certifiedKill 1 180886833267731831409238324799 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredFiftyThreeEU_180886833267731831409238324800, phi_oneHundredFiftyThreeEU_180886833267731831409238324801, phi_oneHundredFiftyThreeEU_180886833267731831409238324802,
    phi_oneHundredFiftyThreeEU_180886833267731831409238324803, phi_oneHundredFiftyThreeEU_180886833267731831409238324804, phi_oneHundredFiftyThreeEU_180886833267731831409238324805,
    phi_oneHundredFiftyThreeEU_180886833267731831409238324806, phi_oneHundredFiftyThreeEU_180886833267731831409238324807, phi_oneHundredFiftyThreeEU_180886833267731831409238324808,
    phi_oneHundredFiftyThreeEU_180886833267731831409238324809, phi_oneHundredFiftyThreeEU_180886833267731831409238324810, phi_oneHundredFiftyThreeEU_180886833267731831409238324811,
    phi_oneHundredFiftyThreeEU_180886833267731831409238324812, phi_oneHundredFiftyThreeEU_180886833267731831409238324813, phi_oneHundredFiftyThreeEU_180886833267731831409238324814,
    phi_oneHundredFiftyThreeEU_180886833267731831409238324815, phi_oneHundredFiftyThreeEU_180886833267731831409238324816, phi_oneHundredFiftyThreeEU_180886833267731831409238324817,
    phi_oneHundredFiftyThreeEU_180886833267731831409238324818, phi_oneHundredFiftyThreeEU_180886833267731831409238324819, phi_oneHundredFiftyThreeEU_180886833267731831409238324820,
    phi_oneHundredFiftyThreeEU_180886833267731831409238324821, phi_oneHundredFiftyThreeEU_180886833267731831409238324822, phi_oneHundredFiftyThreeEU_180886833267731831409238324823,
    phi_oneHundredFiftyThreeEU_180886833267731831409238324824, phi_oneHundredFiftyThreeEU_180886833267731831409238324825, phi_oneHundredFiftyThreeEU_180886833267731831409238324826,
    phi_oneHundredFiftyThreeEU_180886833267731831409238324827, phi_oneHundredFiftyThreeEU_180886833267731831409238324828, phi_oneHundredFiftyThreeEU_180886833267731831409238324829,
    phi_oneHundredFiftyThreeEU_180886833267731831409238324830, phi_oneHundredFiftyThreeEU_180886833267731831409238324831, phi_oneHundredFiftyThreeEU_180886833267731831409238324832,
    phi_oneHundredFiftyThreeEU_180886833267731831409238324833, phi_oneHundredFiftyThreeEU_180886833267731831409238324834, phi_oneHundredFiftyThreeEU_180886833267731831409238324835,
    phi_oneHundredFiftyThreeEU_180886833267731831409238324836, phi_oneHundredFiftyThreeEU_180886833267731831409238324837, phi_oneHundredFiftyThreeEU_180886833267731831409238324838,
    phi_oneHundredFiftyThreeEU_180886833267731831409238324839, phi_oneHundredFiftyThreeEU_180886833267731831409238324840, phi_oneHundredFiftyThreeEU_180886833267731831409238324841,
    phi_oneHundredFiftyThreeEU_180886833267731831409238324842, phi_oneHundredFiftyThreeEU_180886833267731831409238324843, phi_oneHundredFiftyThreeEU_180886833267731831409238324844,
    phi_oneHundredFiftyThreeEU_180886833267731831409238324845, phi_oneHundredFiftyThreeEU_180886833267731831409238324846, phi_oneHundredFiftyThreeEU_180886833267731831409238324847,
    phi_oneHundredFiftyThreeEU_180886833267731831409238324848, phi_oneHundredFiftyThreeEU_180886833267731831409238324849, phi_oneHundredFiftyThreeEU_180886833267731831409238324850,
    phi_oneHundredFiftyThreeEU_180886833267731831409238324851, phi_oneHundredFiftyThreeEU_180886833267731831409238324852, phi_oneHundredFiftyThreeEU_180886833267731831409238324853,
    phi_oneHundredFiftyThreeEU_180886833267731831409238324854, phi_oneHundredFiftyThreeEU_180886833267731831409238324855, phi_oneHundredFiftyThreeEU_180886833267731831409238324856,
    phi_oneHundredFiftyThreeEU_180886833267731831409238324857, phi_oneHundredFiftyThreeEU_180886833267731831409238324858, phi_oneHundredFiftyThreeEU_180886833267731831409238324859,
    phi_oneHundredFiftyThreeEU_180886833267731831409238324860, phi_oneHundredFiftyThreeEU_180886833267731831409238324861, phi_oneHundredFiftyThreeEU_180886833267731831409238324862,
    phi_oneHundredFiftyThreeEU_180886833267731831409238324863, phi_oneHundredFiftyThreeEU_180886833267731831409238324864, phi_oneHundredFiftyThreeEU_180886833267731831409238324865,
    phi_oneHundredFiftyThreeEU_180886833267731831409238324866, phi_oneHundredFiftyThreeEU_180886833267731831409238324867, phi_oneHundredFiftyThreeEU_180886833267731831409238324868,
    phi_oneHundredFiftyThreeEU_180886833267731831409238324869, phi_oneHundredFiftyThreeEU_180886833267731831409238324870, phi_oneHundredFiftyThreeEU_180886833267731831409238324871,
    phi_oneHundredFiftyThreeEU_180886833267731831409238324872, phi_oneHundredFiftyThreeEU_180886833267731831409238324873, phi_oneHundredFiftyThreeEU_180886833267731831409238324874,
    phi_oneHundredFiftyThreeEU_180886833267731831409238324875, phi_oneHundredFiftyThreeEU_180886833267731831409238324876, phi_oneHundredFiftyThreeEU_180886833267731831409238324877,
    phi_oneHundredFiftyThreeEU_180886833267731831409238324878, phi_oneHundredFiftyThreeEU_180886833267731831409238324879, phi_oneHundredFiftyThreeEU_180886833267731831409238324880,
    phi_oneHundredFiftyThreeEU_180886833267731831409238324881, phi_oneHundredFiftyThreeEU_180886833267731831409238324882, phi_oneHundredFiftyThreeEU_180886833267731831409238324883,
    phi_oneHundredFiftyThreeEU_180886833267731831409238324884, phi_oneHundredFiftyThreeEU_180886833267731831409238324885, phi_oneHundredFiftyThreeEU_180886833267731831409238324886,
    phi_oneHundredFiftyThreeEU_180886833267731831409238324887, phi_oneHundredFiftyThreeEU_180886833267731831409238324888, phi_oneHundredFiftyThreeEU_180886833267731831409238324889,
    phi_oneHundredFiftyThreeEU_180886833267731831409238324890, phi_oneHundredFiftyThreeEU_180886833267731831409238324891, phi_oneHundredFiftyThreeEU_180886833267731831409238324892,
    phi_oneHundredFiftyThreeEU_180886833267731831409238324893, phi_oneHundredFiftyThreeEU_180886833267731831409238324894, phi_oneHundredFiftyThreeEU_180886833267731831409238324895,
    phi_oneHundredFiftyThreeEU_180886833267731831409238324896, phi_oneHundredFiftyThreeEU_180886833267731831409238324897, phi_oneHundredFiftyThreeEU_180886833267731831409238324898,
    phi_oneHundredFiftyThreeEU_180886833267731831409238324899, phi_oneHundredFiftyThreeEU_180886833267731831409238324900, phi_oneHundredFiftyThreeEU_180886833267731831409238324901]

end TotientTailPeriodKiller
end Erdos249257
