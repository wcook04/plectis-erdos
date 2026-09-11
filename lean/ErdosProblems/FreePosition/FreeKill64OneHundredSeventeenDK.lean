import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredSeventeenDKFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredSeventeenDKFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredSeventeenDKFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredSeventeenDKFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredSeventeenDKFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredSeventeenDKFastPow a n * oneHundredSeventeenDKFastPow a n * a else oneHundredSeventeenDKFastPow a n * oneHundredSeventeenDKFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredSeventeenDK_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredSeventeenDK_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredSeventeenDK_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredSeventeenDK_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredSeventeenDK_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredSeventeenDK_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredSeventeenDK_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredSeventeenDK_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredSeventeenDK_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredSeventeenDK_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredSeventeenDK_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredSeventeenDK_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredSeventeenDK_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredSeventeenDK_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredSeventeenDK_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredSeventeenDK_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredSeventeenDK_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredSeventeenDK_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredSeventeenDK_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredSeventeenDK_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredSeventeenDK_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredSeventeenDK_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredSeventeenDK_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredSeventeenDK_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredSeventeenDK_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredSeventeenDK_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredSeventeenDK_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredSeventeenDK_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredSeventeenDK_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredSeventeenDK_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredSeventeenDK_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredSeventeenDK_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredSeventeenDK_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredSeventeenDK_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredSeventeenDK_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredSeventeenDK_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredSeventeenDK_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredSeventeenDK_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredSeventeenDK_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredSeventeenDK_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredSeventeenDK_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredSeventeenDK_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredSeventeenDK_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredSeventeenDK_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredSeventeenDK_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredSeventeenDK_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredSeventeenDK_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredSeventeenDK_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredSeventeenDK_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredSeventeenDK_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredSeventeenDK_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredSeventeenDK_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredSeventeenDK_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredSeventeenDK_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredSeventeenDK_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredSeventeenDK_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredSeventeenDK_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredSeventeenDK_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredSeventeenDK_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredSeventeenDK_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredSeventeenDK_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredSeventeenDK_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredSeventeenDK_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredSeventeenDK_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredSeventeenDK_331 : Nat.Prime 331 := by norm_num

private theorem prime_oneHundredSeventeenDK_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredSeventeenDK_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredSeventeenDK_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredSeventeenDK_367 : Nat.Prime 367 := by norm_num

private theorem prime_oneHundredSeventeenDK_379 : Nat.Prime 379 := by norm_num

private theorem prime_oneHundredSeventeenDK_389 : Nat.Prime 389 := by norm_num

private theorem prime_oneHundredSeventeenDK_401 : Nat.Prime 401 := by norm_num

private theorem prime_oneHundredSeventeenDK_419 : Nat.Prime 419 := by norm_num

private theorem prime_oneHundredSeventeenDK_421 : Nat.Prime 421 := by norm_num

private theorem prime_oneHundredSeventeenDK_431 : Nat.Prime 431 := by norm_num

private theorem prime_oneHundredSeventeenDK_433 : Nat.Prime 433 := by norm_num

private theorem prime_oneHundredSeventeenDK_439 : Nat.Prime 439 := by norm_num

private theorem prime_oneHundredSeventeenDK_443 : Nat.Prime 443 := by norm_num

private theorem prime_oneHundredSeventeenDK_449 : Nat.Prime 449 := by norm_num

private theorem prime_oneHundredSeventeenDK_463 : Nat.Prime 463 := by norm_num

private theorem prime_oneHundredSeventeenDK_467 : Nat.Prime 467 := by norm_num

private theorem prime_oneHundredSeventeenDK_479 : Nat.Prime 479 := by norm_num

private theorem prime_oneHundredSeventeenDK_491 : Nat.Prime 491 := by norm_num

private theorem prime_oneHundredSeventeenDK_503 : Nat.Prime 503 := by norm_num

private theorem prime_oneHundredSeventeenDK_521 : Nat.Prime 521 := by norm_num

private theorem prime_oneHundredSeventeenDK_557 : Nat.Prime 557 := by norm_num

private theorem prime_oneHundredSeventeenDK_563 : Nat.Prime 563 := by norm_num

private theorem prime_oneHundredSeventeenDK_569 : Nat.Prime 569 := by norm_num

private theorem prime_oneHundredSeventeenDK_607 : Nat.Prime 607 := by norm_num

private theorem prime_oneHundredSeventeenDK_613 : Nat.Prime 613 := by norm_num

private theorem prime_oneHundredSeventeenDK_619 : Nat.Prime 619 := by norm_num

private theorem prime_oneHundredSeventeenDK_631 : Nat.Prime 631 := by norm_num

private theorem prime_oneHundredSeventeenDK_647 : Nat.Prime 647 := by norm_num

private theorem prime_oneHundredSeventeenDK_653 : Nat.Prime 653 := by norm_num

private theorem prime_oneHundredSeventeenDK_659 : Nat.Prime 659 := by norm_num

private theorem prime_oneHundredSeventeenDK_661 : Nat.Prime 661 := by norm_num

private theorem prime_oneHundredSeventeenDK_683 : Nat.Prime 683 := by norm_num

private theorem prime_oneHundredSeventeenDK_691 : Nat.Prime 691 := by norm_num

private theorem prime_oneHundredSeventeenDK_701 : Nat.Prime 701 := by norm_num

private theorem prime_oneHundredSeventeenDK_727 : Nat.Prime 727 := by norm_num

private theorem prime_oneHundredSeventeenDK_733 : Nat.Prime 733 := by norm_num

private theorem prime_oneHundredSeventeenDK_739 : Nat.Prime 739 := by norm_num

private theorem prime_oneHundredSeventeenDK_773 : Nat.Prime 773 := by norm_num

private theorem prime_oneHundredSeventeenDK_797 : Nat.Prime 797 := by norm_num

private theorem prime_oneHundredSeventeenDK_827 : Nat.Prime 827 := by norm_num

private theorem prime_oneHundredSeventeenDK_853 : Nat.Prime 853 := by norm_num

private theorem prime_oneHundredSeventeenDK_857 : Nat.Prime 857 := by norm_num

private theorem prime_oneHundredSeventeenDK_911 : Nat.Prime 911 := by norm_num

private theorem prime_oneHundredSeventeenDK_937 : Nat.Prime 937 := by norm_num

private theorem prime_oneHundredSeventeenDK_947 : Nat.Prime 947 := by norm_num

private theorem prime_oneHundredSeventeenDK_967 : Nat.Prime 967 := by norm_num

private theorem prime_oneHundredSeventeenDK_971 : Nat.Prime 971 := by norm_num

private theorem prime_oneHundredSeventeenDK_977 : Nat.Prime 977 := by norm_num

private theorem prime_oneHundredSeventeenDK_1049 : Nat.Prime 1049 := by norm_num

private theorem prime_oneHundredSeventeenDK_1061 : Nat.Prime 1061 := by norm_num

private theorem prime_oneHundredSeventeenDK_1069 : Nat.Prime 1069 := by norm_num

private theorem prime_oneHundredSeventeenDK_1093 : Nat.Prime 1093 := by norm_num

private theorem prime_oneHundredSeventeenDK_1117 : Nat.Prime 1117 := by norm_num

private theorem prime_oneHundredSeventeenDK_1129 : Nat.Prime 1129 := by norm_num

private theorem prime_oneHundredSeventeenDK_1171 : Nat.Prime 1171 := by norm_num

private theorem prime_oneHundredSeventeenDK_1223 : Nat.Prime 1223 := by norm_num

private theorem prime_oneHundredSeventeenDK_1231 : Nat.Prime 1231 := by norm_num

private theorem prime_oneHundredSeventeenDK_1291 : Nat.Prime 1291 := by norm_num

private theorem prime_oneHundredSeventeenDK_1301 : Nat.Prime 1301 := by norm_num

private theorem prime_oneHundredSeventeenDK_1439 : Nat.Prime 1439 := by norm_num

private theorem prime_oneHundredSeventeenDK_1447 : Nat.Prime 1447 := by norm_num

private theorem prime_oneHundredSeventeenDK_1453 : Nat.Prime 1453 := by norm_num

private theorem prime_oneHundredSeventeenDK_1459 : Nat.Prime 1459 := by norm_num

private theorem prime_oneHundredSeventeenDK_1523 : Nat.Prime 1523 := by norm_num

private theorem prime_oneHundredSeventeenDK_1549 : Nat.Prime 1549 := by norm_num

private theorem prime_oneHundredSeventeenDK_1571 : Nat.Prime 1571 := by norm_num

private theorem prime_oneHundredSeventeenDK_1583 : Nat.Prime 1583 := by norm_num

private theorem prime_oneHundredSeventeenDK_1607 : Nat.Prime 1607 := by norm_num

private theorem prime_oneHundredSeventeenDK_1613 : Nat.Prime 1613 := by norm_num

private theorem prime_oneHundredSeventeenDK_1667 : Nat.Prime 1667 := by norm_num

private theorem prime_oneHundredSeventeenDK_1693 : Nat.Prime 1693 := by norm_num

private theorem prime_oneHundredSeventeenDK_1733 : Nat.Prime 1733 := by norm_num

private theorem prime_oneHundredSeventeenDK_1747 : Nat.Prime 1747 := by norm_num

private theorem prime_oneHundredSeventeenDK_1759 : Nat.Prime 1759 := by norm_num

private theorem prime_oneHundredSeventeenDK_1831 : Nat.Prime 1831 := by norm_num

private theorem prime_oneHundredSeventeenDK_2011 : Nat.Prime 2011 := by norm_num

private theorem prime_oneHundredSeventeenDK_2111 : Nat.Prime 2111 := by norm_num

private theorem prime_oneHundredSeventeenDK_2399 : Nat.Prime 2399 := by norm_num

private theorem prime_oneHundredSeventeenDK_2411 : Nat.Prime 2411 := by norm_num

private theorem prime_oneHundredSeventeenDK_2671 : Nat.Prime 2671 := by norm_num

private theorem prime_oneHundredSeventeenDK_2693 : Nat.Prime 2693 := by norm_num

private theorem prime_oneHundredSeventeenDK_2777 : Nat.Prime 2777 := by norm_num

private theorem prime_oneHundredSeventeenDK_2789 : Nat.Prime 2789 := by norm_num

private theorem prime_oneHundredSeventeenDK_2963 : Nat.Prime 2963 := by norm_num

private theorem prime_oneHundredSeventeenDK_3001 : Nat.Prime 3001 := by norm_num

private theorem prime_oneHundredSeventeenDK_3067 : Nat.Prime 3067 := by norm_num

private theorem prime_oneHundredSeventeenDK_3089 : Nat.Prime 3089 := by norm_num

private theorem prime_oneHundredSeventeenDK_3313 : Nat.Prime 3313 := by norm_num

private theorem prime_oneHundredSeventeenDK_3391 : Nat.Prime 3391 := by norm_num

private theorem prime_oneHundredSeventeenDK_3457 : Nat.Prime 3457 := by norm_num

private theorem prime_oneHundredSeventeenDK_3491 : Nat.Prime 3491 := by norm_num

private theorem prime_oneHundredSeventeenDK_4211 : Nat.Prime 4211 := by norm_num

private theorem prime_oneHundredSeventeenDK_4463 : Nat.Prime 4463 := by norm_num

private theorem prime_oneHundredSeventeenDK_4643 : Nat.Prime 4643 := by norm_num

private theorem prime_oneHundredSeventeenDK_4673 : Nat.Prime 4673 := by norm_num

private theorem prime_oneHundredSeventeenDK_4691 : Nat.Prime 4691 := by norm_num

private theorem prime_oneHundredSeventeenDK_4729 : Nat.Prime 4729 := by norm_num

private theorem prime_oneHundredSeventeenDK_4813 : Nat.Prime 4813 := by norm_num

private theorem prime_oneHundredSeventeenDK_4871 : Nat.Prime 4871 := by norm_num

private theorem prime_oneHundredSeventeenDK_5503 : Nat.Prime 5503 := by norm_num

private theorem prime_oneHundredSeventeenDK_5519 : Nat.Prime 5519 := by norm_num

private theorem prime_oneHundredSeventeenDK_5527 : Nat.Prime 5527 := by norm_num

private theorem prime_oneHundredSeventeenDK_5669 : Nat.Prime 5669 := by norm_num

private theorem prime_oneHundredSeventeenDK_5711 : Nat.Prime 5711 := by norm_num

private theorem prime_oneHundredSeventeenDK_5867 : Nat.Prime 5867 := by norm_num

private theorem prime_oneHundredSeventeenDK_6011 : Nat.Prime 6011 := by norm_num

private theorem prime_oneHundredSeventeenDK_6323 : Nat.Prime 6323 := by norm_num

private theorem prime_oneHundredSeventeenDK_6367 : Nat.Prime 6367 := by norm_num

private theorem prime_oneHundredSeventeenDK_6427 : Nat.Prime 6427 := by norm_num

private theorem prime_oneHundredSeventeenDK_6521 : Nat.Prime 6521 := by norm_num

private theorem prime_oneHundredSeventeenDK_6733 : Nat.Prime 6733 := by norm_num

private theorem prime_oneHundredSeventeenDK_6779 : Nat.Prime 6779 := by norm_num

private theorem prime_oneHundredSeventeenDK_6863 : Nat.Prime 6863 := by norm_num

private theorem prime_oneHundredSeventeenDK_6911 : Nat.Prime 6911 := by norm_num

private theorem prime_oneHundredSeventeenDK_7039 : Nat.Prime 7039 := by norm_num

private theorem prime_oneHundredSeventeenDK_7247 : Nat.Prime 7247 := by norm_num

private theorem prime_oneHundredSeventeenDK_7351 : Nat.Prime 7351 := by norm_num

private theorem prime_oneHundredSeventeenDK_7583 : Nat.Prime 7583 := by norm_num

private theorem prime_oneHundredSeventeenDK_7949 : Nat.Prime 7949 := by norm_num

private theorem prime_oneHundredSeventeenDK_8231 : Nat.Prime 8231 := by norm_num

private theorem prime_oneHundredSeventeenDK_8819 : Nat.Prime 8819 := by norm_num

private theorem prime_oneHundredSeventeenDK_9127 : Nat.Prime 9127 := by norm_num

private theorem prime_oneHundredSeventeenDK_9439 : Nat.Prime 9439 := by norm_num

private theorem prime_oneHundredSeventeenDK_9551 : Nat.Prime 9551 := by norm_num

private theorem prime_oneHundredSeventeenDK_9719 : Nat.Prime 9719 := by norm_num

private theorem prime_oneHundredSeventeenDK_9829 : Nat.Prime 9829 := by norm_num

private theorem prime_oneHundredSeventeenDK_10163 : Nat.Prime 10163 := by norm_num

private theorem prime_oneHundredSeventeenDK_10463 : Nat.Prime 10463 := by norm_num

private theorem prime_oneHundredSeventeenDK_10639 : Nat.Prime 10639 := by norm_num

private theorem prime_oneHundredSeventeenDK_10657 : Nat.Prime 10657 := by norm_num

private theorem prime_oneHundredSeventeenDK_11321 : Nat.Prime 11321 := by norm_num

private theorem prime_oneHundredSeventeenDK_11813 : Nat.Prime 11813 := by norm_num

private theorem prime_oneHundredSeventeenDK_12281 : Nat.Prime 12281 := by norm_num

private theorem prime_oneHundredSeventeenDK_13099 : Nat.Prime 13099 := by norm_num

private theorem prime_oneHundredSeventeenDK_13313 : Nat.Prime 13313 := by norm_num

private theorem prime_oneHundredSeventeenDK_13469 : Nat.Prime 13469 := by norm_num

private theorem prime_oneHundredSeventeenDK_13729 : Nat.Prime 13729 := by norm_num

private theorem prime_oneHundredSeventeenDK_14033 : Nat.Prime 14033 := by norm_num

private theorem prime_oneHundredSeventeenDK_14831 : Nat.Prime 14831 := by norm_num

private theorem prime_oneHundredSeventeenDK_14879 : Nat.Prime 14879 := by norm_num

private theorem prime_oneHundredSeventeenDK_16417 : Nat.Prime 16417 := by norm_num

private theorem prime_oneHundredSeventeenDK_16931 : Nat.Prime 16931 := by norm_num

private theorem prime_oneHundredSeventeenDK_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredSeventeenDK_17627 : Nat.Prime 17627 := by norm_num

private theorem prime_oneHundredSeventeenDK_17903 : Nat.Prime 17903 := by norm_num

private theorem prime_oneHundredSeventeenDK_18311 : Nat.Prime 18311 := by norm_num

private theorem prime_oneHundredSeventeenDK_18341 : Nat.Prime 18341 := by norm_num

private theorem prime_oneHundredSeventeenDK_19183 : Nat.Prime 19183 := by norm_num

private theorem prime_oneHundredSeventeenDK_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredSeventeenDK_21013 : Nat.Prime 21013 := by norm_num

private theorem prime_oneHundredSeventeenDK_21121 : Nat.Prime 21121 := by norm_num

private theorem prime_oneHundredSeventeenDK_21991 : Nat.Prime 21991 := by norm_num

private theorem prime_oneHundredSeventeenDK_23117 : Nat.Prime 23117 := by norm_num

private theorem prime_oneHundredSeventeenDK_23581 : Nat.Prime 23581 := by norm_num

private theorem prime_oneHundredSeventeenDK_23677 : Nat.Prime 23677 := by norm_num

private theorem prime_oneHundredSeventeenDK_23719 : Nat.Prime 23719 := by norm_num

private theorem prime_oneHundredSeventeenDK_25117 : Nat.Prime 25117 := by norm_num

private theorem prime_oneHundredSeventeenDK_25147 : Nat.Prime 25147 := by norm_num

private theorem prime_oneHundredSeventeenDK_26107 : Nat.Prime 26107 := by norm_num

private theorem prime_oneHundredSeventeenDK_28229 : Nat.Prime 28229 := by norm_num

private theorem prime_oneHundredSeventeenDK_28403 : Nat.Prime 28403 := by norm_num

private theorem prime_oneHundredSeventeenDK_28729 : Nat.Prime 28729 := by norm_num

private theorem prime_oneHundredSeventeenDK_29437 : Nat.Prime 29437 := by norm_num

private theorem prime_oneHundredSeventeenDK_30781 : Nat.Prime 30781 := by norm_num

private theorem prime_oneHundredSeventeenDK_31177 : Nat.Prime 31177 := by norm_num

private theorem prime_oneHundredSeventeenDK_31547 : Nat.Prime 31547 := by norm_num

private theorem prime_oneHundredSeventeenDK_31721 : Nat.Prime 31721 := by norm_num

private theorem prime_oneHundredSeventeenDK_34141 : Nat.Prime 34141 := by norm_num

private theorem prime_oneHundredSeventeenDK_36061 : Nat.Prime 36061 := by norm_num

private theorem prime_oneHundredSeventeenDK_36353 : Nat.Prime 36353 := by norm_num

private theorem prime_oneHundredSeventeenDK_36809 : Nat.Prime 36809 := by norm_num

private theorem prime_oneHundredSeventeenDK_37087 : Nat.Prime 37087 := by norm_num

private theorem prime_oneHundredSeventeenDK_39023 : Nat.Prime 39023 := by norm_num

private theorem prime_oneHundredSeventeenDK_39079 : Nat.Prime 39079 := by norm_num

private theorem prime_oneHundredSeventeenDK_40763 : Nat.Prime 40763 := by norm_num

private theorem prime_oneHundredSeventeenDK_42863 : Nat.Prime 42863 := by norm_num

private theorem prime_oneHundredSeventeenDK_43391 : Nat.Prime 43391 := by norm_num

private theorem prime_oneHundredSeventeenDK_47713 : Nat.Prime 47713 := by norm_num

private theorem prime_oneHundredSeventeenDK_48527 : Nat.Prime 48527 := by norm_num

private theorem prime_oneHundredSeventeenDK_50287 : Nat.Prime 50287 := by norm_num

private theorem prime_oneHundredSeventeenDK_51461 : Nat.Prime 51461 := by norm_num

private theorem prime_oneHundredSeventeenDK_53791 : Nat.Prime 53791 := by norm_num

private theorem prime_oneHundredSeventeenDK_53897 : Nat.Prime 53897 := by norm_num

private theorem prime_oneHundredSeventeenDK_54419 : Nat.Prime 54419 := by norm_num

private theorem prime_oneHundredSeventeenDK_55351 : Nat.Prime 55351 := by norm_num

private theorem prime_oneHundredSeventeenDK_55541 : Nat.Prime 55541 := by norm_num

private theorem prime_oneHundredSeventeenDK_60091 : Nat.Prime 60091 := by norm_num

private theorem prime_oneHundredSeventeenDK_64217 : Nat.Prime 64217 := by norm_num

private theorem prime_oneHundredSeventeenDK_66791 : Nat.Prime 66791 := by norm_num

private theorem prime_oneHundredSeventeenDK_68947 : Nat.Prime 68947 := by norm_num

private theorem prime_oneHundredSeventeenDK_71437 : Nat.Prime 71437 := by norm_num

private theorem prime_oneHundredSeventeenDK_72613 : Nat.Prime 72613 := by norm_num

private theorem prime_oneHundredSeventeenDK_74821 : Nat.Prime 74821 := by norm_num

private theorem prime_oneHundredSeventeenDK_76079 : Nat.Prime 76079 := by norm_num

private theorem prime_oneHundredSeventeenDK_78301 : Nat.Prime 78301 := by norm_num

private theorem prime_oneHundredSeventeenDK_79847 : Nat.Prime 79847 := by norm_num

private theorem prime_oneHundredSeventeenDK_80833 : Nat.Prime 80833 := by norm_num

private theorem prime_oneHundredSeventeenDK_81899 : Nat.Prime 81899 := by norm_num

private theorem prime_oneHundredSeventeenDK_82301 : Nat.Prime 82301 := by norm_num

private theorem prime_oneHundredSeventeenDK_83407 : Nat.Prime 83407 := by norm_num

private theorem prime_oneHundredSeventeenDK_85247 : Nat.Prime 85247 := by norm_num

private theorem prime_oneHundredSeventeenDK_87679 : Nat.Prime 87679 := by norm_num

private theorem prime_oneHundredSeventeenDK_91639 : Nat.Prime 91639 := by norm_num

private theorem prime_oneHundredSeventeenDK_96059 : Nat.Prime 96059 := by norm_num

private theorem prime_oneHundredSeventeenDK_97301 : Nat.Prime 97301 := by norm_num

private theorem prime_oneHundredSeventeenDK_97577 : Nat.Prime 97577 := by norm_num

private theorem prime_oneHundredSeventeenDK_100391 : Nat.Prime 100391 := by norm_num

private theorem prime_oneHundredSeventeenDK_105211 : Nat.Prime 105211 := by norm_num

private theorem prime_oneHundredSeventeenDK_105379 : Nat.Prime 105379 := by norm_num

private theorem prime_oneHundredSeventeenDK_106219 : Nat.Prime 106219 := by norm_num

private theorem prime_oneHundredSeventeenDK_106349 : Nat.Prime 106349 := by norm_num

private theorem prime_oneHundredSeventeenDK_106627 : Nat.Prime 106627 := by norm_num

private theorem prime_oneHundredSeventeenDK_119929 : Nat.Prime 119929 := by norm_num

private theorem prime_oneHundredSeventeenDK_120647 : Nat.Prime 120647 := by norm_num

private theorem prime_oneHundredSeventeenDK_121721 : Nat.Prime 121721 := by norm_num

private theorem prime_oneHundredSeventeenDK_125539 : Nat.Prime 125539 := by norm_num

private theorem prime_oneHundredSeventeenDK_135511 : Nat.Prime 135511 := by norm_num

private theorem prime_oneHundredSeventeenDK_139409 : Nat.Prime 139409 := by norm_num

private theorem prime_oneHundredSeventeenDK_140639 : Nat.Prime 140639 := by norm_num

private theorem prime_oneHundredSeventeenDK_160183 : Nat.Prime 160183 := by norm_num

private theorem prime_oneHundredSeventeenDK_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredSeventeenDK_174413 : Nat.Prime 174413 := by norm_num

private theorem prime_oneHundredSeventeenDK_177433 : Nat.Prime 177433 := by norm_num

private theorem prime_oneHundredSeventeenDK_185483 : Nat.Prime 185483 := by norm_num

private theorem prime_oneHundredSeventeenDK_188911 : Nat.Prime 188911 := by norm_num

private theorem prime_oneHundredSeventeenDK_192121 : Nat.Prime 192121 := by norm_num

private theorem prime_oneHundredSeventeenDK_196541 : Nat.Prime 196541 := by norm_num

private theorem prime_oneHundredSeventeenDK_198839 : Nat.Prime 198839 := by norm_num

private theorem prime_oneHundredSeventeenDK_204557 : Nat.Prime 204557 := by norm_num

private theorem prime_oneHundredSeventeenDK_204859 : Nat.Prime 204859 := by norm_num

private theorem prime_oneHundredSeventeenDK_207869 : Nat.Prime 207869 := by norm_num

private theorem prime_oneHundredSeventeenDK_212627 : Nat.Prime 212627 := by norm_num

private theorem prime_oneHundredSeventeenDK_220589 : Nat.Prime 220589 := by norm_num

private theorem prime_oneHundredSeventeenDK_221587 : Nat.Prime 221587 := by norm_num

private theorem prime_oneHundredSeventeenDK_226777 : Nat.Prime 226777 := by norm_num

private theorem prime_oneHundredSeventeenDK_233347 : Nat.Prime 233347 := by norm_num

private theorem prime_oneHundredSeventeenDK_238531 : Nat.Prime 238531 := by norm_num

private theorem prime_oneHundredSeventeenDK_260651 : Nat.Prime 260651 := by norm_num

private theorem prime_oneHundredSeventeenDK_266009 : Nat.Prime 266009 := by norm_num

private theorem prime_oneHundredSeventeenDK_271231 : Nat.Prime 271231 := by norm_num

private theorem prime_oneHundredSeventeenDK_275389 : Nat.Prime 275389 := by norm_num

private theorem prime_oneHundredSeventeenDK_284833 : Nat.Prime 284833 := by norm_num

private theorem prime_oneHundredSeventeenDK_295313 : Nat.Prime 295313 := by norm_num

private theorem prime_oneHundredSeventeenDK_299363 : Nat.Prime 299363 := by norm_num

private theorem prime_oneHundredSeventeenDK_312031 : Nat.Prime 312031 := by norm_num

private theorem prime_oneHundredSeventeenDK_316847 : Nat.Prime 316847 := by norm_num

private theorem prime_oneHundredSeventeenDK_317903 : Nat.Prime 317903 := by norm_num

private theorem prime_oneHundredSeventeenDK_321187 : Nat.Prime 321187 := by norm_num

private theorem prime_oneHundredSeventeenDK_321911 : Nat.Prime 321911 := by norm_num

private theorem prime_oneHundredSeventeenDK_325411 : Nat.Prime 325411 := by norm_num

private theorem prime_oneHundredSeventeenDK_327289 : Nat.Prime 327289 := by norm_num

private theorem prime_oneHundredSeventeenDK_341461 : Nat.Prime 341461 := by norm_num

private theorem prime_oneHundredSeventeenDK_342337 : Nat.Prime 342337 := by norm_num

private theorem prime_oneHundredSeventeenDK_350437 : Nat.Prime 350437 := by norm_num

private theorem prime_oneHundredSeventeenDK_359663 : Nat.Prime 359663 := by norm_num

private theorem prime_oneHundredSeventeenDK_361451 : Nat.Prime 361451 := by norm_num

private theorem prime_oneHundredSeventeenDK_374317 : Nat.Prime 374317 := by norm_num

private theorem prime_oneHundredSeventeenDK_404017 : Nat.Prime 404017 := by norm_num

private theorem prime_oneHundredSeventeenDK_431929 : Nat.Prime 431929 := by norm_num

private theorem prime_oneHundredSeventeenDK_448867 : Nat.Prime 448867 := by norm_num

private theorem prime_oneHundredSeventeenDK_456523 : Nat.Prime 456523 := by norm_num

private theorem prime_oneHundredSeventeenDK_491737 : Nat.Prime 491737 := by norm_num

private theorem prime_oneHundredSeventeenDK_499663 : Nat.Prime 499663 := by norm_num

private theorem prime_oneHundredSeventeenDK_508577 : Nat.Prime 508577 := by norm_num

private theorem prime_oneHundredSeventeenDK_519119 : Nat.Prime 519119 := by norm_num

private theorem prime_oneHundredSeventeenDK_542537 : Nat.Prime 542537 := by norm_num

private theorem prime_oneHundredSeventeenDK_553961 : Nat.Prime 553961 := by norm_num

private theorem prime_oneHundredSeventeenDK_567659 : Nat.Prime 567659 := by norm_num

private theorem prime_oneHundredSeventeenDK_596159 : Nat.Prime 596159 := by norm_num

private theorem prime_oneHundredSeventeenDK_648371 : Nat.Prime 648371 := by norm_num

private theorem prime_oneHundredSeventeenDK_678593 : Nat.Prime 678593 := by norm_num

private theorem prime_oneHundredSeventeenDK_737927 : Nat.Prime 737927 := by norm_num

private theorem prime_oneHundredSeventeenDK_753583 : Nat.Prime 753583 := by norm_num

private theorem prime_oneHundredSeventeenDK_767537 : Nat.Prime 767537 := by norm_num

private theorem prime_oneHundredSeventeenDK_768073 : Nat.Prime 768073 := by norm_num

private theorem prime_oneHundredSeventeenDK_830887 : Nat.Prime 830887 := by norm_num

private theorem prime_oneHundredSeventeenDK_872033 : Nat.Prime 872033 := by norm_num

private theorem prime_oneHundredSeventeenDK_903781 : Nat.Prime 903781 := by norm_num

private theorem prime_oneHundredSeventeenDK_912049 : Nat.Prime 912049 := by norm_num

private theorem prime_oneHundredSeventeenDK_925291 : Nat.Prime 925291 := by norm_num

private theorem prime_oneHundredSeventeenDK_926507 : Nat.Prime 926507 := by norm_num

private theorem prime_oneHundredSeventeenDK_954469 : Nat.Prime 954469 := by norm_num

private theorem prime_oneHundredSeventeenDK_965749 : Nat.Prime 965749 := by norm_num

private theorem prime_oneHundredSeventeenDK_1050509 : Nat.Prime 1050509 := by norm_num

private theorem prime_oneHundredSeventeenDK_1152937 : Nat.Prime 1152937 := by norm_num

private theorem prime_oneHundredSeventeenDK_1170133 : Nat.Prime 1170133 := by norm_num

private theorem prime_oneHundredSeventeenDK_1182953 : Nat.Prime 1182953 := by norm_num

private theorem prime_oneHundredSeventeenDK_1247591 : Nat.Prime 1247591 := by norm_num

private theorem prime_oneHundredSeventeenDK_1332763 : Nat.Prime 1332763 := by norm_num

private theorem prime_oneHundredSeventeenDK_1342567 : Nat.Prime 1342567 := by norm_num

private theorem prime_oneHundredSeventeenDK_1446257 : Nat.Prime 1446257 := by norm_num

private theorem prime_oneHundredSeventeenDK_1448309 : Nat.Prime 1448309 := by norm_num

private theorem prime_oneHundredSeventeenDK_1473061 : Nat.Prime 1473061 := by norm_num

private theorem prime_oneHundredSeventeenDK_1474171 : Nat.Prime 1474171 := by norm_num

private theorem prime_oneHundredSeventeenDK_1509971 : Nat.Prime 1509971 := by norm_num

private theorem prime_oneHundredSeventeenDK_1551157 : Nat.Prime 1551157 := by norm_num

private theorem prime_oneHundredSeventeenDK_1608473 : Nat.Prime 1608473 := by norm_num

private theorem prime_oneHundredSeventeenDK_1611217 : Nat.Prime 1611217 := by norm_num

private theorem prime_oneHundredSeventeenDK_1617523 : Nat.Prime 1617523 := by norm_num

private theorem prime_oneHundredSeventeenDK_1697173 : Nat.Prime 1697173 := by norm_num

private theorem prime_oneHundredSeventeenDK_1744213 : Nat.Prime 1744213 := by norm_num

private theorem prime_oneHundredSeventeenDK_1879607 : Nat.Prime 1879607 := by norm_num

private theorem prime_oneHundredSeventeenDK_1971517 : Nat.Prime 1971517 := by norm_num

private theorem prime_oneHundredSeventeenDK_1997243 : Nat.Prime 1997243 := by norm_num

private theorem prime_oneHundredSeventeenDK_2297327 : Nat.Prime 2297327 := by norm_num

private theorem prime_oneHundredSeventeenDK_2313967 : Nat.Prime 2313967 := by norm_num

private theorem prime_oneHundredSeventeenDK_2348579 : Nat.Prime 2348579 := by norm_num

private theorem prime_oneHundredSeventeenDK_2484311 : Nat.Prime 2484311 := by norm_num

private theorem prime_oneHundredSeventeenDK_2573449 : Nat.Prime 2573449 := by norm_num

private theorem prime_oneHundredSeventeenDK_2587007 : Nat.Prime 2587007 := by norm_num

private theorem prime_oneHundredSeventeenDK_3048163 : Nat.Prime 3048163 := by norm_num

private theorem prime_oneHundredSeventeenDK_3059143 : Nat.Prime 3059143 := by norm_num

private theorem prime_oneHundredSeventeenDK_3062539 : Nat.Prime 3062539 := by norm_num

private theorem prime_oneHundredSeventeenDK_3166469 : Nat.Prime 3166469 := by norm_num

private theorem prime_oneHundredSeventeenDK_3331079 : Nat.Prime 3331079 := by norm_num

private theorem prime_oneHundredSeventeenDK_4027627 : Nat.Prime 4027627 := by norm_num

private theorem prime_oneHundredSeventeenDK_4179649 : Nat.Prime 4179649 := by norm_num

private theorem prime_oneHundredSeventeenDK_4302461 : Nat.Prime 4302461 := by norm_num

private theorem prime_oneHundredSeventeenDK_4526329 : Nat.Prime 4526329 := by norm_num

private theorem prime_oneHundredSeventeenDK_4618403 : Nat.Prime 4618403 := by norm_num

private theorem prime_oneHundredSeventeenDK_4682219 : Nat.Prime 4682219 := by norm_num

private theorem prime_oneHundredSeventeenDK_5052643 : Nat.Prime 5052643 := by norm_num

private theorem prime_oneHundredSeventeenDK_5132117 : Nat.Prime 5132117 := by norm_num

private theorem prime_oneHundredSeventeenDK_5202511 : Nat.Prime 5202511 := by norm_num

private theorem prime_oneHundredSeventeenDK_5285263 : Nat.Prime 5285263 := by norm_num

private theorem prime_oneHundredSeventeenDK_5663071 : Nat.Prime 5663071 := by norm_num

private theorem prime_oneHundredSeventeenDK_5757727 : Nat.Prime 5757727 := by norm_num

private theorem prime_oneHundredSeventeenDK_5816549 : Nat.Prime 5816549 := by norm_num

private theorem prime_oneHundredSeventeenDK_6045953 : Nat.Prime 6045953 := by norm_num

private theorem prime_oneHundredSeventeenDK_6379693 : Nat.Prime 6379693 := by norm_num

private theorem prime_oneHundredSeventeenDK_6986101 : Nat.Prime 6986101 := by norm_num

private theorem prime_oneHundredSeventeenDK_7631857 : Nat.Prime 7631857 := by norm_num

private theorem prime_oneHundredSeventeenDK_7760507 : Nat.Prime 7760507 := by norm_num

private theorem prime_oneHundredSeventeenDK_7882909 : Nat.Prime 7882909 := by norm_num

private theorem prime_oneHundredSeventeenDK_7914209 : Nat.Prime 7914209 := by norm_num

private theorem prime_oneHundredSeventeenDK_8259551 : Nat.Prime 8259551 := by norm_num

private theorem prime_oneHundredSeventeenDK_8270417 : Nat.Prime 8270417 := by norm_num

private theorem prime_oneHundredSeventeenDK_8302403 : Nat.Prime 8302403 := by norm_num

private theorem prime_oneHundredSeventeenDK_9890501 : Nat.Prime 9890501 := by norm_num

private theorem prime_oneHundredSeventeenDK_10320283 : Nat.Prime 10320283 := by norm_num

private theorem prime_oneHundredSeventeenDK_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredSeventeenDK_12901379 : Nat.Prime 12901379 := by norm_num

private theorem prime_oneHundredSeventeenDK_14885743 : Nat.Prime 14885743 := by norm_num

private theorem prime_oneHundredSeventeenDK_16411201 : Nat.Prime 16411201 := by norm_num

private theorem prime_oneHundredSeventeenDK_18101393 : Nat.Prime 18101393 := by norm_num

private theorem prime_oneHundredSeventeenDK_19916623 : Nat.Prime 19916623 := by norm_num

private theorem prime_oneHundredSeventeenDK_20699779 : Nat.Prime 20699779 := by norm_num

private theorem prime_oneHundredSeventeenDK_21937549 : Nat.Prime 21937549 := by norm_num

private theorem prime_oneHundredSeventeenDK_25109171 : Nat.Prime 25109171 := by norm_num

private theorem prime_oneHundredSeventeenDK_25742081 : Nat.Prime 25742081 := by norm_num

private theorem prime_oneHundredSeventeenDK_26032823 : Nat.Prime 26032823 := by norm_num

private theorem prime_oneHundredSeventeenDK_26060557 : Nat.Prime 26060557 := by norm_num

private theorem prime_oneHundredSeventeenDK_29956481 : Nat.Prime 29956481 := by norm_num

private theorem prime_oneHundredSeventeenDK_32084053 : Nat.Prime 32084053 := by
  apply lucas_primality 32084053 (2 : ZMod 32084053)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (11, 1), (13, 1), (2671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (11, 1), (13, 1), (2671, 1)] : List FactorBlock).map factorBlockValue).prod) = 32084053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_11
      · exact prime_oneHundredSeventeenDK_13
      · exact prime_oneHundredSeventeenDK_2671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 32084053) ^ 16042026 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 32084053) ^ 10694684 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 32084053) ^ 4583436 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 32084053) ^ 2916732 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 32084053) ^ 2468004 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 32084053) ^ 12012 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_34148237 : Nat.Prime 34148237 := by
  apply lucas_primality 34148237 (2 : ZMod 34148237)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (275389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (275389, 1)] : List FactorBlock).map factorBlockValue).prod) = 34148237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_31
      · exact prime_oneHundredSeventeenDK_275389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 34148237) ^ 17074118 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 34148237) ^ 1101556 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 34148237) ^ 124 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_35410211 : Nat.Prime 35410211 := by
  apply lucas_primality 35410211 (2 : ZMod 35410211)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (321911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (321911, 1)] : List FactorBlock).map factorBlockValue).prod) = 35410211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_11
      · exact prime_oneHundredSeventeenDK_321911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 35410211) ^ 17705105 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 35410211) ^ 7082042 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 35410211) ^ 3219110 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 35410211) ^ 110 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_35848051 : Nat.Prime 35848051 := by
  apply lucas_primality 35848051 (2 : ZMod 35848051)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (7, 1), (34141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (7, 1), (34141, 1)] : List FactorBlock).map factorBlockValue).prod) = 35848051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_34141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 35848051) ^ 17924025 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 35848051) ^ 11949350 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 35848051) ^ 7169610 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 35848051) ^ 5121150 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 35848051) ^ 1050 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_37097537 : Nat.Prime 37097537 := by
  apply lucas_primality 37097537 (3 : ZMod 37097537)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (17, 1), (4871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (17, 1), (4871, 1)] : List FactorBlock).map factorBlockValue).prod) = 37097537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_17
      · exact prime_oneHundredSeventeenDK_4871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 37097537) ^ 18548768 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 37097537) ^ 5299648 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 37097537) ^ 2182208 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 37097537) ^ 7616 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_37288723 : Nat.Prime 37288723 := by
  apply lucas_primality 37288723 (3 : ZMod 37288723)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (31, 2), (223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (31, 2), (223, 1)] : List FactorBlock).map factorBlockValue).prod) = 37288723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_29
      · exact prime_oneHundredSeventeenDK_31
      · exact prime_oneHundredSeventeenDK_223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 37288723) ^ 18644361 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 37288723) ^ 12429574 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 37288723) ^ 1285818 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 37288723) ^ 1202862 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 37288723) ^ 167214 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_37910053 : Nat.Prime 37910053 := by
  apply lucas_primality 37910053 (5 : ZMod 37910053)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (37, 1), (53, 1), (179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (37, 1), (53, 1), (179, 1)] : List FactorBlock).map factorBlockValue).prod) = 37910053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_37
      · exact prime_oneHundredSeventeenDK_53
      · exact prime_oneHundredSeventeenDK_179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 37910053) ^ 18955026 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 37910053) ^ 12636684 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 37910053) ^ 1024596 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 37910053) ^ 715284 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 37910053) ^ 211788 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_38398499 : Nat.Prime 38398499 := by
  apply lucas_primality 38398499 (2 : ZMod 38398499)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (325411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (325411, 1)] : List FactorBlock).map factorBlockValue).prod) = 38398499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_59
      · exact prime_oneHundredSeventeenDK_325411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 38398499) ^ 19199249 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 38398499) ^ 650822 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 38398499) ^ 118 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_41774363 : Nat.Prime 41774363 := by
  apply lucas_primality 41774363 (2 : ZMod 41774363)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (439, 1), (971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (439, 1), (971, 1)] : List FactorBlock).map factorBlockValue).prod) = 41774363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_439
      · exact prime_oneHundredSeventeenDK_971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 41774363) ^ 20887181 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 41774363) ^ 5967766 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 41774363) ^ 95158 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 41774363) ^ 43022 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_41838787 : Nat.Prime 41838787 := by
  apply lucas_primality 41838787 (3 : ZMod 41838787)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (37, 1), (5711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (37, 1), (5711, 1)] : List FactorBlock).map factorBlockValue).prod) = 41838787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_11
      · exact prime_oneHundredSeventeenDK_37
      · exact prime_oneHundredSeventeenDK_5711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 41838787) ^ 20919393 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 41838787) ^ 13946262 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 41838787) ^ 3803526 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 41838787) ^ 1130778 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 41838787) ^ 7326 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_49557307 : Nat.Prime 49557307 := by
  apply lucas_primality 49557307 (3 : ZMod 49557307)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (8259551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (8259551, 1)] : List FactorBlock).map factorBlockValue).prod) = 49557307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_8259551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 49557307) ^ 24778653 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 49557307) ^ 16519102 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 49557307) ^ 6 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_51484163 : Nat.Prime 51484163 := by
  apply lucas_primality 51484163 (2 : ZMod 51484163)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (25742081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (25742081, 1)] : List FactorBlock).map factorBlockValue).prod) = 51484163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_25742081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 51484163) ^ 25742081 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 51484163) ^ 2 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_52025111 : Nat.Prime 52025111 := by
  apply lucas_primality 52025111 (13 : ZMod 52025111)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (5202511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (5202511, 1)] : List FactorBlock).map factorBlockValue).prod) = 52025111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_5202511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 52025111) ^ 26012555 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (13 : ZMod 52025111) ^ 10405022 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (13 : ZMod 52025111) ^ 10 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_53826119 : Nat.Prime 53826119 := by
  apply lucas_primality 53826119 (7 : ZMod 53826119)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (1170133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (1170133, 1)] : List FactorBlock).map factorBlockValue).prod) = 53826119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_23
      · exact prime_oneHundredSeventeenDK_1170133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 53826119) ^ 26913059 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 53826119) ^ 2340266 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 53826119) ^ 46 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_57268993 : Nat.Prime 57268993 := by
  apply lucas_primality 57268993 (5 : ZMod 57268993)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (11, 1), (6779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (11, 1), (6779, 1)] : List FactorBlock).map factorBlockValue).prod) = 57268993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_11
      · exact prime_oneHundredSeventeenDK_6779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 57268993) ^ 28634496 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 57268993) ^ 19089664 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 57268993) ^ 5206272 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 57268993) ^ 8448 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_61405583 : Nat.Prime 61405583 := by
  apply lucas_primality 61405583 (5 : ZMod 61405583)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (149, 1), (29437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (149, 1), (29437, 1)] : List FactorBlock).map factorBlockValue).prod) = 61405583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_149
      · exact prime_oneHundredSeventeenDK_29437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 61405583) ^ 30702791 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 61405583) ^ 8772226 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 61405583) ^ 412118 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 61405583) ^ 2086 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_75825557 : Nat.Prime 75825557 := by
  apply lucas_primality 75825557 (2 : ZMod 75825557)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (151, 1), (125539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (151, 1), (125539, 1)] : List FactorBlock).map factorBlockValue).prod) = 75825557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_151
      · exact prime_oneHundredSeventeenDK_125539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 75825557) ^ 37912778 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 75825557) ^ 502156 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 75825557) ^ 604 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_84436981 : Nat.Prime 84436981 := by
  apply lucas_primality 84436981 (7 : ZMod 84436981)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (29, 1), (48527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (29, 1), (48527, 1)] : List FactorBlock).map factorBlockValue).prod) = 84436981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_29
      · exact prime_oneHundredSeventeenDK_48527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 84436981) ^ 42218490 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 84436981) ^ 28145660 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 84436981) ^ 16887396 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 84436981) ^ 2911620 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 84436981) ^ 1740 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_84880469 : Nat.Prime 84880469 := by
  apply lucas_primality 84880469 (2 : ZMod 84880469)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (59, 1), (359663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (59, 1), (359663, 1)] : List FactorBlock).map factorBlockValue).prod) = 84880469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_59
      · exact prime_oneHundredSeventeenDK_359663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 84880469) ^ 42440234 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 84880469) ^ 1438652 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 84880469) ^ 236 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_102208373 : Nat.Prime 102208373 := by
  apply lucas_primality 102208373 (3 : ZMod 102208373)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (19, 1), (192121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (19, 1), (192121, 1)] : List FactorBlock).map factorBlockValue).prod) = 102208373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_19
      · exact prime_oneHundredSeventeenDK_192121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 102208373) ^ 51104186 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 102208373) ^ 14601196 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 102208373) ^ 5379388 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 102208373) ^ 532 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_102346169 : Nat.Prime 102346169 := by
  apply lucas_primality 102346169 (3 : ZMod 102346169)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (41, 1), (312031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (41, 1), (312031, 1)] : List FactorBlock).map factorBlockValue).prod) = 102346169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_41
      · exact prime_oneHundredSeventeenDK_312031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 102346169) ^ 51173084 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 102346169) ^ 2496248 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 102346169) ^ 328 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_104050223 : Nat.Prime 104050223 := by
  apply lucas_primality 104050223 (5 : ZMod 104050223)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (52025111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (52025111, 1)] : List FactorBlock).map factorBlockValue).prod) = 104050223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_52025111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 104050223) ^ 52025111 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 104050223) ^ 2 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_104652781 : Nat.Prime 104652781 := by
  apply lucas_primality 104652781 (14 : ZMod 104652781)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (1744213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (1744213, 1)] : List FactorBlock).map factorBlockValue).prod) = 104652781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_1744213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 104652781) ^ 52326390 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (14 : ZMod 104652781) ^ 34884260 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (14 : ZMod 104652781) ^ 20930556 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (14 : ZMod 104652781) ^ 60 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_106596317 : Nat.Prime 106596317 := by
  apply lucas_primality 106596317 (2 : ZMod 106596317)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (739, 1), (36061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (739, 1), (36061, 1)] : List FactorBlock).map factorBlockValue).prod) = 106596317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_739
      · exact prime_oneHundredSeventeenDK_36061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 106596317) ^ 53298158 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 106596317) ^ 144244 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 106596317) ^ 2956 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_111616303 : Nat.Prime 111616303 := by
  apply lucas_primality 111616303 (5 : ZMod 111616303)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (29, 1), (91639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (29, 1), (91639, 1)] : List FactorBlock).map factorBlockValue).prod) = 111616303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_29
      · exact prime_oneHundredSeventeenDK_91639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 111616303) ^ 55808151 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 111616303) ^ 37205434 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 111616303) ^ 15945186 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 111616303) ^ 3848838 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 111616303) ^ 1218 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_113275949 : Nat.Prime 113275949 := by
  apply lucas_primality 113275949 (2 : ZMod 113275949)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (41, 1), (36353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (41, 1), (36353, 1)] : List FactorBlock).map factorBlockValue).prod) = 113275949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_19
      · exact prime_oneHundredSeventeenDK_41
      · exact prime_oneHundredSeventeenDK_36353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 113275949) ^ 56637974 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 113275949) ^ 5961892 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 113275949) ^ 2762828 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 113275949) ^ 3116 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_115555991 : Nat.Prime 115555991 := by
  apply lucas_primality 115555991 (11 : ZMod 115555991)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (1050509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (1050509, 1)] : List FactorBlock).map factorBlockValue).prod) = 115555991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_11
      · exact prime_oneHundredSeventeenDK_1050509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 115555991) ^ 57777995 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 115555991) ^ 23111198 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 115555991) ^ 10505090 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 115555991) ^ 110 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_124587563 : Nat.Prime 124587563 := by
  apply lucas_primality 124587563 (2 : ZMod 124587563)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (5663071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (5663071, 1)] : List FactorBlock).map factorBlockValue).prod) = 124587563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_11
      · exact prime_oneHundredSeventeenDK_5663071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 124587563) ^ 62293781 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 124587563) ^ 11326142 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 124587563) ^ 22 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_131433079 : Nat.Prime 131433079 := by
  apply lucas_primality 131433079 (17 : ZMod 131433079)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (223, 1), (14033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (223, 1), (14033, 1)] : List FactorBlock).map factorBlockValue).prod) = 131433079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_223
      · exact prime_oneHundredSeventeenDK_14033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 131433079) ^ 65716539 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (17 : ZMod 131433079) ^ 43811026 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (17 : ZMod 131433079) ^ 18776154 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (17 : ZMod 131433079) ^ 589386 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (17 : ZMod 131433079) ^ 9366 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_139568171 : Nat.Prime 139568171 := by
  apply lucas_primality 139568171 (2 : ZMod 139568171)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (284833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (284833, 1)] : List FactorBlock).map factorBlockValue).prod) = 139568171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_284833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 139568171) ^ 69784085 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 139568171) ^ 27913634 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 139568171) ^ 19938310 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 139568171) ^ 490 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_142641539 : Nat.Prime 142641539 := by
  apply lucas_primality 142641539 (2 : ZMod 142641539)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (23, 1), (238531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (23, 1), (238531, 1)] : List FactorBlock).map factorBlockValue).prod) = 142641539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_13
      · exact prime_oneHundredSeventeenDK_23
      · exact prime_oneHundredSeventeenDK_238531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 142641539) ^ 71320769 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 142641539) ^ 10972426 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 142641539) ^ 6201806 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 142641539) ^ 598 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_151640213 : Nat.Prime 151640213 := by
  apply lucas_primality 151640213 (2 : ZMod 151640213)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37910053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37910053, 1)] : List FactorBlock).map factorBlockValue).prod) = 151640213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_37910053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 151640213) ^ 75820106 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 151640213) ^ 4 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_153773531 : Nat.Prime 153773531 := by
  apply lucas_primality 153773531 (2 : ZMod 153773531)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (179, 1), (271, 1), (317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (179, 1), (271, 1), (317, 1)] : List FactorBlock).map factorBlockValue).prod) = 153773531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_179
      · exact prime_oneHundredSeventeenDK_271
      · exact prime_oneHundredSeventeenDK_317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 153773531) ^ 76886765 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 153773531) ^ 30754706 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 153773531) ^ 859070 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 153773531) ^ 567430 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 153773531) ^ 485090 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_159289451 : Nat.Prime 159289451 := by
  apply lucas_primality 159289451 (6 : ZMod 159289451)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (83, 1), (131, 1), (293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (83, 1), (131, 1), (293, 1)] : List FactorBlock).map factorBlockValue).prod) = 159289451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_83
      · exact prime_oneHundredSeventeenDK_131
      · exact prime_oneHundredSeventeenDK_293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 159289451) ^ 79644725 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 159289451) ^ 31857890 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 159289451) ^ 1919150 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 159289451) ^ 1215950 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 159289451) ^ 543650 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_169760939 : Nat.Prime 169760939 := by
  apply lucas_primality 169760939 (2 : ZMod 169760939)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (84880469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (84880469, 1)] : List FactorBlock).map factorBlockValue).prod) = 169760939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_84880469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 169760939) ^ 84880469 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 169760939) ^ 2 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_185423809 : Nat.Prime 185423809 := by
  apply lucas_primality 185423809 (11 : ZMod 185423809)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (965749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (965749, 1)] : List FactorBlock).map factorBlockValue).prod) = 185423809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_965749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 185423809) ^ 92711904 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 185423809) ^ 61807936 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 185423809) ^ 192 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_231179551 : Nat.Prime 231179551 := by
  apply lucas_primality 231179551 (7 : ZMod 231179551)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (7, 2), (71, 1), (443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (7, 2), (71, 1), (443, 1)] : List FactorBlock).map factorBlockValue).prod) = 231179551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_71
      · exact prime_oneHundredSeventeenDK_443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 231179551) ^ 115589775 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 231179551) ^ 77059850 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 231179551) ^ 46235910 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 231179551) ^ 33025650 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 231179551) ^ 3256050 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 231179551) ^ 521850 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_245863127 : Nat.Prime 245863127 := by
  apply lucas_primality 245863127 (5 : ZMod 245863127)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (9127, 1), (13469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (9127, 1), (13469, 1)] : List FactorBlock).map factorBlockValue).prod) = 245863127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_9127
      · exact prime_oneHundredSeventeenDK_13469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 245863127) ^ 122931563 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 245863127) ^ 26938 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 245863127) ^ 18254 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_254606221 : Nat.Prime 254606221 := by
  apply lucas_primality 254606221 (18 : ZMod 254606221)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (11, 1), (42863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (11, 1), (42863, 1)] : List FactorBlock).map factorBlockValue).prod) = 254606221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_11
      · exact prime_oneHundredSeventeenDK_42863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (18 : ZMod 254606221) ^ 127303110 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (18 : ZMod 254606221) ^ 84868740 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (18 : ZMod 254606221) ^ 50921244 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (18 : ZMod 254606221) ^ 23146020 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (18 : ZMod 254606221) ^ 5940 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_258343691 : Nat.Prime 258343691 := by
  apply lucas_primality 258343691 (2 : ZMod 258343691)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (2348579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (2348579, 1)] : List FactorBlock).map factorBlockValue).prod) = 258343691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_11
      · exact prime_oneHundredSeventeenDK_2348579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 258343691) ^ 129171845 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 258343691) ^ 51668738 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 258343691) ^ 23485790 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 258343691) ^ 110 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_338070989 : Nat.Prime 338070989 := by
  apply lucas_primality 338070989 (3 : ZMod 338070989)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (419, 1), (4691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (419, 1), (4691, 1)] : List FactorBlock).map factorBlockValue).prod) = 338070989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_43
      · exact prime_oneHundredSeventeenDK_419
      · exact prime_oneHundredSeventeenDK_4691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 338070989) ^ 169035494 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 338070989) ^ 7862116 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 338070989) ^ 806852 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 338070989) ^ 72068 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_349996873 : Nat.Prime 349996873 := by
  apply lucas_primality 349996873 (11 : ZMod 349996873)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (767537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (767537, 1)] : List FactorBlock).map factorBlockValue).prod) = 349996873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_19
      · exact prime_oneHundredSeventeenDK_767537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 349996873) ^ 174998436 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 349996873) ^ 116665624 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 349996873) ^ 18420888 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 349996873) ^ 456 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_368913829 : Nat.Prime 368913829 := by
  apply lucas_primality 368913829 (2 : ZMod 368913829)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (37, 1), (830887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (37, 1), (830887, 1)] : List FactorBlock).map factorBlockValue).prod) = 368913829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_37
      · exact prime_oneHundredSeventeenDK_830887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 368913829) ^ 184456914 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 368913829) ^ 122971276 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 368913829) ^ 9970644 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 368913829) ^ 444 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_387171233 : Nat.Prime 387171233 := by
  apply lucas_primality 387171233 (3 : ZMod 387171233)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (97, 1), (103, 1), (173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (97, 1), (103, 1), (173, 1)] : List FactorBlock).map factorBlockValue).prod) = 387171233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_97
      · exact prime_oneHundredSeventeenDK_103
      · exact prime_oneHundredSeventeenDK_173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 387171233) ^ 193585616 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 387171233) ^ 55310176 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 387171233) ^ 3991456 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 387171233) ^ 3758944 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 387171233) ^ 2237984 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_411751841 : Nat.Prime 411751841 := by
  apply lucas_primality 411751841 (3 : ZMod 411751841)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (2573449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (2573449, 1)] : List FactorBlock).map factorBlockValue).prod) = 411751841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_2573449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 411751841) ^ 205875920 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 411751841) ^ 82350368 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 411751841) ^ 160 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_425525917 : Nat.Prime 425525917 := by
  apply lucas_primality 425525917 (5 : ZMod 425525917)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (79, 1), (448867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (79, 1), (448867, 1)] : List FactorBlock).map factorBlockValue).prod) = 425525917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_79
      · exact prime_oneHundredSeventeenDK_448867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 425525917) ^ 212762958 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 425525917) ^ 141841972 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 425525917) ^ 5386404 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 425525917) ^ 948 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_429543953 : Nat.Prime 429543953 := by
  apply lucas_primality 429543953 (3 : ZMod 429543953)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (23, 1), (37, 1), (31547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (23, 1), (37, 1), (31547, 1)] : List FactorBlock).map factorBlockValue).prod) = 429543953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_23
      · exact prime_oneHundredSeventeenDK_37
      · exact prime_oneHundredSeventeenDK_31547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 429543953) ^ 214771976 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 429543953) ^ 18675824 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 429543953) ^ 11609296 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 429543953) ^ 13616 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_430764149 : Nat.Prime 430764149 := by
  apply lucas_primality 430764149 (2 : ZMod 430764149)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (4682219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (4682219, 1)] : List FactorBlock).map factorBlockValue).prod) = 430764149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_23
      · exact prime_oneHundredSeventeenDK_4682219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 430764149) ^ 215382074 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 430764149) ^ 18728876 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 430764149) ^ 92 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_546624703 : Nat.Prime 546624703 := by
  apply lucas_primality 546624703 (3 : ZMod 546624703)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (157, 1), (14879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (157, 1), (14879, 1)] : List FactorBlock).map factorBlockValue).prod) = 546624703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_13
      · exact prime_oneHundredSeventeenDK_157
      · exact prime_oneHundredSeventeenDK_14879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 546624703) ^ 273312351 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 546624703) ^ 182208234 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 546624703) ^ 42048054 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 546624703) ^ 3481686 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 546624703) ^ 36738 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_640433267 : Nat.Prime 640433267 := by
  apply lucas_primality 640433267 (2 : ZMod 640433267)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) = 640433267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_11
      · exact prime_oneHundredSeventeenDK_19
      · exact prime_oneHundredSeventeenDK_61
      · exact prime_oneHundredSeventeenDK_25117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 640433267) ^ 320216633 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 58221206 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 33707014 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 10498906 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 25498 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_17203
      · exact prime_oneHundredSeventeenDK_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_729682649 : Nat.Prime 729682649 := by
  apply lucas_primality 729682649 (3 : ZMod 729682649)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (107, 1), (191, 1), (4463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (107, 1), (191, 1), (4463, 1)] : List FactorBlock).map factorBlockValue).prod) = 729682649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_107
      · exact prime_oneHundredSeventeenDK_191
      · exact prime_oneHundredSeventeenDK_4463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 729682649) ^ 364841324 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 729682649) ^ 6819464 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 729682649) ^ 3820328 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 729682649) ^ 163496 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_772908557 : Nat.Prime 772908557 := by
  apply lucas_primality 772908557 (2 : ZMod 772908557)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (71, 1), (55541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (71, 1), (55541, 1)] : List FactorBlock).map factorBlockValue).prod) = 772908557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_71
      · exact prime_oneHundredSeventeenDK_55541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 772908557) ^ 386454278 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 772908557) ^ 110415508 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 772908557) ^ 10886036 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 772908557) ^ 13916 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_820351907 : Nat.Prime 820351907 := by
  apply lucas_primality 820351907 (2 : ZMod 820351907)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (37288723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (37288723, 1)] : List FactorBlock).map factorBlockValue).prod) = 820351907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_11
      · exact prime_oneHundredSeventeenDK_37288723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 820351907) ^ 410175953 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 820351907) ^ 74577446 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 820351907) ^ 22 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_829112689 : Nat.Prime 829112689 := by
  apply lucas_primality 829112689 (7 : ZMod 829112689)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5757727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5757727, 1)] : List FactorBlock).map factorBlockValue).prod) = 829112689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5757727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 829112689) ^ 414556344 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 829112689) ^ 276370896 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 829112689) ^ 144 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_904820593 : Nat.Prime 904820593 := by
  apply lucas_primality 904820593 (5 : ZMod 904820593)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (13, 2), (71, 1), (1571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (13, 2), (71, 1), (1571, 1)] : List FactorBlock).map factorBlockValue).prod) = 904820593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_13
      · exact prime_oneHundredSeventeenDK_71
      · exact prime_oneHundredSeventeenDK_1571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 904820593) ^ 452410296 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 904820593) ^ 301606864 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 904820593) ^ 69601584 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 904820593) ^ 12743952 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 904820593) ^ 575952 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_906208483 : Nat.Prime 906208483 := by
  apply lucas_primality 906208483 (2 : ZMod 906208483)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (131, 1), (1152937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (131, 1), (1152937, 1)] : List FactorBlock).map factorBlockValue).prod) = 906208483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_131
      · exact prime_oneHundredSeventeenDK_1152937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 906208483) ^ 453104241 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 906208483) ^ 302069494 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 906208483) ^ 6917622 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 906208483) ^ 786 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_924447929 : Nat.Prime 924447929 := by
  apply lucas_primality 924447929 (3 : ZMod 924447929)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (115555991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (115555991, 1)] : List FactorBlock).map factorBlockValue).prod) = 924447929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_115555991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 924447929) ^ 462223964 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 924447929) ^ 8 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_945329461 : Nat.Prime 945329461 := by
  apply lucas_primality 945329461 (2 : ZMod 945329461)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (151, 2), (691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (151, 2), (691, 1)] : List FactorBlock).map factorBlockValue).prod) = 945329461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_151
      · exact prime_oneHundredSeventeenDK_691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 945329461) ^ 472664730 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 945329461) ^ 315109820 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 945329461) ^ 189065892 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 945329461) ^ 6260460 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 945329461) ^ 1368060 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_989533793 : Nat.Prime 989533793 := by
  apply lucas_primality 989533793 (3 : ZMod 989533793)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (13, 1), (503, 1), (4729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (13, 1), (503, 1), (4729, 1)] : List FactorBlock).map factorBlockValue).prod) = 989533793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_13
      · exact prime_oneHundredSeventeenDK_503
      · exact prime_oneHundredSeventeenDK_4729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 989533793) ^ 494766896 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 989533793) ^ 76117984 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 989533793) ^ 1967264 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 989533793) ^ 209248 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_1140911063 : Nat.Prime 1140911063 := by
  apply lucas_primality 1140911063 (5 : ZMod 1140911063)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (233, 1), (739, 1), (3313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (233, 1), (739, 1), (3313, 1)] : List FactorBlock).map factorBlockValue).prod) = 1140911063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_233
      · exact prime_oneHundredSeventeenDK_739
      · exact prime_oneHundredSeventeenDK_3313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1140911063) ^ 570455531 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1140911063) ^ 4896614 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1140911063) ^ 1543858 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1140911063) ^ 344374 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_1180123171 : Nat.Prime 1180123171 := by
  apply lucas_primality 1180123171 (13 : ZMod 1180123171)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (2313967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (2313967, 1)] : List FactorBlock).map factorBlockValue).prod) = 1180123171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_17
      · exact prime_oneHundredSeventeenDK_2313967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 1180123171) ^ 590061585 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (13 : ZMod 1180123171) ^ 393374390 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (13 : ZMod 1180123171) ^ 236024634 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (13 : ZMod 1180123171) ^ 69419010 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (13 : ZMod 1180123171) ^ 510 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_1211157029 : Nat.Prime 1211157029 := by
  apply lucas_primality 1211157029 (2 : ZMod 1211157029)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (467, 1), (648371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (467, 1), (648371, 1)] : List FactorBlock).map factorBlockValue).prod) = 1211157029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_467
      · exact prime_oneHundredSeventeenDK_648371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1211157029) ^ 605578514 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1211157029) ^ 2593484 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1211157029) ^ 1868 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_1329916981 : Nat.Prime 1329916981 := by
  apply lucas_primality 1329916981 (11 : ZMod 1329916981)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (3166469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (3166469, 1)] : List FactorBlock).map factorBlockValue).prod) = 1329916981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_3166469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1329916981) ^ 664958490 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 1329916981) ^ 443305660 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 1329916981) ^ 265983396 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 1329916981) ^ 189988140 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 1329916981) ^ 420 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_1373986741 : Nat.Prime 1373986741 := by
  apply lucas_primality 1373986741 (2 : ZMod 1373986741)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (43, 1), (76079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (43, 1), (76079, 1)] : List FactorBlock).map factorBlockValue).prod) = 1373986741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_43
      · exact prime_oneHundredSeventeenDK_76079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1373986741) ^ 686993370 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1373986741) ^ 457995580 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1373986741) ^ 274797348 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1373986741) ^ 196283820 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1373986741) ^ 31953180 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1373986741) ^ 18060 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_1389075071 : Nat.Prime 1389075071 := by
  apply lucas_primality 1389075071 (13 : ZMod 1389075071)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (107, 1), (229, 1), (5669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (107, 1), (229, 1), (5669, 1)] : List FactorBlock).map factorBlockValue).prod) = 1389075071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_107
      · exact prime_oneHundredSeventeenDK_229
      · exact prime_oneHundredSeventeenDK_5669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 1389075071) ^ 694537535 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (13 : ZMod 1389075071) ^ 277815014 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (13 : ZMod 1389075071) ^ 12982010 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (13 : ZMod 1389075071) ^ 6065830 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (13 : ZMod 1389075071) ^ 245030 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_1533463643 : Nat.Prime 1533463643 := by
  apply lucas_primality 1533463643 (5 : ZMod 1533463643)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (3491, 1), (4673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (3491, 1), (4673, 1)] : List FactorBlock).map factorBlockValue).prod) = 1533463643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_47
      · exact prime_oneHundredSeventeenDK_3491
      · exact prime_oneHundredSeventeenDK_4673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1533463643) ^ 766731821 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1533463643) ^ 32626886 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1533463643) ^ 439262 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1533463643) ^ 328154 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_1846492777 : Nat.Prime 1846492777 := by
  apply lucas_primality 1846492777 (5 : ZMod 1846492777)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (97, 1), (419, 1), (631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (97, 1), (419, 1), (631, 1)] : List FactorBlock).map factorBlockValue).prod) = 1846492777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_97
      · exact prime_oneHundredSeventeenDK_419
      · exact prime_oneHundredSeventeenDK_631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1846492777) ^ 923246388 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1846492777) ^ 615497592 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1846492777) ^ 19036008 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1846492777) ^ 4406904 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1846492777) ^ 2926296 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_1980602333 : Nat.Prime 1980602333 := by
  apply lucas_primality 1980602333 (2 : ZMod 1980602333)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (26060557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (26060557, 1)] : List FactorBlock).map factorBlockValue).prod) = 1980602333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_19
      · exact prime_oneHundredSeventeenDK_26060557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1980602333) ^ 990301166 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1980602333) ^ 104242228 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1980602333) ^ 76 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_2152359269 : Nat.Prime 2152359269 := by
  apply lucas_primality 2152359269 (2 : ZMod 2152359269)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (89, 1), (6045953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (89, 1), (6045953, 1)] : List FactorBlock).map factorBlockValue).prod) = 2152359269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_89
      · exact prime_oneHundredSeventeenDK_6045953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2152359269) ^ 1076179634 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2152359269) ^ 24183812 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2152359269) ^ 356 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_2318099881 : Nat.Prime 2318099881 := by
  apply lucas_primality 2318099881 (7 : ZMod 2318099881)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (349, 1), (55351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (349, 1), (55351, 1)] : List FactorBlock).map factorBlockValue).prod) = 2318099881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_349
      · exact prime_oneHundredSeventeenDK_55351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2318099881) ^ 1159049940 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 2318099881) ^ 772699960 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 2318099881) ^ 463619976 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 2318099881) ^ 6642120 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 2318099881) ^ 41880 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_2810396503 : Nat.Prime 2810396503 := by
  apply lucas_primality 2810396503 (3 : ZMod 2810396503)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (307, 1), (508577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (307, 1), (508577, 1)] : List FactorBlock).map factorBlockValue).prod) = 2810396503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_307
      · exact prime_oneHundredSeventeenDK_508577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2810396503) ^ 1405198251 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2810396503) ^ 936798834 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2810396503) ^ 9154386 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2810396503) ^ 5526 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_2851881371 : Nat.Prime 2851881371 := by
  apply lucas_primality 2851881371 (2 : ZMod 2851881371)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (21937549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (21937549, 1)] : List FactorBlock).map factorBlockValue).prod) = 2851881371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_13
      · exact prime_oneHundredSeventeenDK_21937549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2851881371) ^ 1425940685 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2851881371) ^ 570376274 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2851881371) ^ 219375490 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2851881371) ^ 130 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_3371100101 : Nat.Prime 3371100101 := by
  apply lucas_primality 3371100101 (7 : ZMod 3371100101)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (827, 1), (40763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (827, 1), (40763, 1)] : List FactorBlock).map factorBlockValue).prod) = 3371100101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_827
      · exact prime_oneHundredSeventeenDK_40763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 3371100101) ^ 1685550050 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 3371100101) ^ 674220020 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 3371100101) ^ 4076300 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 3371100101) ^ 82700 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_3716300911 : Nat.Prime 3716300911 := by
  apply lucas_primality 3716300911 (6 : ZMod 3716300911)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (89, 1), (198839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (89, 1), (198839, 1)] : List FactorBlock).map factorBlockValue).prod) = 3716300911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_89
      · exact prime_oneHundredSeventeenDK_198839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3716300911) ^ 1858150455 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 3716300911) ^ 1238766970 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 3716300911) ^ 743260182 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 3716300911) ^ 530900130 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 3716300911) ^ 41756190 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 3716300911) ^ 18690 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_3944461847 : Nat.Prime 3944461847 := by
  apply lucas_primality 3944461847 (5 : ZMod 3944461847)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (113, 1), (1342567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (113, 1), (1342567, 1)] : List FactorBlock).map factorBlockValue).prod) = 3944461847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_13
      · exact prime_oneHundredSeventeenDK_113
      · exact prime_oneHundredSeventeenDK_1342567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3944461847) ^ 1972230923 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 3944461847) ^ 303420142 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 3944461847) ^ 34906742 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 3944461847) ^ 2938 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_4237659991 : Nat.Prime 4237659991 := by
  apply lucas_primality 4237659991 (6 : ZMod 4237659991)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (5, 1), (103, 1), (16931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (5, 1), (103, 1), (16931, 1)] : List FactorBlock).map factorBlockValue).prod) = 4237659991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_103
      · exact prime_oneHundredSeventeenDK_16931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 4237659991) ^ 2118829995 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 4237659991) ^ 1412553330 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 4237659991) ^ 847531998 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 4237659991) ^ 41142330 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 4237659991) ^ 250290 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_4315154339 : Nat.Prime 4315154339 := by
  apply lucas_primality 4315154339 (2 : ZMod 4315154339)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (23, 1), (967, 1), (8819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (23, 1), (967, 1), (8819, 1)] : List FactorBlock).map factorBlockValue).prod) = 4315154339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_11
      · exact prime_oneHundredSeventeenDK_23
      · exact prime_oneHundredSeventeenDK_967
      · exact prime_oneHundredSeventeenDK_8819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4315154339) ^ 2157577169 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4315154339) ^ 392286758 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4315154339) ^ 187615406 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4315154339) ^ 4462414 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4315154339) ^ 489302 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_5055574231 : Nat.Prime 5055574231 := by
  apply lucas_primality 5055574231 (7 : ZMod 5055574231)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (7, 1), (251, 1), (10657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (7, 1), (251, 1), (10657, 1)] : List FactorBlock).map factorBlockValue).prod) = 5055574231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_251
      · exact prime_oneHundredSeventeenDK_10657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 5055574231) ^ 2527787115 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 5055574231) ^ 1685191410 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 5055574231) ^ 1011114846 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 5055574231) ^ 722224890 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 5055574231) ^ 20141730 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 5055574231) ^ 474390 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_5434050593 : Nat.Prime 5434050593 := by
  apply lucas_primality 5434050593 (3 : ZMod 5434050593)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (313, 1), (542537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (313, 1), (542537, 1)] : List FactorBlock).map factorBlockValue).prod) = 5434050593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_313
      · exact prime_oneHundredSeventeenDK_542537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5434050593) ^ 2717025296 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5434050593) ^ 17361184 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5434050593) ^ 10016 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_5792061817 : Nat.Prime 5792061817 := by
  apply lucas_primality 5792061817 (5 : ZMod 5792061817)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (43, 1), (207869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (43, 1), (207869, 1)] : List FactorBlock).map factorBlockValue).prod) = 5792061817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_43
      · exact prime_oneHundredSeventeenDK_207869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 5792061817) ^ 2896030908 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 5792061817) ^ 1930687272 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 5792061817) ^ 134699112 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 5792061817) ^ 27864 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_5893280359 : Nat.Prime 5893280359 := by
  apply lucas_primality 5893280359 (3 : ZMod 5893280359)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (31, 1), (4526329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (31, 1), (4526329, 1)] : List FactorBlock).map factorBlockValue).prod) = 5893280359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_31
      · exact prime_oneHundredSeventeenDK_4526329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5893280359) ^ 2946640179 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5893280359) ^ 1964426786 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5893280359) ^ 841897194 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5893280359) ^ 190105818 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5893280359) ^ 1302 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_31
      · exact prime_oneHundredSeventeenDK_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_6998309863 : Nat.Prime 6998309863 := by
  apply lucas_primality 6998309863 (3 : ZMod 6998309863)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (19, 1), (67, 1), (53897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (19, 1), (67, 1), (53897, 1)] : List FactorBlock).map factorBlockValue).prod) = 6998309863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_17
      · exact prime_oneHundredSeventeenDK_19
      · exact prime_oneHundredSeventeenDK_67
      · exact prime_oneHundredSeventeenDK_53897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6998309863) ^ 3499154931 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 6998309863) ^ 2332769954 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 6998309863) ^ 411665286 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 6998309863) ^ 368332098 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 6998309863) ^ 104452386 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 6998309863) ^ 129846 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_8846288837 : Nat.Prime 8846288837 := by
  apply lucas_primality 8846288837 (2 : ZMod 8846288837)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (31, 1), (926507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (31, 1), (926507, 1)] : List FactorBlock).map factorBlockValue).prod) = 8846288837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_11
      · exact prime_oneHundredSeventeenDK_31
      · exact prime_oneHundredSeventeenDK_926507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8846288837) ^ 4423144418 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8846288837) ^ 1263755548 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8846288837) ^ 804208076 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8846288837) ^ 285364156 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8846288837) ^ 9548 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_9000837667 : Nat.Prime 9000837667 := by
  apply lucas_primality 9000837667 (3 : ZMod 9000837667)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (41, 1), (79, 1), (51461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (41, 1), (79, 1), (51461, 1)] : List FactorBlock).map factorBlockValue).prod) = 9000837667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_41
      · exact prime_oneHundredSeventeenDK_79
      · exact prime_oneHundredSeventeenDK_51461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9000837667) ^ 4500418833 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 9000837667) ^ 3000279222 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 9000837667) ^ 219532626 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 9000837667) ^ 113934654 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 9000837667) ^ 174906 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_9257508937 : Nat.Prime 9257508937 := by
  apply lucas_primality 9257508937 (5 : ZMod 9257508937)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (13, 1), (9890501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (13, 1), (9890501, 1)] : List FactorBlock).map factorBlockValue).prod) = 9257508937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_13
      · exact prime_oneHundredSeventeenDK_9890501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9257508937) ^ 4628754468 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 9257508937) ^ 3085836312 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 9257508937) ^ 712116072 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 9257508937) ^ 936 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_10373380819 : Nat.Prime 10373380819 := by
  apply lucas_primality 10373380819 (2 : ZMod 10373380819)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (271, 1), (6379693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (271, 1), (6379693, 1)] : List FactorBlock).map factorBlockValue).prod) = 10373380819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_271
      · exact prime_oneHundredSeventeenDK_6379693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10373380819) ^ 5186690409 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 10373380819) ^ 3457793606 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 10373380819) ^ 38278158 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 10373380819) ^ 1626 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_11801231711 : Nat.Prime 11801231711 := by
  apply lucas_primality 11801231711 (11 : ZMod 11801231711)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1180123171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1180123171, 1)] : List FactorBlock).map factorBlockValue).prod) = 11801231711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_1180123171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 11801231711) ^ 5900615855 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 11801231711) ^ 2360246342 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 11801231711) ^ 10 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_12503007593 : Nat.Prime 12503007593 := by
  apply lucas_primality 12503007593 (3 : ZMod 12503007593)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (14831, 1), (105379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (14831, 1), (105379, 1)] : List FactorBlock).map factorBlockValue).prod) = 12503007593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_14831
      · exact prime_oneHundredSeventeenDK_105379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 12503007593) ^ 6251503796 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 12503007593) ^ 843032 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 12503007593) ^ 118648 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_12543070187 : Nat.Prime 12543070187 := by
  apply lucas_primality 12543070187 (2 : ZMod 12543070187)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (368913829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (368913829, 1)] : List FactorBlock).map factorBlockValue).prod) = 12543070187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_17
      · exact prime_oneHundredSeventeenDK_368913829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 12543070187) ^ 6271535093 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 12543070187) ^ 737827658 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 12543070187) ^ 34 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_12886318591 : Nat.Prime 12886318591 := by
  apply lucas_primality 12886318591 (6 : ZMod 12886318591)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (429543953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (429543953, 1)] : List FactorBlock).map factorBlockValue).prod) = 12886318591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_429543953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 12886318591) ^ 6443159295 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 12886318591) ^ 4295439530 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 12886318591) ^ 2577263718 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 12886318591) ^ 30 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_13322557151 : Nat.Prime 13322557151 := by
  apply lucas_primality 13322557151 (7 : ZMod 13322557151)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (71, 1), (97, 1), (5527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (71, 1), (97, 1), (5527, 1)] : List FactorBlock).map factorBlockValue).prod) = 13322557151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_71
      · exact prime_oneHundredSeventeenDK_97
      · exact prime_oneHundredSeventeenDK_5527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 13322557151) ^ 6661278575 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 13322557151) ^ 2664511430 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 13322557151) ^ 1903222450 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 13322557151) ^ 187641650 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 13322557151) ^ 137345950 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 13322557151) ^ 2410450 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_14477129489 : Nat.Prime 14477129489 := by
  apply lucas_primality 14477129489 (3 : ZMod 14477129489)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (904820593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (904820593, 1)] : List FactorBlock).map factorBlockValue).prod) = 14477129489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_904820593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 14477129489) ^ 7238564744 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 14477129489) ^ 16 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_15972754883 : Nat.Prime 15972754883 := by
  apply lucas_primality 15972754883 (2 : ZMod 15972754883)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1140911063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1140911063, 1)] : List FactorBlock).map factorBlockValue).prod) = 15972754883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_1140911063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 15972754883) ^ 7986377441 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 15972754883) ^ 2281822126 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 15972754883) ^ 14 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_17220763193 : Nat.Prime 17220763193 := by
  apply lucas_primality 17220763193 (3 : ZMod 17220763193)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (937, 1), (2297327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (937, 1), (2297327, 1)] : List FactorBlock).map factorBlockValue).prod) = 17220763193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_937
      · exact prime_oneHundredSeventeenDK_2297327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 17220763193) ^ 8610381596 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 17220763193) ^ 18378616 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 17220763193) ^ 7496 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_18309463891 : Nat.Prime 18309463891 := by
  apply lucas_primality 18309463891 (2 : ZMod 18309463891)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (41, 1), (14885743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (41, 1), (14885743, 1)] : List FactorBlock).map factorBlockValue).prod) = 18309463891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_41
      · exact prime_oneHundredSeventeenDK_14885743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18309463891) ^ 9154731945 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 18309463891) ^ 6103154630 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 18309463891) ^ 3661892778 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 18309463891) ^ 446572290 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 18309463891) ^ 1230 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_20095622483 : Nat.Prime 20095622483 := by
  apply lucas_primality 20095622483 (2 : ZMod 20095622483)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (772908557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (772908557, 1)] : List FactorBlock).map factorBlockValue).prod) = 20095622483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_13
      · exact prime_oneHundredSeventeenDK_772908557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 20095622483) ^ 10047811241 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 20095622483) ^ 1545817114 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 20095622483) ^ 26 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_22292713759 : Nat.Prime 22292713759 := by
  apply lucas_primality 22292713759 (7 : ZMod 22292713759)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (75825557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (75825557, 1)] : List FactorBlock).map factorBlockValue).prod) = 22292713759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_75825557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 22292713759) ^ 11146356879 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 22292713759) ^ 7430904586 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 22292713759) ^ 3184673394 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 22292713759) ^ 294 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_23046330287 : Nat.Prime 23046330287 := by
  apply lucas_primality 23046330287 (7 : ZMod 23046330287)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (173, 1), (1583, 1), (6011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (173, 1), (1583, 1), (6011, 1)] : List FactorBlock).map factorBlockValue).prod) = 23046330287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_173
      · exact prime_oneHundredSeventeenDK_1583
      · exact prime_oneHundredSeventeenDK_6011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 23046330287) ^ 11523165143 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 23046330287) ^ 3292332898 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 23046330287) ^ 133215782 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 23046330287) ^ 14558642 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 23046330287) ^ 3834026 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_24039012317 : Nat.Prime 24039012317 := by
  apply lucas_primality 24039012317 (2 : ZMod 24039012317)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (17, 1), (1231, 1), (26107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (17, 1), (1231, 1), (26107, 1)] : List FactorBlock).map factorBlockValue).prod) = 24039012317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_11
      · exact prime_oneHundredSeventeenDK_17
      · exact prime_oneHundredSeventeenDK_1231
      · exact prime_oneHundredSeventeenDK_26107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24039012317) ^ 12019506158 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 24039012317) ^ 2185364756 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 24039012317) ^ 1414059548 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 24039012317) ^ 19528036 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 24039012317) ^ 920788 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_25790344861 : Nat.Prime 25790344861 := by
  apply lucas_primality 25790344861 (2 : ZMod 25790344861)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (61405583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (61405583, 1)] : List FactorBlock).map factorBlockValue).prod) = 25790344861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_61405583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 25790344861) ^ 12895172430 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 25790344861) ^ 8596781620 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 25790344861) ^ 5158068972 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 25790344861) ^ 3684334980 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 25790344861) ^ 420 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_26001608891 : Nat.Prime 26001608891 := by
  apply lucas_primality 26001608891 (11 : ZMod 26001608891)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (563, 1), (4618403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (563, 1), (4618403, 1)] : List FactorBlock).map factorBlockValue).prod) = 26001608891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_563
      · exact prime_oneHundredSeventeenDK_4618403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 26001608891) ^ 13000804445 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 26001608891) ^ 5200321778 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 26001608891) ^ 46184030 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 26001608891) ^ 5630 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_26702345737 : Nat.Prime 26702345737 := by
  apply lucas_primality 26702345737 (5 : ZMod 26702345737)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (11, 1), (163, 1), (68947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (11, 1), (163, 1), (68947, 1)] : List FactorBlock).map factorBlockValue).prod) = 26702345737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_11
      · exact prime_oneHundredSeventeenDK_163
      · exact prime_oneHundredSeventeenDK_68947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 26702345737) ^ 13351172868 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 26702345737) ^ 8900781912 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 26702345737) ^ 2427485976 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 26702345737) ^ 163818072 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 26702345737) ^ 387288 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_27259443481 : Nat.Prime 27259443481 := by
  apply lucas_primality 27259443481 (17 : ZMod 27259443481)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (101, 1), (137, 1), (16417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (101, 1), (137, 1), (16417, 1)] : List FactorBlock).map factorBlockValue).prod) = 27259443481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_101
      · exact prime_oneHundredSeventeenDK_137
      · exact prime_oneHundredSeventeenDK_16417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 27259443481) ^ 13629721740 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (17 : ZMod 27259443481) ^ 9086481160 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (17 : ZMod 27259443481) ^ 5451888696 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (17 : ZMod 27259443481) ^ 269895480 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (17 : ZMod 27259443481) ^ 198974040 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (17 : ZMod 27259443481) ^ 1660440 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_34608107059 : Nat.Prime 34608107059 := by
  apply lucas_primality 34608107059 (2 : ZMod 34608107059)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (29, 2), (167, 1), (5867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (29, 2), (167, 1), (5867, 1)] : List FactorBlock).map factorBlockValue).prod) = 34608107059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_29
      · exact prime_oneHundredSeventeenDK_167
      · exact prime_oneHundredSeventeenDK_5867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 34608107059) ^ 17304053529 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 34608107059) ^ 11536035686 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 34608107059) ^ 4944015294 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 34608107059) ^ 1193383002 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 34608107059) ^ 207234174 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 34608107059) ^ 5898774 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_37339383437 : Nat.Prime 37339383437 := by
  apply lucas_primality 37339383437 (2 : ZMod 37339383437)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (163, 1), (57268993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (163, 1), (57268993, 1)] : List FactorBlock).map factorBlockValue).prod) = 37339383437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_163
      · exact prime_oneHundredSeventeenDK_57268993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 37339383437) ^ 18669691718 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 37339383437) ^ 229075972 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 37339383437) ^ 652 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_39508371347 : Nat.Prime 39508371347 := by
  apply lucas_primality 39508371347 (2 : ZMod 39508371347)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (367, 1), (53826119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (367, 1), (53826119, 1)] : List FactorBlock).map factorBlockValue).prod) = 39508371347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_367
      · exact prime_oneHundredSeventeenDK_53826119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 39508371347) ^ 19754185673 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 39508371347) ^ 107652238 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 39508371347) ^ 734 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_46333919623 : Nat.Prime 46333919623 := by
  apply lucas_primality 46333919623 (6 : ZMod 46333919623)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (72613, 1), (106349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (72613, 1), (106349, 1)] : List FactorBlock).map factorBlockValue).prod) = 46333919623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_72613
      · exact prime_oneHundredSeventeenDK_106349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 46333919623) ^ 23166959811 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 46333919623) ^ 15444639874 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 46333919623) ^ 638094 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 46333919623) ^ 435678 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_49190047217 : Nat.Prime 49190047217 := by
  apply lucas_primality 49190047217 (3 : ZMod 49190047217)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (17627, 1), (174413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (17627, 1), (174413, 1)] : List FactorBlock).map factorBlockValue).prod) = 49190047217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_17627
      · exact prime_oneHundredSeventeenDK_174413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 49190047217) ^ 24595023608 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 49190047217) ^ 2790608 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 49190047217) ^ 282032 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_49476689651 : Nat.Prime 49476689651 := by
  apply lucas_primality 49476689651 (2 : ZMod 49476689651)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (989533793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (989533793, 1)] : List FactorBlock).map factorBlockValue).prod) = 49476689651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_989533793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 49476689651) ^ 24738344825 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 49476689651) ^ 9895337930 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 49476689651) ^ 50 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_59130884849 : Nat.Prime 59130884849 := by
  apply lucas_primality 59130884849 (3 : ZMod 59130884849)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 2), (17, 1), (61, 1), (257, 1), (283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 2), (17, 1), (61, 1), (257, 1), (283, 1)] : List FactorBlock).map factorBlockValue).prod) = 59130884849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_17
      · exact prime_oneHundredSeventeenDK_61
      · exact prime_oneHundredSeventeenDK_257
      · exact prime_oneHundredSeventeenDK_283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 59130884849) ^ 29565442424 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 59130884849) ^ 8447269264 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 59130884849) ^ 3478287344 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 59130884849) ^ 969358768 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 59130884849) ^ 230081264 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 59130884849) ^ 208943056 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_70764736103 : Nat.Prime 70764736103 := by
  apply lucas_primality 70764736103 (5 : ZMod 70764736103)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (317, 1), (111616303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (317, 1), (111616303, 1)] : List FactorBlock).map factorBlockValue).prod) = 70764736103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_317
      · exact prime_oneHundredSeventeenDK_111616303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 70764736103) ^ 35382368051 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 70764736103) ^ 223232606 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 70764736103) ^ 634 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_80770263887 : Nat.Prime 80770263887 := by
  apply lucas_primality 80770263887 (5 : ZMod 80770263887)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (13313, 1), (233347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (13313, 1), (233347, 1)] : List FactorBlock).map factorBlockValue).prod) = 80770263887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_13
      · exact prime_oneHundredSeventeenDK_13313
      · exact prime_oneHundredSeventeenDK_233347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 80770263887) ^ 40385131943 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 80770263887) ^ 6213097222 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 80770263887) ^ 6067022 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 80770263887) ^ 346138 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_85208399431 : Nat.Prime 85208399431 := by
  apply lucas_primality 85208399431 (6 : ZMod 85208399431)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (17, 1), (29, 1), (74821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (17, 1), (29, 1), (74821, 1)] : List FactorBlock).map factorBlockValue).prod) = 85208399431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_11
      · exact prime_oneHundredSeventeenDK_17
      · exact prime_oneHundredSeventeenDK_29
      · exact prime_oneHundredSeventeenDK_74821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 85208399431) ^ 42604199715 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 85208399431) ^ 28402799810 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 85208399431) ^ 17041679886 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 85208399431) ^ 12172628490 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 85208399431) ^ 7746218130 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 85208399431) ^ 5012258790 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 85208399431) ^ 2938220670 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 85208399431) ^ 1138830 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_95329096367 : Nat.Prime 95329096367 := by
  apply lucas_primality 95329096367 (5 : ZMod 95329096367)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (163, 1), (41774363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (163, 1), (41774363, 1)] : List FactorBlock).map factorBlockValue).prod) = 95329096367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_163
      · exact prime_oneHundredSeventeenDK_41774363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 95329096367) ^ 47664548183 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 95329096367) ^ 13618442338 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 95329096367) ^ 584841082 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 95329096367) ^ 2282 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_97871859109 : Nat.Prime 97871859109 := by
  apply lucas_primality 97871859109 (2 : ZMod 97871859109)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (101, 1), (307, 1), (87679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (101, 1), (307, 1), (87679, 1)] : List FactorBlock).map factorBlockValue).prod) = 97871859109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_101
      · exact prime_oneHundredSeventeenDK_307
      · exact prime_oneHundredSeventeenDK_87679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 97871859109) ^ 48935929554 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 97871859109) ^ 32623953036 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 97871859109) ^ 969028308 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 97871859109) ^ 318800844 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 97871859109) ^ 1116252 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_115669499017 : Nat.Prime 115669499017 := by
  apply lucas_primality 115669499017 (15 : ZMod 115669499017)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (401, 1), (2693, 1), (4463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (401, 1), (2693, 1), (4463, 1)] : List FactorBlock).map factorBlockValue).prod) = 115669499017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_401
      · exact prime_oneHundredSeventeenDK_2693
      · exact prime_oneHundredSeventeenDK_4463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 115669499017) ^ 57834749508 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (15 : ZMod 115669499017) ^ 38556499672 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (15 : ZMod 115669499017) ^ 288452616 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (15 : ZMod 115669499017) ^ 42951912 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (15 : ZMod 115669499017) ^ 25917432 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_118662433481 : Nat.Prime 118662433481 := by
  apply lucas_primality 118662433481 (6 : ZMod 118662433481)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (71, 1), (79, 1), (263, 1), (2011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (71, 1), (79, 1), (263, 1), (2011, 1)] : List FactorBlock).map factorBlockValue).prod) = 118662433481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_71
      · exact prime_oneHundredSeventeenDK_79
      · exact prime_oneHundredSeventeenDK_263
      · exact prime_oneHundredSeventeenDK_2011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 118662433481) ^ 59331216740 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 118662433481) ^ 23732486696 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 118662433481) ^ 1671301880 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 118662433481) ^ 1502056120 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 118662433481) ^ 451187960 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 118662433481) ^ 59006680 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_167008481483 : Nat.Prime 167008481483 := by
  apply lucas_primality 167008481483 (5 : ZMod 167008481483)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (43, 1), (102208373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (43, 1), (102208373, 1)] : List FactorBlock).map factorBlockValue).prod) = 167008481483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_19
      · exact prime_oneHundredSeventeenDK_43
      · exact prime_oneHundredSeventeenDK_102208373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 167008481483) ^ 83504240741 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 167008481483) ^ 8789920078 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 167008481483) ^ 3883918174 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 167008481483) ^ 1634 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_169551237041 : Nat.Prime 169551237041 := by
  apply lucas_primality 169551237041 (3 : ZMod 169551237041)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (401, 1), (5285263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (401, 1), (5285263, 1)] : List FactorBlock).map factorBlockValue).prod) = 169551237041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_401
      · exact prime_oneHundredSeventeenDK_5285263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 169551237041) ^ 84775618520 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 169551237041) ^ 33910247408 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 169551237041) ^ 422821040 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 169551237041) ^ 32080 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_199487547151 : Nat.Prime 199487547151 := by
  apply lucas_primality 199487547151 (3 : ZMod 199487547151)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (1329916981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (1329916981, 1)] : List FactorBlock).map factorBlockValue).prod) = 199487547151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_1329916981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 199487547151) ^ 99743773575 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 199487547151) ^ 66495849050 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 199487547151) ^ 39897509430 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 199487547151) ^ 150 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_243364641461 : Nat.Prime 243364641461 := by
  apply lucas_primality 243364641461 (2 : ZMod 243364641461)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) = 243364641461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_19
      · exact prime_oneHundredSeventeenDK_640433267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 243364641461) ^ 121682320730 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 48672928292 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 12808665340 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 380 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_308181357101 : Nat.Prime 308181357101 := by
  apply lucas_primality 308181357101 (2 : ZMod 308181357101)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (31, 1), (109, 1), (912049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (31, 1), (109, 1), (912049, 1)] : List FactorBlock).map factorBlockValue).prod) = 308181357101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_31
      · exact prime_oneHundredSeventeenDK_109
      · exact prime_oneHundredSeventeenDK_912049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 308181357101) ^ 154090678550 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 308181357101) ^ 61636271420 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 308181357101) ^ 9941334100 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 308181357101) ^ 2827351900 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 308181357101) ^ 337900 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_364603809013 : Nat.Prime 364603809013 := by
  apply lucas_primality 364603809013 (2 : ZMod 364603809013)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (281, 1), (9551, 1), (11321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (281, 1), (9551, 1), (11321, 1)] : List FactorBlock).map factorBlockValue).prod) = 364603809013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_281
      · exact prime_oneHundredSeventeenDK_9551
      · exact prime_oneHundredSeventeenDK_11321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 364603809013) ^ 182301904506 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 364603809013) ^ 121534603004 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 364603809013) ^ 1297522452 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 364603809013) ^ 38174412 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 364603809013) ^ 32205972 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_368666113003 : Nat.Prime 368666113003 := by
  apply lucas_primality 368666113003 (2 : ZMod 368666113003)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (193, 1), (347, 1), (83407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (193, 1), (347, 1), (83407, 1)] : List FactorBlock).map factorBlockValue).prod) = 368666113003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_11
      · exact prime_oneHundredSeventeenDK_193
      · exact prime_oneHundredSeventeenDK_347
      · exact prime_oneHundredSeventeenDK_83407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 368666113003) ^ 184333056501 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 368666113003) ^ 122888704334 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 368666113003) ^ 33515101182 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 368666113003) ^ 1910187114 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 368666113003) ^ 1062438366 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 368666113003) ^ 4420086 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_381546518033 : Nat.Prime 381546518033 := by
  apply lucas_primality 381546518033 (3 : ZMod 381546518033)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (233, 1), (102346169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (233, 1), (102346169, 1)] : List FactorBlock).map factorBlockValue).prod) = 381546518033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_233
      · exact prime_oneHundredSeventeenDK_102346169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 381546518033) ^ 190773259016 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 381546518033) ^ 1637538704 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 381546518033) ^ 3728 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_462677996069 : Nat.Prime 462677996069 := by
  apply lucas_primality 462677996069 (2 : ZMod 462677996069)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (115669499017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (115669499017, 1)] : List FactorBlock).map factorBlockValue).prod) = 462677996069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_115669499017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 462677996069) ^ 231338998034 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 462677996069) ^ 4 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_520830452771 : Nat.Prime 520830452771 := by
  apply lucas_primality 520830452771 (2 : ZMod 520830452771)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (39079, 1), (1332763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (39079, 1), (1332763, 1)] : List FactorBlock).map factorBlockValue).prod) = 520830452771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_39079
      · exact prime_oneHundredSeventeenDK_1332763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 520830452771) ^ 260415226385 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 520830452771) ^ 104166090554 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 520830452771) ^ 13327630 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 520830452771) ^ 390790 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_607515741979 : Nat.Prime 607515741979 := by
  apply lucas_primality 607515741979 (2 : ZMod 607515741979)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (67, 1), (1733, 1), (872033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (67, 1), (1733, 1), (872033, 1)] : List FactorBlock).map factorBlockValue).prod) = 607515741979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_67
      · exact prime_oneHundredSeventeenDK_1733
      · exact prime_oneHundredSeventeenDK_872033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 607515741979) ^ 303757870989 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 607515741979) ^ 202505247326 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 607515741979) ^ 9067399134 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 607515741979) ^ 350557266 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 607515741979) ^ 696666 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_625014320243 : Nat.Prime 625014320243 := by
  apply lucas_primality 625014320243 (2 : ZMod 625014320243)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (24039012317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (24039012317, 1)] : List FactorBlock).map factorBlockValue).prod) = 625014320243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_13
      · exact prime_oneHundredSeventeenDK_24039012317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 625014320243) ^ 312507160121 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 625014320243) ^ 48078024634 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 625014320243) ^ 26 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_983800944341 : Nat.Prime 983800944341 := by
  apply lucas_primality 983800944341 (2 : ZMod 983800944341)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (49190047217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (49190047217, 1)] : List FactorBlock).map factorBlockValue).prod) = 983800944341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_49190047217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 983800944341) ^ 491900472170 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 983800944341) ^ 196760188868 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 983800944341) ^ 20 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_1213579343059 : Nat.Prime 1213579343059 := by
  apply lucas_primality 1213579343059 (3 : ZMod 1213579343059)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (167, 1), (1211157029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (167, 1), (1211157029, 1)] : List FactorBlock).map factorBlockValue).prod) = 1213579343059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_167
      · exact prime_oneHundredSeventeenDK_1211157029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1213579343059) ^ 606789671529 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1213579343059) ^ 404526447686 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1213579343059) ^ 7266942174 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1213579343059) ^ 1002 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_1465208853187 : Nat.Prime 1465208853187 := by
  apply lucas_primality 1465208853187 (2 : ZMod 1465208853187)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (131, 1), (479, 1), (299363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (131, 1), (479, 1), (299363, 1)] : List FactorBlock).map factorBlockValue).prod) = 1465208853187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_13
      · exact prime_oneHundredSeventeenDK_131
      · exact prime_oneHundredSeventeenDK_479
      · exact prime_oneHundredSeventeenDK_299363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1465208853187) ^ 732604426593 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1465208853187) ^ 488402951062 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1465208853187) ^ 112708373322 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1465208853187) ^ 11184800406 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1465208853187) ^ 3058891134 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1465208853187) ^ 4894422 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_1564506913061 : Nat.Prime 1564506913061 := by
  apply lucas_primality 1564506913061 (2 : ZMod 1564506913061)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (13, 1), (281, 1), (3059143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (13, 1), (281, 1), (3059143, 1)] : List FactorBlock).map factorBlockValue).prod) = 1564506913061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_13
      · exact prime_oneHundredSeventeenDK_281
      · exact prime_oneHundredSeventeenDK_3059143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1564506913061) ^ 782253456530 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1564506913061) ^ 312901382612 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1564506913061) ^ 223500987580 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1564506913061) ^ 120346685620 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1564506913061) ^ 5567640260 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1564506913061) ^ 511420 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_1597500646127 : Nat.Prime 1597500646127 := by
  apply lucas_primality 1597500646127 (10 : ZMod 1597500646127)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (10373380819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (10373380819, 1)] : List FactorBlock).map factorBlockValue).prod) = 1597500646127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_11
      · exact prime_oneHundredSeventeenDK_10373380819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 1597500646127) ^ 798750323063 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (10 : ZMod 1597500646127) ^ 228214378018 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (10 : ZMod 1597500646127) ^ 145227331466 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (10 : ZMod 1597500646127) ^ 154 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_2437902708193 : Nat.Prime 2437902708193 := by
  apply lucas_primality 2437902708193 (15 : ZMod 2437902708193)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (7, 1), (19183, 1), (21013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (7, 1), (19183, 1), (21013, 1)] : List FactorBlock).map factorBlockValue).prod) = 2437902708193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_19183
      · exact prime_oneHundredSeventeenDK_21013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 2437902708193) ^ 1218951354096 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (15 : ZMod 2437902708193) ^ 812634236064 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (15 : ZMod 2437902708193) ^ 348271815456 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (15 : ZMod 2437902708193) ^ 127086624 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (15 : ZMod 2437902708193) ^ 116018784 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_2676546708113 : Nat.Prime 2676546708113 := by
  apply lucas_primality 2676546708113 (3 : ZMod 2676546708113)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (107, 1), (28729, 1), (54419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (107, 1), (28729, 1), (54419, 1)] : List FactorBlock).map factorBlockValue).prod) = 2676546708113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_107
      · exact prime_oneHundredSeventeenDK_28729
      · exact prime_oneHundredSeventeenDK_54419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2676546708113) ^ 1338273354056 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2676546708113) ^ 25014455216 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2676546708113) ^ 93165328 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2676546708113) ^ 49184048 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_3662228970263 : Nat.Prime 3662228970263 := by
  apply lucas_primality 3662228970263 (5 : ZMod 3662228970263)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (25790344861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (25790344861, 1)] : List FactorBlock).map factorBlockValue).prod) = 3662228970263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_71
      · exact prime_oneHundredSeventeenDK_25790344861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3662228970263) ^ 1831114485131 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 3662228970263) ^ 51580689722 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 3662228970263) ^ 142 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_3687111941479 : Nat.Prime 3687111941479 := by
  apply lucas_primality 3687111941479 (3 : ZMod 3687111941479)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (17, 1), (37, 1), (139568171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (17, 1), (37, 1), (139568171, 1)] : List FactorBlock).map factorBlockValue).prod) = 3687111941479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_17
      · exact prime_oneHundredSeventeenDK_37
      · exact prime_oneHundredSeventeenDK_139568171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3687111941479) ^ 1843555970739 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687111941479) ^ 1229037313826 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687111941479) ^ 526730277354 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687111941479) ^ 216888937734 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687111941479) ^ 99651674094 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687111941479) ^ 26418 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_4067900353939 : Nat.Prime 4067900353939 := by
  apply lucas_primality 4067900353939 (3 : ZMod 4067900353939)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (263, 1), (151640213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (263, 1), (151640213, 1)] : List FactorBlock).map factorBlockValue).prod) = 4067900353939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_17
      · exact prime_oneHundredSeventeenDK_263
      · exact prime_oneHundredSeventeenDK_151640213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4067900353939) ^ 2033950176969 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 4067900353939) ^ 1355966784646 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 4067900353939) ^ 239288256114 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 4067900353939) ^ 15467301726 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 4067900353939) ^ 26826 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_4857613868521 : Nat.Prime 4857613868521 := by
  apply lucas_primality 4857613868521 (31 : ZMod 4857613868521)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (7, 1), (7949, 1), (80833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (7, 1), (7949, 1), (80833, 1)] : List FactorBlock).map factorBlockValue).prod) = 4857613868521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_7949
      · exact prime_oneHundredSeventeenDK_80833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 4857613868521) ^ 2428806934260 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (31 : ZMod 4857613868521) ^ 1619204622840 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (31 : ZMod 4857613868521) ^ 971522773704 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (31 : ZMod 4857613868521) ^ 693944838360 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (31 : ZMod 4857613868521) ^ 611097480 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (31 : ZMod 4857613868521) ^ 60094440 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_9050402962151 : Nat.Prime 9050402962151 := by
  apply lucas_primality 9050402962151 (11 : ZMod 9050402962151)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (11, 1), (31, 1), (127, 1), (4179649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (11, 1), (31, 1), (127, 1), (4179649, 1)] : List FactorBlock).map factorBlockValue).prod) = 9050402962151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_11
      · exact prime_oneHundredSeventeenDK_31
      · exact prime_oneHundredSeventeenDK_127
      · exact prime_oneHundredSeventeenDK_4179649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 9050402962151) ^ 4525201481075 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 9050402962151) ^ 1810080592430 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 9050402962151) ^ 822763905650 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 9050402962151) ^ 291948482650 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 9050402962151) ^ 71263015450 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 9050402962151) ^ 2165350 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_13409142180199 : Nat.Prime 13409142180199 := by
  apply lucas_primality 13409142180199 (3 : ZMod 13409142180199)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (113, 1), (106627, 1), (185483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (113, 1), (106627, 1), (185483, 1)] : List FactorBlock).map factorBlockValue).prod) = 13409142180199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_113
      · exact prime_oneHundredSeventeenDK_106627
      · exact prime_oneHundredSeventeenDK_185483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13409142180199) ^ 6704571090099 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 13409142180199) ^ 4469714060066 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 13409142180199) ^ 118664975046 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 13409142180199) ^ 125757474 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 13409142180199) ^ 72293106 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_13996320415397 : Nat.Prime 13996320415397 := by
  apply lucas_primality 13996320415397 (2 : ZMod 13996320415397)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (229, 1), (1389075071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (229, 1), (1389075071, 1)] : List FactorBlock).map factorBlockValue).prod) = 13996320415397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_11
      · exact prime_oneHundredSeventeenDK_229
      · exact prime_oneHundredSeventeenDK_1389075071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13996320415397) ^ 6998160207698 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 13996320415397) ^ 1272392765036 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 13996320415397) ^ 61119303124 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 13996320415397) ^ 10076 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_14305552217941 : Nat.Prime 14305552217941 := by
  apply lucas_primality 14305552217941 (2 : ZMod 14305552217941)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (6427, 1), (37097537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (6427, 1), (37097537, 1)] : List FactorBlock).map factorBlockValue).prod) = 14305552217941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_6427
      · exact prime_oneHundredSeventeenDK_37097537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14305552217941) ^ 7152776108970 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 14305552217941) ^ 4768517405980 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 14305552217941) ^ 2861110443588 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 14305552217941) ^ 2225852220 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 14305552217941) ^ 385620 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_18100805924303 : Nat.Prime 18100805924303 := by
  apply lucas_primality 18100805924303 (5 : ZMod 18100805924303)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (9050402962151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (9050402962151, 1)] : List FactorBlock).map factorBlockValue).prod) = 18100805924303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_9050402962151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 18100805924303) ^ 9050402962151 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 18100805924303) ^ 2 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_19211985866123 : Nat.Prime 19211985866123 := by
  apply lucas_primality 19211985866123 (2 : ZMod 19211985866123)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (47, 1), (1613, 1), (18101393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (47, 1), (1613, 1), (18101393, 1)] : List FactorBlock).map factorBlockValue).prod) = 19211985866123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_47
      · exact prime_oneHundredSeventeenDK_1613
      · exact prime_oneHundredSeventeenDK_18101393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 19211985866123) ^ 9605992933061 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 19211985866123) ^ 2744569409446 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 19211985866123) ^ 408765656726 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 19211985866123) ^ 11910716594 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 19211985866123) ^ 1061354 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_26184934309609 : Nat.Prime 26184934309609 := by
  apply lucas_primality 26184934309609 (14 : ZMod 26184934309609)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (773, 1), (5519, 1), (85247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (773, 1), (5519, 1), (85247, 1)] : List FactorBlock).map factorBlockValue).prod) = 26184934309609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_773
      · exact prime_oneHundredSeventeenDK_5519
      · exact prime_oneHundredSeventeenDK_85247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 26184934309609) ^ 13092467154804 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (14 : ZMod 26184934309609) ^ 8728311436536 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (14 : ZMod 26184934309609) ^ 33874429896 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (14 : ZMod 26184934309609) ^ 4744507032 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (14 : ZMod 26184934309609) ^ 307165464 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_27663524209333 : Nat.Prime 27663524209333 := by
  apply lucas_primality 27663524209333 (2 : ZMod 27663524209333)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (11, 1), (29, 1), (1607, 1), (499663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (11, 1), (29, 1), (1607, 1), (499663, 1)] : List FactorBlock).map factorBlockValue).prod) = 27663524209333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_11
      · exact prime_oneHundredSeventeenDK_29
      · exact prime_oneHundredSeventeenDK_1607
      · exact prime_oneHundredSeventeenDK_499663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 27663524209333) ^ 13831762104666 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 27663524209333) ^ 9221174736444 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 27663524209333) ^ 2514865837212 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 27663524209333) ^ 953914627908 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 27663524209333) ^ 17214389676 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 27663524209333) ^ 55364364 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_27920119256221 : Nat.Prime 27920119256221 := by
  apply lucas_primality 27920119256221 (7 : ZMod 27920119256221)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (631, 1), (797, 1), (925291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (631, 1), (797, 1), (925291, 1)] : List FactorBlock).map factorBlockValue).prod) = 27920119256221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_631
      · exact prime_oneHundredSeventeenDK_797
      · exact prime_oneHundredSeventeenDK_925291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 27920119256221) ^ 13960059628110 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 27920119256221) ^ 9306706418740 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 27920119256221) ^ 5584023851244 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 27920119256221) ^ 44247415620 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 27920119256221) ^ 35031517260 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 27920119256221) ^ 30174420 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_29816700622001 : Nat.Prime 29816700622001 := by
  apply lucas_primality 29816700622001 (6 : ZMod 29816700622001)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 3), (17, 1), (353, 1), (2484311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 3), (17, 1), (353, 1), (2484311, 1)] : List FactorBlock).map factorBlockValue).prod) = 29816700622001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_17
      · exact prime_oneHundredSeventeenDK_353
      · exact prime_oneHundredSeventeenDK_2484311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 29816700622001) ^ 14908350311000 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 29816700622001) ^ 5963340124400 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 29816700622001) ^ 1753923566000 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 29816700622001) ^ 84466574000 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 29816700622001) ^ 12002000 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_32547242434771 : Nat.Prime 32547242434771 := by
  apply lucas_primality 32547242434771 (3 : ZMod 32547242434771)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (7, 1), (17220763193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (7, 1), (17220763193, 1)] : List FactorBlock).map factorBlockValue).prod) = 32547242434771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_17220763193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 32547242434771) ^ 16273621217385 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 32547242434771) ^ 10849080811590 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 32547242434771) ^ 6509448486954 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 32547242434771) ^ 4649606062110 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 32547242434771) ^ 1890 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_33312673606897 : Nat.Prime 33312673606897 := by
  apply lucas_primality 33312673606897 (7 : ZMod 33312673606897)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (31, 1), (151, 2), (327289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (31, 1), (151, 2), (327289, 1)] : List FactorBlock).map factorBlockValue).prod) = 33312673606897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_31
      · exact prime_oneHundredSeventeenDK_151
      · exact prime_oneHundredSeventeenDK_327289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 33312673606897) ^ 16656336803448 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 33312673606897) ^ 11104224535632 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 33312673606897) ^ 1074602374416 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 33312673606897) ^ 220613732496 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 33312673606897) ^ 101783664 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_43994722243573 : Nat.Prime 43994722243573 := by
  apply lucas_primality 43994722243573 (2 : ZMod 43994722243573)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (47, 1), (26001608891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (47, 1), (26001608891, 1)] : List FactorBlock).map factorBlockValue).prod) = 43994722243573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_47
      · exact prime_oneHundredSeventeenDK_26001608891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 43994722243573) ^ 21997361121786 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 43994722243573) ^ 14664907414524 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 43994722243573) ^ 936057920076 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 43994722243573) ^ 1692 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_45752552594669 : Nat.Prime 45752552594669 := by
  apply lucas_primality 45752552594669 (2 : ZMod 45752552594669)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) = 45752552594669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_47
      · exact prime_oneHundredSeventeenDK_243364641461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 45752552594669) ^ 22876276297334 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 973458565844 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 188 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_51350336634101 : Nat.Prime 51350336634101 := by
  apply lucas_primality 51350336634101 (2 : ZMod 51350336634101)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 1), (17, 1), (4315154339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 1), (17, 1), (4315154339, 1)] : List FactorBlock).map factorBlockValue).prod) = 51350336634101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_17
      · exact prime_oneHundredSeventeenDK_4315154339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 51350336634101) ^ 25675168317050 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 51350336634101) ^ 10270067326820 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 51350336634101) ^ 7335762376300 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 51350336634101) ^ 3020608037300 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 51350336634101) ^ 11900 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_56138634761201 : Nat.Prime 56138634761201 := by
  apply lucas_primality 56138634761201 (3 : ZMod 56138634761201)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (241, 1), (2963, 1), (196541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (241, 1), (2963, 1), (196541, 1)] : List FactorBlock).map factorBlockValue).prod) = 56138634761201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_241
      · exact prime_oneHundredSeventeenDK_2963
      · exact prime_oneHundredSeventeenDK_196541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 56138634761201) ^ 28069317380600 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 56138634761201) ^ 11227726952240 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 56138634761201) ^ 232940393200 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 56138634761201) ^ 18946552400 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 56138634761201) ^ 285633200 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_75985136210957 : Nat.Prime 75985136210957 := by
  apply lucas_primality 75985136210957 (2 : ZMod 75985136210957)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (89, 1), (66791, 1), (456523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (89, 1), (66791, 1), (456523, 1)] : List FactorBlock).map factorBlockValue).prod) = 75985136210957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_89
      · exact prime_oneHundredSeventeenDK_66791
      · exact prime_oneHundredSeventeenDK_456523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 75985136210957) ^ 37992568105478 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 75985136210957) ^ 10855019458708 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 75985136210957) ^ 853765575404 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 75985136210957) ^ 1137655316 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 75985136210957) ^ 166443172 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_78086914741933 : Nat.Prime 78086914741933 := by
  apply lucas_primality 78086914741933 (2 : ZMod 78086914741933)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (103, 1), (3716300911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (103, 1), (3716300911, 1)] : List FactorBlock).map factorBlockValue).prod) = 78086914741933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_17
      · exact prime_oneHundredSeventeenDK_103
      · exact prime_oneHundredSeventeenDK_3716300911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 78086914741933) ^ 39043457370966 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 78086914741933) ^ 26028971580644 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 78086914741933) ^ 4593347925996 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 78086914741933) ^ 758125385844 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 78086914741933) ^ 21012 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_113993486613649 : Nat.Prime 113993486613649 := by
  apply lucas_primality 113993486613649 (7 : ZMod 113993486613649)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (19, 1), (317, 1), (131433079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (19, 1), (317, 1), (131433079, 1)] : List FactorBlock).map factorBlockValue).prod) = 113993486613649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_19
      · exact prime_oneHundredSeventeenDK_317
      · exact prime_oneHundredSeventeenDK_131433079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 113993486613649) ^ 56996743306824 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 113993486613649) ^ 37997828871216 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 113993486613649) ^ 5999657190192 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 113993486613649) ^ 359600904144 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 113993486613649) ^ 867312 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_115342509540833 : Nat.Prime 115342509540833 := by
  apply lucas_primality 115342509540833 (3 : ZMod 115342509540833)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (2777, 1), (185423809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (2777, 1), (185423809, 1)] : List FactorBlock).map factorBlockValue).prod) = 115342509540833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_2777
      · exact prime_oneHundredSeventeenDK_185423809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 115342509540833) ^ 57671254770416 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 115342509540833) ^ 16477501362976 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 115342509540833) ^ 41534933216 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 115342509540833) ^ 622048 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_153219463591079 : Nat.Prime 153219463591079 := by
  apply lucas_primality 153219463591079 (7 : ZMod 153219463591079)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (151, 1), (197, 1), (1747, 1), (1474171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (151, 1), (197, 1), (1747, 1), (1474171, 1)] : List FactorBlock).map factorBlockValue).prod) = 153219463591079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_151
      · exact prime_oneHundredSeventeenDK_197
      · exact prime_oneHundredSeventeenDK_1747
      · exact prime_oneHundredSeventeenDK_1474171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 153219463591079) ^ 76609731795539 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 153219463591079) ^ 1014698434378 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 153219463591079) ^ 777763774574 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 153219463591079) ^ 87704329474 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 153219463591079) ^ 103936018 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_187612731501289 : Nat.Prime 187612731501289 := by
  apply lucas_primality 187612731501289 (7 : ZMod 187612731501289)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (389, 1), (20095622483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (389, 1), (20095622483, 1)] : List FactorBlock).map factorBlockValue).prod) = 187612731501289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_389
      · exact prime_oneHundredSeventeenDK_20095622483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 187612731501289) ^ 93806365750644 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 187612731501289) ^ 62537577167096 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 187612731501289) ^ 482294939592 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 187612731501289) ^ 9336 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_267494201311979 : Nat.Prime 267494201311979 := by
  apply lucas_primality 267494201311979 (6 : ZMod 267494201311979)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (97, 1), (107, 1), (12886318591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (97, 1), (107, 1), (12886318591, 1)] : List FactorBlock).map factorBlockValue).prod) = 267494201311979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_97
      · exact prime_oneHundredSeventeenDK_107
      · exact prime_oneHundredSeventeenDK_12886318591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 267494201311979) ^ 133747100655989 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 267494201311979) ^ 2757672178474 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 267494201311979) ^ 2499945806654 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 267494201311979) ^ 20758 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_327173442757709 : Nat.Prime 327173442757709 := by
  apply lucas_primality 327173442757709 (2 : ZMod 327173442757709)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (6521, 1), (12543070187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (6521, 1), (12543070187, 1)] : List FactorBlock).map factorBlockValue).prod) = 327173442757709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_6521
      · exact prime_oneHundredSeventeenDK_12543070187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 327173442757709) ^ 163586721378854 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 327173442757709) ^ 50172280748 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 327173442757709) ^ 26084 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_366020420757353 : Nat.Prime 366020420757353 := by
  apply lucas_primality 366020420757353 (3 : ZMod 366020420757353)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) = 366020420757353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_45752552594669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 366020420757353) ^ 183010210378676 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 366020420757353) ^ 8 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_381185991510433 : Nat.Prime 381185991510433 := by
  apply lucas_primality 381185991510433 (5 : ZMod 381185991510433)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (937, 1), (4237659991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (937, 1), (4237659991, 1)] : List FactorBlock).map factorBlockValue).prod) = 381185991510433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_937
      · exact prime_oneHundredSeventeenDK_4237659991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 381185991510433) ^ 190592995755216 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 381185991510433) ^ 127061997170144 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 381185991510433) ^ 406815359136 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 381185991510433) ^ 89952 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_400875657510611 : Nat.Prime 400875657510611 := by
  apply lucas_primality 400875657510611 (2 : ZMod 400875657510611)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (10163, 1), (3944461847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (10163, 1), (3944461847, 1)] : List FactorBlock).map factorBlockValue).prod) = 400875657510611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_10163
      · exact prime_oneHundredSeventeenDK_3944461847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 400875657510611) ^ 200437828755305 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 400875657510611) ^ 80175131502122 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 400875657510611) ^ 39444618470 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 400875657510611) ^ 101630 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_797799947097187 : Nat.Prime 797799947097187 := by
  apply lucas_primality 797799947097187 (5 : ZMod 797799947097187)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (797, 1), (5055574231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (797, 1), (5055574231, 1)] : List FactorBlock).map factorBlockValue).prod) = 797799947097187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_11
      · exact prime_oneHundredSeventeenDK_797
      · exact prime_oneHundredSeventeenDK_5055574231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 797799947097187) ^ 398899973548593 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 797799947097187) ^ 265933315699062 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 797799947097187) ^ 72527267917926 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 797799947097187) ^ 1001003697738 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 797799947097187) ^ 157806 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_810117218002061 : Nat.Prime 810117218002061 := by
  apply lucas_primality 810117218002061 (2 : ZMod 810117218002061)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (23, 1), (79, 1), (22292713759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (23, 1), (79, 1), (22292713759, 1)] : List FactorBlock).map factorBlockValue).prod) = 810117218002061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_23
      · exact prime_oneHundredSeventeenDK_79
      · exact prime_oneHundredSeventeenDK_22292713759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 810117218002061) ^ 405058609001030 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 810117218002061) ^ 162023443600412 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 810117218002061) ^ 35222487739220 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 810117218002061) ^ 10254648329140 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 810117218002061) ^ 36340 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_829722028640579 : Nat.Prime 829722028640579 := by
  apply lucas_primality 829722028640579 (2 : ZMod 829722028640579)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (14305552217941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (14305552217941, 1)] : List FactorBlock).map factorBlockValue).prod) = 829722028640579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_29
      · exact prime_oneHundredSeventeenDK_14305552217941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 829722028640579) ^ 414861014320289 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 829722028640579) ^ 28611104435882 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 829722028640579) ^ 58 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_1006897964662531 : Nat.Prime 1006897964662531 := by
  apply lucas_primality 1006897964662531 (13 : ZMod 1006897964662531)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (59, 1), (1117, 1), (169760939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (59, 1), (1117, 1), (169760939, 1)] : List FactorBlock).map factorBlockValue).prod) = 1006897964662531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_59
      · exact prime_oneHundredSeventeenDK_1117
      · exact prime_oneHundredSeventeenDK_169760939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 1006897964662531) ^ 503448982331265 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (13 : ZMod 1006897964662531) ^ 335632654887510 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (13 : ZMod 1006897964662531) ^ 201379592932506 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (13 : ZMod 1006897964662531) ^ 17066067197670 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (13 : ZMod 1006897964662531) ^ 901430586090 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (13 : ZMod 1006897964662531) ^ 5931270 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_1034958593446733 : Nat.Prime 1034958593446733 := by
  apply lucas_primality 1034958593446733 (2 : ZMod 1034958593446733)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (263, 1), (983800944341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (263, 1), (983800944341, 1)] : List FactorBlock).map factorBlockValue).prod) = 1034958593446733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_263
      · exact prime_oneHundredSeventeenDK_983800944341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1034958593446733) ^ 517479296723366 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1034958593446733) ^ 3935203777364 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1034958593446733) ^ 1052 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_1187826903350189 : Nat.Prime 1187826903350189 := by
  apply lucas_primality 1187826903350189 (2 : ZMod 1187826903350189)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (73, 1), (4067900353939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (73, 1), (4067900353939, 1)] : List FactorBlock).map factorBlockValue).prod) = 1187826903350189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_73
      · exact prime_oneHundredSeventeenDK_4067900353939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1187826903350189) ^ 593913451675094 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1187826903350189) ^ 16271601415756 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1187826903350189) ^ 292 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_1452722104942727 : Nat.Prime 1452722104942727 := by
  apply lucas_primality 1452722104942727 (5 : ZMod 1452722104942727)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (197, 1), (3687111941479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (197, 1), (3687111941479, 1)] : List FactorBlock).map factorBlockValue).prod) = 1452722104942727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_197
      · exact prime_oneHundredSeventeenDK_3687111941479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1452722104942727) ^ 726361052471363 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1452722104942727) ^ 7374223882958 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1452722104942727) ^ 394 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_1789103977804019 : Nat.Prime 1789103977804019 := by
  apply lucas_primality 1789103977804019 (2 : ZMod 1789103977804019)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (947, 1), (121721, 1), (7760507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (947, 1), (121721, 1), (7760507, 1)] : List FactorBlock).map factorBlockValue).prod) = 1789103977804019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_947
      · exact prime_oneHundredSeventeenDK_121721
      · exact prime_oneHundredSeventeenDK_7760507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1789103977804019) ^ 894551988902009 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1789103977804019) ^ 1889233345094 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1789103977804019) ^ 14698400258 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1789103977804019) ^ 230539574 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_1976029373590001 : Nat.Prime 1976029373590001 := by
  apply lucas_primality 1976029373590001 (3 : ZMod 1976029373590001)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 4), (137, 1), (433, 1), (3331079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 4), (137, 1), (433, 1), (3331079, 1)] : List FactorBlock).map factorBlockValue).prod) = 1976029373590001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_137
      · exact prime_oneHundredSeventeenDK_433
      · exact prime_oneHundredSeventeenDK_3331079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1976029373590001) ^ 988014686795000 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1976029373590001) ^ 395205874718000 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1976029373590001) ^ 14423572070000 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1976029373590001) ^ 4563578230000 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1976029373590001) ^ 593210000 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_2251352778015469 : Nat.Prime 2251352778015469 := by
  apply lucas_primality 2251352778015469 (2 : ZMod 2251352778015469)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (187612731501289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (187612731501289, 1)] : List FactorBlock).map factorBlockValue).prod) = 2251352778015469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_187612731501289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2251352778015469) ^ 1125676389007734 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2251352778015469) ^ 750450926005156 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2251352778015469) ^ 12 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_2399981386688101 : Nat.Prime 2399981386688101 := by
  apply lucas_primality 2399981386688101 (2 : ZMod 2399981386688101)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (79, 1), (347, 1), (439, 1), (221587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (79, 1), (347, 1), (439, 1), (221587, 1)] : List FactorBlock).map factorBlockValue).prod) = 2399981386688101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_79
      · exact prime_oneHundredSeventeenDK_347
      · exact prime_oneHundredSeventeenDK_439
      · exact prime_oneHundredSeventeenDK_221587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2399981386688101) ^ 1199990693344050 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2399981386688101) ^ 799993795562700 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2399981386688101) ^ 479996277337620 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2399981386688101) ^ 30379511223900 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2399981386688101) ^ 6916372872300 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2399981386688101) ^ 5466927987900 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2399981386688101) ^ 10830876300 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_3633308037590813 : Nat.Prime 3633308037590813 := by
  apply lucas_primality 3633308037590813 (3 : ZMod 3633308037590813)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (41, 1), (167, 1), (311, 1), (607, 1), (100391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (41, 1), (167, 1), (311, 1), (607, 1), (100391, 1)] : List FactorBlock).map factorBlockValue).prod) = 3633308037590813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_41
      · exact prime_oneHundredSeventeenDK_167
      · exact prime_oneHundredSeventeenDK_311
      · exact prime_oneHundredSeventeenDK_607
      · exact prime_oneHundredSeventeenDK_100391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3633308037590813) ^ 1816654018795406 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3633308037590813) ^ 519044005370116 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3633308037590813) ^ 88617269209532 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3633308037590813) ^ 21756335554436 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3633308037590813) ^ 11682662500292 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3633308037590813) ^ 5985680457316 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3633308037590813) ^ 36191571332 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_3887315177361709 : Nat.Prime 3887315177361709 := by
  apply lucas_primality 3887315177361709 (2 : ZMod 3887315177361709)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (12901379, 1), (25109171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (12901379, 1), (25109171, 1)] : List FactorBlock).map factorBlockValue).prod) = 3887315177361709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_12901379
      · exact prime_oneHundredSeventeenDK_25109171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3887315177361709) ^ 1943657588680854 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3887315177361709) ^ 1295771725787236 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3887315177361709) ^ 301310052 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3887315177361709) ^ 154816548 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_4580428198607927 : Nat.Prime 4580428198607927 := by
  apply lucas_primality 4580428198607927 (7 : ZMod 4580428198607927)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (327173442757709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (327173442757709, 1)] : List FactorBlock).map factorBlockValue).prod) = 4580428198607927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_327173442757709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 4580428198607927) ^ 2290214099303963 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 4580428198607927) ^ 654346885515418 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 4580428198607927) ^ 14 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_6102026044398121 : Nat.Prime 6102026044398121 := by
  apply lucas_primality 6102026044398121 (7 : ZMod 6102026044398121)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (53791, 1), (945329461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (53791, 1), (945329461, 1)] : List FactorBlock).map factorBlockValue).prod) = 6102026044398121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_53791
      · exact prime_oneHundredSeventeenDK_945329461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6102026044398121) ^ 3051013022199060 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 6102026044398121) ^ 2034008681466040 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 6102026044398121) ^ 1220405208879624 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 6102026044398121) ^ 113439535320 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 6102026044398121) ^ 6454920 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_7266616075181627 : Nat.Prime 7266616075181627 := by
  apply lucas_primality 7266616075181627 (2 : ZMod 7266616075181627)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3633308037590813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3633308037590813, 1)] : List FactorBlock).map factorBlockValue).prod) = 7266616075181627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3633308037590813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 7266616075181627) ^ 3633308037590813 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 7266616075181627) ^ 2 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_8560070626452379 : Nat.Prime 8560070626452379 := by
  apply lucas_primality 8560070626452379 (2 : ZMod 8560070626452379)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (1093, 1), (118662433481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (1093, 1), (118662433481, 1)] : List FactorBlock).map factorBlockValue).prod) = 8560070626452379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_11
      · exact prime_oneHundredSeventeenDK_1093
      · exact prime_oneHundredSeventeenDK_118662433481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8560070626452379) ^ 4280035313226189 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8560070626452379) ^ 2853356875484126 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8560070626452379) ^ 778188238768398 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8560070626452379) ^ 7831720609746 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8560070626452379) ^ 72138 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_9194337137883169 : Nat.Prime 9194337137883169 := by
  apply lucas_primality 9194337137883169 (19 : ZMod 9194337137883169)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (23, 1), (462677996069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (23, 1), (462677996069, 1)] : List FactorBlock).map factorBlockValue).prod) = 9194337137883169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_23
      · exact prime_oneHundredSeventeenDK_462677996069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 9194337137883169) ^ 4597168568941584 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (19 : ZMod 9194337137883169) ^ 3064779045961056 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (19 : ZMod 9194337137883169) ^ 399753788603616 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (19 : ZMod 9194337137883169) ^ 19872 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_11839881883925141 : Nat.Prime 11839881883925141 := by
  apply lucas_primality 11839881883925141 (10 : ZMod 11839881883925141)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (89, 1), (739, 1), (9000837667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (89, 1), (739, 1), (9000837667, 1)] : List FactorBlock).map factorBlockValue).prod) = 11839881883925141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_89
      · exact prime_oneHundredSeventeenDK_739
      · exact prime_oneHundredSeventeenDK_9000837667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 11839881883925141) ^ 5919940941962570 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (10 : ZMod 11839881883925141) ^ 2367976376785028 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (10 : ZMod 11839881883925141) ^ 133032380718260 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (10 : ZMod 11839881883925141) ^ 16021491047260 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (10 : ZMod 11839881883925141) ^ 1315420 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_12582490561661879 : Nat.Prime 12582490561661879 := by
  apply lucas_primality 12582490561661879 (11 : ZMod 12582490561661879)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (13, 1), (43994722243573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (13, 1), (43994722243573, 1)] : List FactorBlock).map factorBlockValue).prod) = 12582490561661879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_11
      · exact prime_oneHundredSeventeenDK_13
      · exact prime_oneHundredSeventeenDK_43994722243573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 12582490561661879) ^ 6291245280830939 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 12582490561661879) ^ 1143862778332898 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 12582490561661879) ^ 967883889358606 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 12582490561661879) ^ 286 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_13770374832918083 : Nat.Prime 13770374832918083 := by
  apply lucas_primality 13770374832918083 (2 : ZMod 13770374832918083)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (103, 1), (683, 1), (97871859109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (103, 1), (683, 1), (97871859109, 1)] : List FactorBlock).map factorBlockValue).prod) = 13770374832918083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_103
      · exact prime_oneHundredSeventeenDK_683
      · exact prime_oneHundredSeventeenDK_97871859109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13770374832918083) ^ 6885187416459041 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 13770374832918083) ^ 133692959542894 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 13770374832918083) ^ 20161602976454 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 13770374832918083) ^ 140698 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_16279918539612547 : Nat.Prime 16279918539612547 := by
  apply lucas_primality 16279918539612547 (7 : ZMod 16279918539612547)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (29816700622001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (29816700622001, 1)] : List FactorBlock).map factorBlockValue).prod) = 16279918539612547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_13
      · exact prime_oneHundredSeventeenDK_29816700622001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 16279918539612547) ^ 8139959269806273 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 16279918539612547) ^ 5426639513204182 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 16279918539612547) ^ 2325702648516078 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 16279918539612547) ^ 1252301426124042 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 16279918539612547) ^ 546 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_23557898706072893 : Nat.Prime 23557898706072893 := by
  apply lucas_primality 23557898706072893 (2 : ZMod 23557898706072893)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (31, 1), (53, 1), (379, 1), (1831, 1), (737927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (31, 1), (53, 1), (379, 1), (1831, 1), (737927, 1)] : List FactorBlock).map factorBlockValue).prod) = 23557898706072893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_31
      · exact prime_oneHundredSeventeenDK_53
      · exact prime_oneHundredSeventeenDK_379
      · exact prime_oneHundredSeventeenDK_1831
      · exact prime_oneHundredSeventeenDK_737927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 23557898706072893) ^ 11778949353036446 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 23557898706072893) ^ 3365414100867556 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 23557898706072893) ^ 759932216324932 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 23557898706072893) ^ 444488654831564 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 23557898706072893) ^ 62158044079348 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 23557898706072893) ^ 12866138015332 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 23557898706072893) ^ 31924429796 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_25862387424264449 : Nat.Prime 25862387424264449 := by
  apply lucas_primality 25862387424264449 (3 : ZMod 25862387424264449)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (7583, 1), (13322557151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (7583, 1), (13322557151, 1)] : List FactorBlock).map factorBlockValue).prod) = 25862387424264449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_7583
      · exact prime_oneHundredSeventeenDK_13322557151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 25862387424264449) ^ 12931193712132224 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 25862387424264449) ^ 3410574630656 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 25862387424264449) ^ 1941248 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_30206938939875931 : Nat.Prime 30206938939875931 := by
  apply lucas_primality 30206938939875931 (2 : ZMod 30206938939875931)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1006897964662531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1006897964662531, 1)] : List FactorBlock).map factorBlockValue).prod) = 30206938939875931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_1006897964662531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 30206938939875931) ^ 15103469469937965 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 30206938939875931) ^ 10068979646625310 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 30206938939875931) ^ 6041387787975186 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 30206938939875931) ^ 30 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_34109510071640009 : Nat.Prime 34109510071640009 := by
  apply lucas_primality 34109510071640009 (3 : ZMod 34109510071640009)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (131, 1), (32547242434771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (131, 1), (32547242434771, 1)] : List FactorBlock).map factorBlockValue).prod) = 34109510071640009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_131
      · exact prime_oneHundredSeventeenDK_32547242434771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 34109510071640009) ^ 17054755035820004 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 34109510071640009) ^ 260377939478168 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 34109510071640009) ^ 1048 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_38652385516178669 : Nat.Prime 38652385516178669 := by
  apply lucas_primality 38652385516178669 (2 : ZMod 38652385516178669)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (17, 1), (1171, 1), (37339383437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (17, 1), (1171, 1), (37339383437, 1)] : List FactorBlock).map factorBlockValue).prod) = 38652385516178669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_13
      · exact prime_oneHundredSeventeenDK_17
      · exact prime_oneHundredSeventeenDK_1171
      · exact prime_oneHundredSeventeenDK_37339383437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 38652385516178669) ^ 19326192758089334 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 38652385516178669) ^ 2973260424321436 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 38652385516178669) ^ 2273669736245804 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 38652385516178669) ^ 33008014958308 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 38652385516178669) ^ 1035164 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_77126746040136427 : Nat.Prime 77126746040136427 := by
  apply lucas_primality 77126746040136427 (2 : ZMod 77126746040136427)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (241, 1), (97577, 1), (546624703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (241, 1), (97577, 1), (546624703, 1)] : List FactorBlock).map factorBlockValue).prod) = 77126746040136427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_241
      · exact prime_oneHundredSeventeenDK_97577
      · exact prime_oneHundredSeventeenDK_546624703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 77126746040136427) ^ 38563373020068213 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 77126746040136427) ^ 25708915346712142 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 77126746040136427) ^ 320027991867786 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 77126746040136427) ^ 790419320538 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 77126746040136427) ^ 141096342 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_101014991469007579 : Nat.Prime 101014991469007579 := by
  apply lucas_primality 101014991469007579 (2 : ZMod 101014991469007579)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (67, 1), (27920119256221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (67, 1), (27920119256221, 1)] : List FactorBlock).map factorBlockValue).prod) = 101014991469007579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_67
      · exact prime_oneHundredSeventeenDK_27920119256221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 101014991469007579) ^ 50507495734503789 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 101014991469007579) ^ 33671663823002526 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 101014991469007579) ^ 1507686439835934 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 101014991469007579) ^ 3618 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_104686817909989841 : Nat.Prime 104686817909989841 := by
  apply lucas_primality 104686817909989841 (3 : ZMod 104686817909989841)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (7, 1), (31721, 1), (5893280359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (7, 1), (31721, 1), (5893280359, 1)] : List FactorBlock).map factorBlockValue).prod) = 104686817909989841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_31721
      · exact prime_oneHundredSeventeenDK_5893280359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 104686817909989841) ^ 52343408954994920 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 104686817909989841) ^ 20937363581997968 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 104686817909989841) ^ 14955259701427120 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 104686817909989841) ^ 3300237001040 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 104686817909989841) ^ 17763760 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_177112743868002511 : Nat.Prime 177112743868002511 := by
  apply lucas_primality 177112743868002511 (6 : ZMod 177112743868002511)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (281, 1), (678593, 1), (10320283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (281, 1), (678593, 1), (10320283, 1)] : List FactorBlock).map factorBlockValue).prod) = 177112743868002511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_281
      · exact prime_oneHundredSeventeenDK_678593
      · exact prime_oneHundredSeventeenDK_10320283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 177112743868002511) ^ 88556371934001255 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 177112743868002511) ^ 59037581289334170 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 177112743868002511) ^ 35422548773600502 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 177112743868002511) ^ 630294462163710 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 177112743868002511) ^ 260999957070 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 177112743868002511) ^ 17161616970 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_280858881705970091 : Nat.Prime 280858881705970091 := by
  apply lucas_primality 280858881705970091 (2 : ZMod 280858881705970091)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (567659, 1), (49476689651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (567659, 1), (49476689651, 1)] : List FactorBlock).map factorBlockValue).prod) = 280858881705970091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_567659
      · exact prime_oneHundredSeventeenDK_49476689651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 280858881705970091) ^ 140429440852985045 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 280858881705970091) ^ 56171776341194018 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 280858881705970091) ^ 494766896510 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 280858881705970091) ^ 5676590 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_350116243023856541 : Nat.Prime 350116243023856541 := by
  apply lucas_primality 350116243023856541 (2 : ZMod 350116243023856541)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 2), (11, 1), (1247591, 1), (26032823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 2), (11, 1), (1247591, 1), (26032823, 1)] : List FactorBlock).map factorBlockValue).prod) = 350116243023856541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_11
      · exact prime_oneHundredSeventeenDK_1247591
      · exact prime_oneHundredSeventeenDK_26032823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 350116243023856541) ^ 175058121511928270 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 350116243023856541) ^ 70023248604771308 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 350116243023856541) ^ 50016606146265220 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 350116243023856541) ^ 31828749365805140 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 350116243023856541) ^ 280633831940 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 350116243023856541) ^ 13449030980 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_638983830804654331 : Nat.Prime 638983830804654331 := by
  apply lucas_primality 638983830804654331 (10 : ZMod 638983830804654331)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (19, 1), (59, 1), (13729, 1), (153773531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (19, 1), (59, 1), (13729, 1), (153773531, 1)] : List FactorBlock).map factorBlockValue).prod) = 638983830804654331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_19
      · exact prime_oneHundredSeventeenDK_59
      · exact prime_oneHundredSeventeenDK_13729
      · exact prime_oneHundredSeventeenDK_153773531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 638983830804654331) ^ 319491915402327165 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (10 : ZMod 638983830804654331) ^ 212994610268218110 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (10 : ZMod 638983830804654331) ^ 127796766160930866 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (10 : ZMod 638983830804654331) ^ 33630727937087070 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (10 : ZMod 638983830804654331) ^ 10830234420417870 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (10 : ZMod 638983830804654331) ^ 46542634627770 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (10 : ZMod 638983830804654331) ^ 4155356430 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_689576496218686451 : Nat.Prime 689576496218686451 := by
  apply lucas_primality 689576496218686451 (2 : ZMod 689576496218686451)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (11, 3), (43, 1), (619, 1), (653, 1), (596159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (11, 3), (43, 1), (619, 1), (653, 1), (596159, 1)] : List FactorBlock).map factorBlockValue).prod) = 689576496218686451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_11
      · exact prime_oneHundredSeventeenDK_43
      · exact prime_oneHundredSeventeenDK_619
      · exact prime_oneHundredSeventeenDK_653
      · exact prime_oneHundredSeventeenDK_596159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 689576496218686451) ^ 344788248109343225 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 689576496218686451) ^ 137915299243737290 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 689576496218686451) ^ 62688772383516950 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 689576496218686451) ^ 16036662702760150 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 689576496218686451) ^ 1114016956734550 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 689576496218686451) ^ 1056013011054650 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 689576496218686451) ^ 1156698961550 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_848084353418624149 : Nat.Prime 848084353418624149 := by
  apply lucas_primality 848084353418624149 (2 : ZMod 848084353418624149)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (23557898706072893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (23557898706072893, 1)] : List FactorBlock).map factorBlockValue).prod) = 848084353418624149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_23557898706072893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 848084353418624149) ^ 424042176709312074 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 848084353418624149) ^ 282694784472874716 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 848084353418624149) ^ 36 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_1384073961782806691 : Nat.Prime 1384073961782806691 := by
  apply lucas_primality 1384073961782806691 (6 : ZMod 1384073961782806691)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (12582490561661879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (12582490561661879, 1)] : List FactorBlock).map factorBlockValue).prod) = 1384073961782806691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_11
      · exact prime_oneHundredSeventeenDK_12582490561661879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1384073961782806691) ^ 692036980891403345 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1384073961782806691) ^ 276814792356561338 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1384073961782806691) ^ 125824905616618790 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1384073961782806691) ^ 110 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_2184199832046529223 : Nat.Prime 2184199832046529223 := by
  apply lucas_primality 2184199832046529223 (5 : ZMod 2184199832046529223)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (317903, 1), (491737, 1), (6986101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (317903, 1), (491737, 1), (6986101, 1)] : List FactorBlock).map factorBlockValue).prod) = 2184199832046529223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_317903
      · exact prime_oneHundredSeventeenDK_491737
      · exact prime_oneHundredSeventeenDK_6986101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2184199832046529223) ^ 1092099916023264611 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 2184199832046529223) ^ 6870648694874 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 2184199832046529223) ^ 4441804932406 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 2184199832046529223) ^ 312649335022 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_2927544154246713619 : Nat.Prime 2927544154246713619 := by
  apply lucas_primality 2927544154246713619 (3 : ZMod 2927544154246713619)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (8560070626452379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (8560070626452379, 1)] : List FactorBlock).map factorBlockValue).prod) = 2927544154246713619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_19
      · exact prime_oneHundredSeventeenDK_8560070626452379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2927544154246713619) ^ 1463772077123356809 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2927544154246713619) ^ 975848051415571206 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2927544154246713619) ^ 154081271276142822 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2927544154246713619) ^ 342 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_2988225518317662589 : Nat.Prime 2988225518317662589 := by
  apply lucas_primality 2988225518317662589 (6 : ZMod 2988225518317662589)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (59, 1), (727, 1), (105211, 1), (7882909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (59, 1), (727, 1), (105211, 1), (7882909, 1)] : List FactorBlock).map factorBlockValue).prod) = 2988225518317662589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_59
      · exact prime_oneHundredSeventeenDK_727
      · exact prime_oneHundredSeventeenDK_105211
      · exact prime_oneHundredSeventeenDK_7882909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2988225518317662589) ^ 1494112759158831294 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 2988225518317662589) ^ 996075172772554196 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 2988225518317662589) ^ 426889359759666084 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 2988225518317662589) ^ 50647890140977332 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 2988225518317662589) ^ 4110351469487844 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 2988225518317662589) ^ 28402215721908 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 2988225518317662589) ^ 379076495532 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_3014995691311940443 : Nat.Prime 3014995691311940443 := by
  apply lucas_primality 3014995691311940443 (2 : ZMod 3014995691311940443)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (321187, 1), (1564506913061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (321187, 1), (1564506913061, 1)] : List FactorBlock).map factorBlockValue).prod) = 3014995691311940443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_321187
      · exact prime_oneHundredSeventeenDK_1564506913061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3014995691311940443) ^ 1507497845655970221 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3014995691311940443) ^ 1004998563770646814 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3014995691311940443) ^ 9387041478366 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3014995691311940443) ^ 1927122 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_5760823914764129569 : Nat.Prime 5760823914764129569 := by
  apply lucas_primality 5760823914764129569 (11 : ZMod 5760823914764129569)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (103, 1), (137, 1), (607515741979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (103, 1), (137, 1), (607515741979, 1)] : List FactorBlock).map factorBlockValue).prod) = 5760823914764129569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_103
      · exact prime_oneHundredSeventeenDK_137
      · exact prime_oneHundredSeventeenDK_607515741979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 5760823914764129569) ^ 2880411957382064784 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 5760823914764129569) ^ 1920274638254709856 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 5760823914764129569) ^ 822974844966304224 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 5760823914764129569) ^ 55930329269554656 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 5760823914764129569) ^ 42049809596818464 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 5760823914764129569) ^ 9482592 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_6879047620673288231 : Nat.Prime 6879047620673288231 := by
  apply lucas_primality 6879047620673288231 (13 : ZMod 6879047620673288231)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (79, 1), (3067, 1), (167008481483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (79, 1), (3067, 1), (167008481483, 1)] : List FactorBlock).map factorBlockValue).prod) = 6879047620673288231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_17
      · exact prime_oneHundredSeventeenDK_79
      · exact prime_oneHundredSeventeenDK_3067
      · exact prime_oneHundredSeventeenDK_167008481483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 6879047620673288231) ^ 3439523810336644115 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (13 : ZMod 6879047620673288231) ^ 1375809524134657646 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (13 : ZMod 6879047620673288231) ^ 404649860039605190 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (13 : ZMod 6879047620673288231) ^ 87076552160421370 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (13 : ZMod 6879047620673288231) ^ 2242923906316690 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (13 : ZMod 6879047620673288231) ^ 41189810 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_9051852206305875919 : Nat.Prime 9051852206305875919 := by
  apply lucas_primality 9051852206305875919 (3 : ZMod 9051852206305875919)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (9829, 1), (23719, 1), (924447929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (9829, 1), (23719, 1), (924447929, 1)] : List FactorBlock).map factorBlockValue).prod) = 9051852206305875919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_9829
      · exact prime_oneHundredSeventeenDK_23719
      · exact prime_oneHundredSeventeenDK_924447929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9051852206305875919) ^ 4525926103152937959 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 9051852206305875919) ^ 3017284068768625306 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 9051852206305875919) ^ 1293121743757982274 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 9051852206305875919) ^ 920933177973942 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 9051852206305875919) ^ 381628745153922 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 9051852206305875919) ^ 9791630142 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_10880067820548607651 : Nat.Prime 10880067820548607651 := by
  apply lucas_primality 10880067820548607651 (2 : ZMod 10880067820548607651)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (109, 1), (113, 1), (157, 1), (12503007593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (109, 1), (113, 1), (157, 1), (12503007593, 1)] : List FactorBlock).map factorBlockValue).prod) = 10880067820548607651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_109
      · exact prime_oneHundredSeventeenDK_113
      · exact prime_oneHundredSeventeenDK_157
      · exact prime_oneHundredSeventeenDK_12503007593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10880067820548607651) ^ 5440033910274303825 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 10880067820548607651) ^ 3626689273516202550 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 10880067820548607651) ^ 2176013564109721530 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 10880067820548607651) ^ 99817135968335850 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 10880067820548607651) ^ 96283786022554050 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 10880067820548607651) ^ 69299795035341450 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 10880067820548607651) ^ 870196050 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_24159991592813491439 : Nat.Prime 24159991592813491439 := by
  apply lucas_primality 24159991592813491439 (13 : ZMod 24159991592813491439)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (53, 1), (683, 1), (71437, 1), (245863127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (53, 1), (683, 1), (71437, 1), (245863127, 1)] : List FactorBlock).map factorBlockValue).prod) = 24159991592813491439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_19
      · exact prime_oneHundredSeventeenDK_53
      · exact prime_oneHundredSeventeenDK_683
      · exact prime_oneHundredSeventeenDK_71437
      · exact prime_oneHundredSeventeenDK_245863127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 24159991592813491439) ^ 12079995796406745719 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (13 : ZMod 24159991592813491439) ^ 1271578504884920602 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (13 : ZMod 24159991592813491439) ^ 455848897977613046 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (13 : ZMod 24159991592813491439) ^ 35373340545846986 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (13 : ZMod 24159991592813491439) ^ 338199974702374 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (13 : ZMod 24159991592813491439) ^ 98266022594 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_41924664091911494519 : Nat.Prime 41924664091911494519 := by
  apply lucas_primality 41924664091911494519 (13 : ZMod 41924664091911494519)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (347, 1), (10639, 1), (60091, 1), (3048163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (347, 1), (10639, 1), (60091, 1), (3048163, 1)] : List FactorBlock).map factorBlockValue).prod) = 41924664091911494519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_31
      · exact prime_oneHundredSeventeenDK_347
      · exact prime_oneHundredSeventeenDK_10639
      · exact prime_oneHundredSeventeenDK_60091
      · exact prime_oneHundredSeventeenDK_3048163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 41924664091911494519) ^ 20962332045955747259 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (13 : ZMod 41924664091911494519) ^ 1352408519093919178 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (13 : ZMod 41924664091911494519) ^ 120820357613577794 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (13 : ZMod 41924664091911494519) ^ 3940658341189162 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (13 : ZMod 41924664091911494519) ^ 697686244061698 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (13 : ZMod 41924664091911494519) ^ 13754075517586 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_42376090025613958487 : Nat.Prime 42376090025613958487 := by
  apply lucas_primality 42376090025613958487 (5 : ZMod 42376090025613958487)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (37, 1), (1049, 1), (1446257, 1), (16411201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (37, 1), (1049, 1), (1446257, 1), (16411201, 1)] : List FactorBlock).map factorBlockValue).prod) = 42376090025613958487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_23
      · exact prime_oneHundredSeventeenDK_37
      · exact prime_oneHundredSeventeenDK_1049
      · exact prime_oneHundredSeventeenDK_1446257
      · exact prime_oneHundredSeventeenDK_16411201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 42376090025613958487) ^ 21188045012806979243 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 42376090025613958487) ^ 1842438696765824282 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 42376090025613958487) ^ 1145299730421998878 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 42376090025613958487) ^ 40396653980566214 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 42376090025613958487) ^ 29300525442998 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 42376090025613958487) ^ 2582144355286 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_49777685765000546389 : Nat.Prime 49777685765000546389 := by
  apply lucas_primality 49777685765000546389 (2 : ZMod 49777685765000546389)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (17, 1), (211, 1), (1733, 1), (95329096367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (17, 1), (211, 1), (1733, 1), (95329096367, 1)] : List FactorBlock).map factorBlockValue).prod) = 49777685765000546389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_17
      · exact prime_oneHundredSeventeenDK_211
      · exact prime_oneHundredSeventeenDK_1733
      · exact prime_oneHundredSeventeenDK_95329096367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 49777685765000546389) ^ 24888842882500273194 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 49777685765000546389) ^ 16592561921666848796 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 49777685765000546389) ^ 7111097966428649484 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 49777685765000546389) ^ 2928099162647090964 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 49777685765000546389) ^ 235913202677727708 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 49777685765000546389) ^ 28723419368148036 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 49777685765000546389) ^ 522166764 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_105131039647847779157 : Nat.Prime 105131039647847779157 := by
  apply lucas_primality 105131039647847779157 (2 : ZMod 105131039647847779157)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (173, 1), (1831, 1), (2676546708113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (173, 1), (1831, 1), (2676546708113, 1)] : List FactorBlock).map factorBlockValue).prod) = 105131039647847779157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_31
      · exact prime_oneHundredSeventeenDK_173
      · exact prime_oneHundredSeventeenDK_1831
      · exact prime_oneHundredSeventeenDK_2676546708113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 105131039647847779157) ^ 52565519823923889578 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 105131039647847779157) ^ 3391323859607992876 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 105131039647847779157) ^ 607693870796807972 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 105131039647847779157) ^ 57417279982440076 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 105131039647847779157) ^ 39278612 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_124478453735397502303 : Nat.Prime 124478453735397502303 := by
  apply lucas_primality 124478453735397502303 (19 : ZMod 124478453735397502303)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (404017, 1), (51350336634101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (404017, 1), (51350336634101, 1)] : List FactorBlock).map factorBlockValue).prod) = 124478453735397502303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_404017
      · exact prime_oneHundredSeventeenDK_51350336634101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 124478453735397502303) ^ 62239226867698751151 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (19 : ZMod 124478453735397502303) ^ 41492817911799167434 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (19 : ZMod 124478453735397502303) ^ 308102019804606 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (19 : ZMod 124478453735397502303) ^ 2424102 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_131564767494176166793 : Nat.Prime 131564767494176166793 := by
  apply lucas_primality 131564767494176166793 (7 : ZMod 131564767494176166793)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (463, 1), (11839881883925141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (463, 1), (11839881883925141, 1)] : List FactorBlock).map factorBlockValue).prod) = 131564767494176166793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_463
      · exact prime_oneHundredSeventeenDK_11839881883925141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 131564767494176166793) ^ 65782383747088083396 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 131564767494176166793) ^ 43854922498058722264 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 131564767494176166793) ^ 284157165214203384 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 131564767494176166793) ^ 11112 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_131655542491839391273 : Nat.Prime 131655542491839391273 := by
  apply lucas_primality 131655542491839391273 (5 : ZMod 131655542491839391273)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (13, 1), (41, 1), (381185991510433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (13, 1), (41, 1), (381185991510433, 1)] : List FactorBlock).map factorBlockValue).prod) = 131655542491839391273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_13
      · exact prime_oneHundredSeventeenDK_41
      · exact prime_oneHundredSeventeenDK_381185991510433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 131655542491839391273) ^ 65827771245919695636 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 131655542491839391273) ^ 43885180830613130424 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 131655542491839391273) ^ 10127349422449183944 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 131655542491839391273) ^ 3211110792483887592 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 131655542491839391273) ^ 345384 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_135822707804172451877 : Nat.Prime 135822707804172451877 := by
  apply lucas_primality 135822707804172451877 (2 : ZMod 135822707804172451877)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (41, 1), (89, 1), (347, 1), (2437902708193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (41, 1), (89, 1), (347, 1), (2437902708193, 1)] : List FactorBlock).map factorBlockValue).prod) = 135822707804172451877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_11
      · exact prime_oneHundredSeventeenDK_41
      · exact prime_oneHundredSeventeenDK_89
      · exact prime_oneHundredSeventeenDK_347
      · exact prime_oneHundredSeventeenDK_2437902708193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 135822707804172451877) ^ 67911353902086225938 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 135822707804172451877) ^ 12347518891288404716 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 135822707804172451877) ^ 3312748970833474436 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 135822707804172451877) ^ 1526097840496319684 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 135822707804172451877) ^ 391419907216635308 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 135822707804172451877) ^ 55712932 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_256223811061086791179 : Nat.Prime 256223811061086791179 := by
  apply lucas_primality 256223811061086791179 (2 : ZMod 256223811061086791179)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) = 256223811061086791179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_17
      · exact prime_oneHundredSeventeenDK_6863
      · exact prime_oneHundredSeventeenDK_366020420757353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 256223811061086791179) ^ 128111905530543395589 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 85407937020362263726 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 15071988885946281834 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 37334082917250006 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 700026 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_313010856169636387583 : Nat.Prime 313010856169636387583 := by
  apply lucas_primality 313010856169636387583 (5 : ZMod 313010856169636387583)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1447, 1), (32084053, 1), (3371100101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1447, 1), (32084053, 1), (3371100101, 1)] : List FactorBlock).map factorBlockValue).prod) = 313010856169636387583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_1447
      · exact prime_oneHundredSeventeenDK_32084053
      · exact prime_oneHundredSeventeenDK_3371100101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 313010856169636387583) ^ 156505428084818193791 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 313010856169636387583) ^ 216317108617578706 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 313010856169636387583) ^ 9755963692294 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 313010856169636387583) ^ 92851249382 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_590566329281522909617 : Nat.Prime 590566329281522909617 := by
  apply lucas_primality 590566329281522909617 (20 : ZMod 590566329281522909617)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (1448309, 1), (1213579343059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (1448309, 1), (1213579343059, 1)] : List FactorBlock).map factorBlockValue).prod) = 590566329281522909617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_1448309
      · exact prime_oneHundredSeventeenDK_1213579343059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (20 : ZMod 590566329281522909617) ^ 295283164640761454808 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (20 : ZMod 590566329281522909617) ^ 196855443093840969872 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (20 : ZMod 590566329281522909617) ^ 84366618468788987088 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (20 : ZMod 590566329281522909617) ^ 407762659267824 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (20 : ZMod 590566329281522909617) ^ 486631824 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_597332229180006556669 : Nat.Prime 597332229180006556669 := by
  apply lucas_primality 597332229180006556669 (2 : ZMod 597332229180006556669)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (49777685765000546389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (49777685765000546389, 1)] : List FactorBlock).map factorBlockValue).prod) = 597332229180006556669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_49777685765000546389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 597332229180006556669) ^ 298666114590003278334 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 597332229180006556669) ^ 199110743060002185556 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 597332229180006556669) ^ 12 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_601135034269270369663 : Nat.Prime 601135034269270369663 := by
  apply lucas_primality 601135034269270369663 (3 : ZMod 601135034269270369663)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (101, 1), (142641539, 1), (2318099881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (101, 1), (142641539, 1), (2318099881, 1)] : List FactorBlock).map factorBlockValue).prod) = 601135034269270369663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_101
      · exact prime_oneHundredSeventeenDK_142641539
      · exact prime_oneHundredSeventeenDK_2318099881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 601135034269270369663) ^ 300567517134635184831 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 601135034269270369663) ^ 200378344756423456554 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 601135034269270369663) ^ 5951832022468023462 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 601135034269270369663) ^ 4214305583658 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 601135034269270369663) ^ 259322317902 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_728399691556238262391 : Nat.Prime 728399691556238262391 := by
  apply lucas_primality 728399691556238262391 (6 : ZMod 728399691556238262391)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (23, 1), (857, 1), (30781, 1), (135511, 1), (295313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (23, 1), (857, 1), (30781, 1), (135511, 1), (295313, 1)] : List FactorBlock).map factorBlockValue).prod) = 728399691556238262391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_23
      · exact prime_oneHundredSeventeenDK_857
      · exact prime_oneHundredSeventeenDK_30781
      · exact prime_oneHundredSeventeenDK_135511
      · exact prime_oneHundredSeventeenDK_295313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 728399691556238262391) ^ 364199845778119131195 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 728399691556238262391) ^ 242799897185412754130 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 728399691556238262391) ^ 145679938311247652478 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 728399691556238262391) ^ 31669551806792967930 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 728399691556238262391) ^ 849941297031783270 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 728399691556238262391) ^ 23663938519094190 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 728399691556238262391) ^ 5375207116442490 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 728399691556238262391) ^ 2466534461931030 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_1151969505208148903813 : Nat.Prime 1151969505208148903813 := by
  apply lucas_primality 1151969505208148903813 (2 : ZMod 1151969505208148903813)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1879607, 1), (153219463591079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1879607, 1), (153219463591079, 1)] : List FactorBlock).map factorBlockValue).prod) = 1151969505208148903813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_1879607
      · exact prime_oneHundredSeventeenDK_153219463591079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1151969505208148903813) ^ 575984752604074451906 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1151969505208148903813) ^ 612877854364316 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1151969505208148903813) ^ 7518428 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_1205269042013298899237 : Nat.Prime 1205269042013298899237 := by
  apply lucas_primality 1205269042013298899237 (2 : ZMod 1205269042013298899237)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (1549, 1), (47713, 1), (341461, 1), (519119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (1549, 1), (47713, 1), (341461, 1), (519119, 1)] : List FactorBlock).map factorBlockValue).prod) = 1205269042013298899237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_23
      · exact prime_oneHundredSeventeenDK_1549
      · exact prime_oneHundredSeventeenDK_47713
      · exact prime_oneHundredSeventeenDK_341461
      · exact prime_oneHundredSeventeenDK_519119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1205269042013298899237) ^ 602634521006649449618 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 52403001826665169532 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 778094927058294964 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 25260810303550372 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 3529741440496276 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 2321758675782044 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_1791621948270583135097 : Nat.Prime 1791621948270583135097 := by
  apply lucas_primality 1791621948270583135097 (3 : ZMod 1791621948270583135097)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (557, 1), (6367, 1), (4857613868521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (557, 1), (6367, 1), (4857613868521, 1)] : List FactorBlock).map factorBlockValue).prod) = 1791621948270583135097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_13
      · exact prime_oneHundredSeventeenDK_557
      · exact prime_oneHundredSeventeenDK_6367
      · exact prime_oneHundredSeventeenDK_4857613868521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1791621948270583135097) ^ 895810974135291567548 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1791621948270583135097) ^ 137817072943891010392 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1791621948270583135097) ^ 3216556460090813528 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1791621948270583135097) ^ 281391856175684488 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1791621948270583135097) ^ 368827576 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_2973544566831419806559 : Nat.Prime 2973544566831419806559 := by
  apply lucas_primality 2973544566831419806559 (11 : ZMod 2973544566831419806559)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (521, 1), (77126746040136427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (521, 1), (77126746040136427, 1)] : List FactorBlock).map factorBlockValue).prod) = 2973544566831419806559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_37
      · exact prime_oneHundredSeventeenDK_521
      · exact prime_oneHundredSeventeenDK_77126746040136427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 2973544566831419806559) ^ 1486772283415709903279 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 2973544566831419806559) ^ 80366069373822156934 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 2973544566831419806559) ^ 5707379206970095598 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 2973544566831419806559) ^ 38554 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_3074685732733041494149 : Nat.Prime 3074685732733041494149 := by
  apply lucas_primality 3074685732733041494149 (2 : ZMod 3074685732733041494149)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) = 3074685732733041494149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_256223811061086791179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3074685732733041494149) ^ 1537342866366520747074 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 1024895244244347164716 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 12 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_5903909875390047909359 : Nat.Prime 5903909875390047909359 := by
  apply lucas_primality 5903909875390047909359 (11 : ZMod 5903909875390047909359)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (613, 1), (739, 1), (140639, 1), (46333919623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (613, 1), (739, 1), (140639, 1), (46333919623, 1)] : List FactorBlock).map factorBlockValue).prod) = 5903909875390047909359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_613
      · exact prime_oneHundredSeventeenDK_739
      · exact prime_oneHundredSeventeenDK_140639
      · exact prime_oneHundredSeventeenDK_46333919623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 5903909875390047909359) ^ 2951954937695023954679 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 5903909875390047909359) ^ 9631174348107745366 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 5903909875390047909359) ^ 7989052605399252922 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 5903909875390047909359) ^ 41979179853312722 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (11 : ZMod 5903909875390047909359) ^ 127420902946 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_10092963498666755004889 : Nat.Prime 10092963498666755004889 := by
  apply lucas_primality 10092963498666755004889 (7 : ZMod 10092963498666755004889)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (73, 1), (5760823914764129569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (73, 1), (5760823914764129569, 1)] : List FactorBlock).map factorBlockValue).prod) = 10092963498666755004889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_73
      · exact prime_oneHundredSeventeenDK_5760823914764129569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 10092963498666755004889) ^ 5046481749333377502444 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 10092963498666755004889) ^ 3364321166222251668296 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 10092963498666755004889) ^ 138259773954339109656 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 10092963498666755004889) ^ 1752 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_15650542808481819379151 : Nat.Prime 15650542808481819379151 := by
  apply lucas_primality 15650542808481819379151 (23 : ZMod 15650542808481819379151)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (313010856169636387583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (313010856169636387583, 1)] : List FactorBlock).map factorBlockValue).prod) = 15650542808481819379151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_313010856169636387583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (23 : ZMod 15650542808481819379151) ^ 7825271404240909689575 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (23 : ZMod 15650542808481819379151) ^ 3130108561696363875830 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (23 : ZMod 15650542808481819379151) ^ 50 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_26222388896024577446077 : Nat.Prime 26222388896024577446077 := by
  apply lucas_primality 26222388896024577446077 (2 : ZMod 26222388896024577446077)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (728399691556238262391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (728399691556238262391, 1)] : List FactorBlock).map factorBlockValue).prod) = 26222388896024577446077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_728399691556238262391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 26222388896024577446077) ^ 13111194448012288723038 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 26222388896024577446077) ^ 8740796298674859148692 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 26222388896024577446077) ^ 36 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_26734605944249517689521 : Nat.Prime 26734605944249517689521 := by
  apply lucas_primality 26734605944249517689521 (35 : ZMod 26734605944249517689521)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (17, 1), (2184199832046529223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (17, 1), (2184199832046529223, 1)] : List FactorBlock).map factorBlockValue).prod) = 26734605944249517689521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_17
      · exact prime_oneHundredSeventeenDK_2184199832046529223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (35 : ZMod 26734605944249517689521) ^ 13367302972124758844760 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (35 : ZMod 26734605944249517689521) ^ 8911535314749839229840 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (35 : ZMod 26734605944249517689521) ^ 5346921188849903537904 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (35 : ZMod 26734605944249517689521) ^ 1572623879073501040560 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (35 : ZMod 26734605944249517689521) ^ 12240 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_42998926758493995242329 : Nat.Prime 42998926758493995242329 := by
  apply lucas_primality 42998926758493995242329 (7 : ZMod 42998926758493995242329)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1791621948270583135097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1791621948270583135097, 1)] : List FactorBlock).map factorBlockValue).prod) = 42998926758493995242329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_1791621948270583135097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 42998926758493995242329) ^ 21499463379246997621164 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 42998926758493995242329) ^ 14332975586164665080776 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 42998926758493995242329) ^ 24 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_55144517844561571008773 : Nat.Prime 55144517844561571008773 := by
  apply lucas_primality 55144517844561571008773 (2 : ZMod 55144517844561571008773)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (149, 1), (157, 1), (29956481, 1), (2810396503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (149, 1), (157, 1), (29956481, 1), (2810396503, 1)] : List FactorBlock).map factorBlockValue).prod) = 55144517844561571008773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_149
      · exact prime_oneHundredSeventeenDK_157
      · exact prime_oneHundredSeventeenDK_29956481
      · exact prime_oneHundredSeventeenDK_2810396503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 55144517844561571008773) ^ 27572258922280785504386 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 55144517844561571008773) ^ 7877788263508795858396 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 55144517844561571008773) ^ 370097435198399805428 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 55144517844561571008773) ^ 351238967162812554196 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 55144517844561571008773) ^ 1840820951051012 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 55144517844561571008773) ^ 19621614880924 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_82177469443059690490913 : Nat.Prime 82177469443059690490913 := by
  apply lucas_primality 82177469443059690490913 (3 : ZMod 82177469443059690490913)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 2), (41, 1), (1223, 1), (23117, 1), (18309463891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 2), (41, 1), (1223, 1), (23117, 1), (18309463891, 1)] : List FactorBlock).map factorBlockValue).prod) = 82177469443059690490913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_11
      · exact prime_oneHundredSeventeenDK_41
      · exact prime_oneHundredSeventeenDK_1223
      · exact prime_oneHundredSeventeenDK_23117
      · exact prime_oneHundredSeventeenDK_18309463891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 82177469443059690490913) ^ 41088734721529845245456 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 82177469443059690490913) ^ 7470679040278153680992 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 82177469443059690490913) ^ 2004328523001455865632 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 82177469443059690490913) ^ 67193351956712747744 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 82177469443059690490913) ^ 3554850086216191136 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 82177469443059690490913) ^ 4488250990432 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_93761125199472257067967 : Nat.Prime 93761125199472257067967 := by
  apply lucas_primality 93761125199472257067967 (3 : ZMod 93761125199472257067967)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (167, 1), (21991, 1), (5132117, 1), (829112689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (167, 1), (21991, 1), (5132117, 1), (829112689, 1)] : List FactorBlock).map factorBlockValue).prod) = 93761125199472257067967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_167
      · exact prime_oneHundredSeventeenDK_21991
      · exact prime_oneHundredSeventeenDK_5132117
      · exact prime_oneHundredSeventeenDK_829112689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 93761125199472257067967) ^ 46880562599736128533983 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 93761125199472257067967) ^ 31253708399824085689322 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 93761125199472257067967) ^ 561443863469893754898 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 93761125199472257067967) ^ 4263613532784878226 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 93761125199472257067967) ^ 18269483178086598 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 93761125199472257067967) ^ 113086105716894 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_114270582252405377601457 : Nat.Prime 114270582252405377601457 := by
  apply lucas_primality 114270582252405377601457 (5 : ZMod 114270582252405377601457)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (263, 1), (9051852206305875919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (263, 1), (9051852206305875919, 1)] : List FactorBlock).map factorBlockValue).prod) = 114270582252405377601457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_263
      · exact prime_oneHundredSeventeenDK_9051852206305875919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 114270582252405377601457) ^ 57135291126202688800728 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 114270582252405377601457) ^ 38090194084135125867152 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 114270582252405377601457) ^ 434488905902682044112 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 114270582252405377601457) ^ 12624 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_249702100761660521262019 : Nat.Prime 249702100761660521262019 := by
  apply lucas_primality 249702100761660521262019 (2 : ZMod 249702100761660521262019)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (733, 1), (2988225518317662589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (733, 1), (2988225518317662589, 1)] : List FactorBlock).map factorBlockValue).prod) = 249702100761660521262019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_19
      · exact prime_oneHundredSeventeenDK_733
      · exact prime_oneHundredSeventeenDK_2988225518317662589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 249702100761660521262019) ^ 124851050380830260631009 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 249702100761660521262019) ^ 83234033587220173754006 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 249702100761660521262019) ^ 13142215829561080066422 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 249702100761660521262019) ^ 340657709088213535146 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 249702100761660521262019) ^ 83562 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_382694266830165704393761 : Nat.Prime 382694266830165704393761 := by
  apply lucas_primality 382694266830165704393761 (7 : ZMod 382694266830165704393761)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (11, 1), (24159991592813491439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (11, 1), (24159991592813491439, 1)] : List FactorBlock).map factorBlockValue).prod) = 382694266830165704393761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_11
      · exact prime_oneHundredSeventeenDK_24159991592813491439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 382694266830165704393761) ^ 191347133415082852196880 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 382694266830165704393761) ^ 127564755610055234797920 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 382694266830165704393761) ^ 76538853366033140878752 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 382694266830165704393761) ^ 34790387893651427672160 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 382694266830165704393761) ^ 15840 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_404061569272471932682793 : Nat.Prime 404061569272471932682793 := by
  apply lucas_primality 404061569272471932682793 (3 : ZMod 404061569272471932682793)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (120647, 1), (903781, 1), (15972754883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (120647, 1), (903781, 1), (15972754883, 1)] : List FactorBlock).map factorBlockValue).prod) = 404061569272471932682793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_29
      · exact prime_oneHundredSeventeenDK_120647
      · exact prime_oneHundredSeventeenDK_903781
      · exact prime_oneHundredSeventeenDK_15972754883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 404061569272471932682793) ^ 202030784636235966341396 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 404061569272471932682793) ^ 13933157561119721816648 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 404061569272471932682793) ^ 3349122392371728536 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 404061569272471932682793) ^ 447079070341677832 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 404061569272471932682793) ^ 25296924183224 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_1682809102787506222932509 : Nat.Prime 1682809102787506222932509 := by
  apply lucas_primality 1682809102787506222932509 (3 : ZMod 1682809102787506222932509)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (29, 1), (223, 1), (1523, 1), (6102026044398121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (29, 1), (223, 1), (1523, 1), (6102026044398121, 1)] : List FactorBlock).map factorBlockValue).prod) = 1682809102787506222932509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_29
      · exact prime_oneHundredSeventeenDK_223
      · exact prime_oneHundredSeventeenDK_1523
      · exact prime_oneHundredSeventeenDK_6102026044398121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1682809102787506222932509) ^ 841404551393753111466254 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1682809102787506222932509) ^ 240401300398215174704644 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1682809102787506222932509) ^ 58027900096120904239052 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1682809102787506222932509) ^ 7546229160482090685796 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1682809102787506222932509) ^ 1104930468015434158196 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1682809102787506222932509) ^ 275778748 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_3754450653856369568678699 : Nat.Prime 3754450653856369568678699 := by
  apply lucas_primality 3754450653856369568678699 (2 : ZMod 3754450653856369568678699)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (307, 1), (5503, 1), (101014991469007579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (307, 1), (5503, 1), (101014991469007579, 1)] : List FactorBlock).map factorBlockValue).prod) = 3754450653856369568678699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_11
      · exact prime_oneHundredSeventeenDK_307
      · exact prime_oneHundredSeventeenDK_5503
      · exact prime_oneHundredSeventeenDK_101014991469007579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3754450653856369568678699) ^ 1877225326928184784339349 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3754450653856369568678699) ^ 341313695805124506243518 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3754450653856369568678699) ^ 12229480957186871559214 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3754450653856369568678699) ^ 682255252381677188566 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3754450653856369568678699) ^ 37167262 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_5476058014252977989660701 : Nat.Prime 5476058014252977989660701 := by
  apply lucas_primality 5476058014252977989660701 (6 : ZMod 5476058014252977989660701)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 2), (220589, 1), (9194337137883169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 2), (220589, 1), (9194337137883169, 1)] : List FactorBlock).map factorBlockValue).prod) = 5476058014252977989660701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_220589
      · exact prime_oneHundredSeventeenDK_9194337137883169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 5476058014252977989660701) ^ 2738029007126488994830350 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 5476058014252977989660701) ^ 1825352671417659329886900 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 5476058014252977989660701) ^ 1095211602850595597932140 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 5476058014252977989660701) ^ 24824710272284556300 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 5476058014252977989660701) ^ 595590300 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_8614100475777196663272469 : Nat.Prime 8614100475777196663272469 := by
  apply lucas_primality 8614100475777196663272469 (2 : ZMod 8614100475777196663272469)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (163, 2), (233, 1), (38652385516178669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (163, 2), (233, 1), (38652385516178669, 1)] : List FactorBlock).map factorBlockValue).prod) = 8614100475777196663272469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_163
      · exact prime_oneHundredSeventeenDK_233
      · exact prime_oneHundredSeventeenDK_38652385516178669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8614100475777196663272469) ^ 4307050237888598331636234 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8614100475777196663272469) ^ 2871366825259065554424156 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8614100475777196663272469) ^ 52847242182682188118236 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8614100475777196663272469) ^ 36970388308056638039796 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8614100475777196663272469) ^ 222860772 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_11114923699480130495687369 : Nat.Prime 11114923699480130495687369 := by
  apply lucas_primality 11114923699480130495687369 (3 : ZMod 11114923699480130495687369)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (43, 1), (8231, 1), (23581, 1), (1971517, 1), (84436981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (43, 1), (8231, 1), (23581, 1), (1971517, 1), (84436981, 1)] : List FactorBlock).map factorBlockValue).prod) = 11114923699480130495687369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_43
      · exact prime_oneHundredSeventeenDK_8231
      · exact prime_oneHundredSeventeenDK_23581
      · exact prime_oneHundredSeventeenDK_1971517
      · exact prime_oneHundredSeventeenDK_84436981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11114923699480130495687369) ^ 5557461849740065247843684 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 11114923699480130495687369) ^ 258486597662328616178776 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 11114923699480130495687369) ^ 1350373429653763879928 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 11114923699480130495687369) ^ 471350820553841249128 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 11114923699480130495687369) ^ 5637751893328908904 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (3 : ZMod 11114923699480130495687369) ^ 131635730788149928 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_11218590871048679969085913 : Nat.Prime 11218590871048679969085913 := by
  apply lucas_primality 11218590871048679969085913 (5 : ZMod 11218590871048679969085913)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (47, 1), (241, 1), (9439, 1), (1997243, 1), (729682649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (47, 1), (241, 1), (9439, 1), (1997243, 1), (729682649, 1)] : List FactorBlock).map factorBlockValue).prod) = 11218590871048679969085913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_47
      · exact prime_oneHundredSeventeenDK_241
      · exact prime_oneHundredSeventeenDK_9439
      · exact prime_oneHundredSeventeenDK_1997243
      · exact prime_oneHundredSeventeenDK_729682649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 11218590871048679969085913) ^ 5609295435524339984542956 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 11218590871048679969085913) ^ 3739530290349559989695304 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 11218590871048679969085913) ^ 238693422788269786576296 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 11218590871048679969085913) ^ 46550169589413609830232 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 11218590871048679969085913) ^ 1188535954131653773608 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 11218590871048679969085913) ^ 5617038523128472584 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 11218590871048679969085913) ^ 15374616467067288 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_17375358050499965333353763 : Nat.Prime 17375358050499965333353763 := by
  apply lucas_primality 17375358050499965333353763 (2 : ZMod 17375358050499965333353763)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (64217, 1), (212627, 1), (27663524209333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (64217, 1), (212627, 1), (27663524209333, 1)] : List FactorBlock).map factorBlockValue).prod) = 17375358050499965333353763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_23
      · exact prime_oneHundredSeventeenDK_64217
      · exact prime_oneHundredSeventeenDK_212627
      · exact prime_oneHundredSeventeenDK_27663524209333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17375358050499965333353763) ^ 8687679025249982666676881 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 17375358050499965333353763) ^ 755450350021737623189294 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 17375358050499965333353763) ^ 270572559454660998386 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 17375358050499965333353763) ^ 81717552570933914006 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 17375358050499965333353763) ^ 628096330714 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_28473698114456612601652801 : Nat.Prime 28473698114456612601652801 := by
  apply lucas_primality 28473698114456612601652801 (7 : ZMod 28473698114456612601652801)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 2), (21121, 1), (280858881705970091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 2), (21121, 1), (280858881705970091, 1)] : List FactorBlock).map factorBlockValue).prod) = 28473698114456612601652801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_21121
      · exact prime_oneHundredSeventeenDK_280858881705970091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 28473698114456612601652801) ^ 14236849057228306300826400 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 28473698114456612601652801) ^ 9491232704818870867217600 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 28473698114456612601652801) ^ 5694739622891322520330560 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 28473698114456612601652801) ^ 1348122632188656436800 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (7 : ZMod 28473698114456612601652801) ^ 101380800 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_35242095653510885100338677 : Nat.Prime 35242095653510885100338677 := by
  apply lucas_primality 35242095653510885100338677 (2 : ZMod 35242095653510885100338677)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (768073, 1), (159289451, 1), (1846492777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (768073, 1), (159289451, 1), (1846492777, 1)] : List FactorBlock).map factorBlockValue).prod) = 35242095653510885100338677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_13
      · exact prime_oneHundredSeventeenDK_768073
      · exact prime_oneHundredSeventeenDK_159289451
      · exact prime_oneHundredSeventeenDK_1846492777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 35242095653510885100338677) ^ 17621047826755442550169338 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 35242095653510885100338677) ^ 11747365217836961700112892 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 35242095653510885100338677) ^ 2710930434885452700026052 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 35242095653510885100338677) ^ 45883784032912086612 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 35242095653510885100338677) ^ 221245634486560476 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 35242095653510885100338677) ^ 19085964533675988 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_695101635377036301602157323 : Nat.Prime 695101635377036301602157323 := by
  apply lucas_primality 695101635377036301602157323 (2 : ZMod 695101635377036301602157323)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (853, 1), (954469, 1), (13770374832918083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (853, 1), (954469, 1), (13770374832918083, 1)] : List FactorBlock).map factorBlockValue).prod) = 695101635377036301602157323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_31
      · exact prime_oneHundredSeventeenDK_853
      · exact prime_oneHundredSeventeenDK_954469
      · exact prime_oneHundredSeventeenDK_13770374832918083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 695101635377036301602157323) ^ 347550817688518150801078661 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 695101635377036301602157323) ^ 22422633399259235535553462 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 695101635377036301602157323) ^ 814890545576830365301474 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 695101635377036301602157323) ^ 728260043413705737538 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 695101635377036301602157323) ^ 50478047534 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_892420809290517574315027789 : Nat.Prime 892420809290517574315027789 := by
  apply lucas_primality 892420809290517574315027789 (2 : ZMod 892420809290517574315027789)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (73, 1), (569, 1), (1509971, 1), (3062539, 1), (387171233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (73, 1), (569, 1), (1509971, 1), (3062539, 1), (387171233, 1)] : List FactorBlock).map factorBlockValue).prod) = 892420809290517574315027789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_73
      · exact prime_oneHundredSeventeenDK_569
      · exact prime_oneHundredSeventeenDK_1509971
      · exact prime_oneHundredSeventeenDK_3062539
      · exact prime_oneHundredSeventeenDK_387171233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 892420809290517574315027789) ^ 446210404645258787157513894 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 892420809290517574315027789) ^ 297473603096839191438342596 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 892420809290517574315027789) ^ 12224942593020788689246956 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 892420809290517574315027789) ^ 1568402125290892046247852 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 892420809290517574315027789) ^ 591018509157141146628 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 892420809290517574315027789) ^ 291399002360628737892 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 892420809290517574315027789) ^ 2304977057245669836 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_1143183681322563834866357911 : Nat.Prime 1143183681322563834866357911 := by
  apply lucas_primality 1143183681322563834866357911 (6 : ZMod 1143183681322563834866357911)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (19, 1), (3391, 1), (820351907, 1), (26702345737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (19, 1), (3391, 1), (820351907, 1), (26702345737, 1)] : List FactorBlock).map factorBlockValue).prod) = 1143183681322563834866357911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_19
      · exact prime_oneHundredSeventeenDK_3391
      · exact prime_oneHundredSeventeenDK_820351907
      · exact prime_oneHundredSeventeenDK_26702345737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1143183681322563834866357911) ^ 571591840661281917433178955 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1143183681322563834866357911) ^ 381061227107521278288785970 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1143183681322563834866357911) ^ 228636736264512766973271582 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1143183681322563834866357911) ^ 60167562174871780782439890 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1143183681322563834866357911) ^ 337122878597040352364010 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1143183681322563834866357911) ^ 1393528401126230130 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1143183681322563834866357911) ^ 42812106943043430 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_1686892993171100292912552527 : Nat.Prime 1686892993171100292912552527 := by
  apply lucas_primality 1686892993171100292912552527 (5 : ZMod 1686892993171100292912552527)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (7914209, 1), (1384073961782806691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (7914209, 1), (1384073961782806691, 1)] : List FactorBlock).map factorBlockValue).prod) = 1686892993171100292912552527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_11
      · exact prime_oneHundredSeventeenDK_7914209
      · exact prime_oneHundredSeventeenDK_1384073961782806691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1686892993171100292912552527) ^ 843446496585550146456276263 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1686892993171100292912552527) ^ 240984713310157184701793218 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1686892993171100292912552527) ^ 153353908470100026628413866 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1686892993171100292912552527) ^ 213147390114552230414 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1686892993171100292912552527) ^ 1218788186 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_5123156497778897185882566937 : Nat.Prime 5123156497778897185882566937 := by
  apply lucas_primality 5123156497778897185882566937 (17 : ZMod 5123156497778897185882566937)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 2), (7247, 1), (601135034269270369663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 2), (7247, 1), (601135034269270369663, 1)] : List FactorBlock).map factorBlockValue).prod) = 5123156497778897185882566937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_7247
      · exact prime_oneHundredSeventeenDK_601135034269270369663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 5123156497778897185882566937) ^ 2561578248889448592941283468 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (17 : ZMod 5123156497778897185882566937) ^ 1707718832592965728627522312 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (17 : ZMod 5123156497778897185882566937) ^ 731879499682699597983223848 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (17 : ZMod 5123156497778897185882566937) ^ 706934800300661954723688 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (17 : ZMod 5123156497778897185882566937) ^ 8522472 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_17290653180003778002353663401 : Nat.Prime 17290653180003778002353663401 := by
  apply lucas_primality 17290653180003778002353663401 (17 : ZMod 17290653180003778002353663401)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 2), (13, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 2), (13, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 17290653180003778002353663401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_13
      · exact prime_oneHundredSeventeenDK_171401
      · exact prime_oneHundredSeventeenDK_714027719
      · exact prime_oneHundredSeventeenDK_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 17290653180003778002353663401) ^ 8645326590001889001176831700 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (17 : ZMod 17290653180003778002353663401) ^ 5763551060001259334117887800 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (17 : ZMod 17290653180003778002353663401) ^ 3458130636000755600470732680 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (17 : ZMod 17290653180003778002353663401) ^ 1330050244615675230950281800 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (17 : ZMod 17290653180003778002353663401) ^ 100878368154233510903400 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (17 : ZMod 17290653180003778002353663401) ^ 24215660988931128600 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (17 : ZMod 17290653180003778002353663401) ^ 2863810522505064600 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_17290653180003778002353663407 : Nat.Prime 17290653180003778002353663407 := by
  apply lucas_primality 17290653180003778002353663407 (5 : ZMod 17290653180003778002353663407)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (89, 1), (27259443481, 1), (1187826903350189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (89, 1), (27259443481, 1), (1187826903350189, 1)] : List FactorBlock).map factorBlockValue).prod) = 17290653180003778002353663407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_89
      · exact prime_oneHundredSeventeenDK_27259443481
      · exact prime_oneHundredSeventeenDK_1187826903350189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 17290653180003778002353663407) ^ 8645326590001889001176831703 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 17290653180003778002353663407) ^ 5763551060001259334117887802 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 17290653180003778002353663407) ^ 194277002022514359577007454 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 17290653180003778002353663407) ^ 634299566389000926 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (5 : ZMod 17290653180003778002353663407) ^ 14556542818854 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_19760746491432889145547043897 : Nat.Prime 19760746491432889145547043897 := by
  apply lucas_primality 19760746491432889145547043897 (10 : ZMod 19760746491432889145547043897)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (7, 1), (7247, 1), (601135034269270369663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (7, 1), (7247, 1), (601135034269270369663, 1)] : List FactorBlock).map factorBlockValue).prod) = 19760746491432889145547043897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_7247
      · exact prime_oneHundredSeventeenDK_601135034269270369663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 19760746491432889145547043897) ^ 9880373245716444572773521948 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (10 : ZMod 19760746491432889145547043897) ^ 6586915497144296381849014632 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (10 : ZMod 19760746491432889145547043897) ^ 2822963784490412735078149128 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (10 : ZMod 19760746491432889145547043897) ^ 2726748515445410396791368 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (10 : ZMod 19760746491432889145547043897) ^ 32872392 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_46108408480010074672943102429 : Nat.Prime 46108408480010074672943102429 := by
  apply lucas_primality 46108408480010074672943102429 (2 : ZMod 46108408480010074672943102429)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (479, 1), (308181357101, 1), (78086914741933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (479, 1), (308181357101, 1), (78086914741933, 1)] : List FactorBlock).map factorBlockValue).prod) = 46108408480010074672943102429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_479
      · exact prime_oneHundredSeventeenDK_308181357101
      · exact prime_oneHundredSeventeenDK_78086914741933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 46108408480010074672943102429) ^ 23054204240005037336471551214 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 46108408480010074672943102429) ^ 96259725427995980528064932 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 46108408480010074672943102429) ^ 149614528645543628 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 46108408480010074672943102429) ^ 590475480205516 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_138325225440030224018829307261 : Nat.Prime 138325225440030224018829307261 := by
  apply lucas_primality 138325225440030224018829307261 (6 : ZMod 138325225440030224018829307261)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (421, 1), (5476058014252977989660701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (421, 1), (5476058014252977989660701, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_3
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_421
      · exact prime_oneHundredSeventeenDK_5476058014252977989660701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 138325225440030224018829307261) ^ 69162612720015112009414653630 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 138325225440030224018829307261) ^ 46108408480010074672943102420 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 138325225440030224018829307261) ^ 27665045088006044803765861452 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 138325225440030224018829307261) ^ 328563480855178679379642060 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (6 : ZMod 138325225440030224018829307261) ^ 25260 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSeventeenDK_138325225440030224018829307301 : Nat.Prime 138325225440030224018829307301 := by
  apply lucas_primality 138325225440030224018829307301 (2 : ZMod 138325225440030224018829307301)
  · rw [← oneHundredSeventeenDKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 1), (19, 1), (197, 1), (401, 1), (131655542491839391273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 1), (19, 1), (197, 1), (401, 1), (131655542491839391273, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSeventeenDK_2
      · exact prime_oneHundredSeventeenDK_5
      · exact prime_oneHundredSeventeenDK_7
      · exact prime_oneHundredSeventeenDK_19
      · exact prime_oneHundredSeventeenDK_197
      · exact prime_oneHundredSeventeenDK_401
      · exact prime_oneHundredSeventeenDK_131655542491839391273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 138325225440030224018829307301) ^ 69162612720015112009414653650 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 138325225440030224018829307301) ^ 27665045088006044803765861460 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 138325225440030224018829307301) ^ 19760746491432889145547043900 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 138325225440030224018829307301) ^ 7280275023159485474675226700 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 138325225440030224018829307301) ^ 702158504771727025476290900 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 138325225440030224018829307301) ^ 344950686882868389074387300 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide
    · change (2 : ZMod 138325225440030224018829307301) ^ 1050660100 ≠ 1
      rw [← oneHundredSeventeenDKFastPow_eq_pow]
      decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307200 : Nat.totient 138325225440030224018829307200 = 34049087556049349416194048000 := by
  rw [← show ((([(2, 6), (3, 2), (5, 2), (13, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307200 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_3, prime_oneHundredSeventeenDK_5, prime_oneHundredSeventeenDK_13, prime_oneHundredSeventeenDK_171401, prime_oneHundredSeventeenDK_714027719, prime_oneHundredSeventeenDK_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307201 : Nat.totient 138325225440030224018829307201 = 138113367744597888119839594512 := by
  rw [← show ((([(653, 1), (5052643, 1), (41924664091911494519, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307201 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_653, prime_oneHundredSeventeenDK_5052643, prime_oneHundredSeventeenDK_41924664091911494519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307202 : Nat.totient 138325225440030224018829307202 = 55819371083036234378005592640 := by
  rw [← show ((([(2, 1), (7, 1), (31, 1), (37, 1), (8614100475777196663272469, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307202 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_7, prime_oneHundredSeventeenDK_31, prime_oneHundredSeventeenDK_37, prime_oneHundredSeventeenDK_8614100475777196663272469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307203 : Nat.totient 138325225440030224018829307203 = 91814066674002363255652253664 := by
  rw [← show ((([(3, 1), (229, 1), (1617523, 1), (124478453735397502303, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307203 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_3, prime_oneHundredSeventeenDK_229, prime_oneHundredSeventeenDK_1617523, prime_oneHundredSeventeenDK_124478453735397502303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307204 : Nat.totient 138325225440030224018829307204 = 69097426463856713794191214080 := by
  rw [← show ((([(2, 2), (1061, 1), (14477129489, 1), (2251352778015469, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307204 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_1061, prime_oneHundredSeventeenDK_14477129489, prime_oneHundredSeventeenDK_2251352778015469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307205 : Nat.totient 138325225440030224018829307205 = 104035685827134021439633764480 := by
  rw [← show ((([(5, 1), (19, 1), (131, 1), (11114923699480130495687369, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307205 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_5, prime_oneHundredSeventeenDK_19, prime_oneHundredSeventeenDK_131, prime_oneHundredSeventeenDK_11114923699480130495687369]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307206 : Nat.totient 138325225440030224018829307206 = 46088985399146834513982968256 := by
  rw [← show ((([(2, 1), (3, 1), (2399, 1), (226777, 1), (42376090025613958487, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307206 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_3, prime_oneHundredSeventeenDK_2399, prime_oneHundredSeventeenDK_226777, prime_oneHundredSeventeenDK_42376090025613958487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307207 : Nat.totient 138325225440030224018829307207 = 138311923412122376426083221984 := by
  rw [← show ((([(13099, 1), (96059, 1), (106219, 1), (1034958593446733, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307207 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_13099, prime_oneHundredSeventeenDK_96059, prime_oneHundredSeventeenDK_106219, prime_oneHundredSeventeenDK_1034958593446733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307208 : Nat.totient 138325225440030224018829307208 = 69162612720015112009414653600 := by
  rw [← show ((([(2, 3), (17290653180003778002353663401, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307208 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_17290653180003778002353663401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307209 : Nat.totient 138325225440030224018829307209 = 71623210737770650355496053760 := by
  rw [← show ((([(3, 2), (7, 1), (11, 1), (317, 1), (9719, 1), (6998309863, 1), (9257508937, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307209 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_3, prime_oneHundredSeventeenDK_7, prime_oneHundredSeventeenDK_11, prime_oneHundredSeventeenDK_317, prime_oneHundredSeventeenDK_9719, prime_oneHundredSeventeenDK_6998309863, prime_oneHundredSeventeenDK_9257508937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307210 : Nat.totient 138325225440030224018829307210 = 54248569075018596789374223360 := by
  rw [← show ((([(2, 1), (5, 1), (53, 1), (2111, 1), (4643, 1), (350437, 1), (75985136210957, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307210 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_5, prime_oneHundredSeventeenDK_53, prime_oneHundredSeventeenDK_2111, prime_oneHundredSeventeenDK_4643, prime_oneHundredSeventeenDK_350437, prime_oneHundredSeventeenDK_75985136210957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307211 : Nat.totient 138325225440030224018829307211 = 138324842745763393853124552000 := by
  rw [← show ((([(361451, 1), (382694266830165704393761, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307211 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_361451, prime_oneHundredSeventeenDK_382694266830165704393761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307212 : Nat.totient 138325225440030224018829307212 = 45650654296509439240340659200 := by
  rw [← show ((([(2, 2), (3, 1), (101, 1), (50287, 1), (139409, 1), (16279918539612547, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307212 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_3, prime_oneHundredSeventeenDK_101, prime_oneHundredSeventeenDK_50287, prime_oneHundredSeventeenDK_139409, prime_oneHundredSeventeenDK_16279918539612547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307213 : Nat.totient 138325225440030224018829307213 = 117099687894507203523078094848 := by
  rw [← show ((([(13, 1), (17, 1), (73, 1), (83, 1), (906208483, 1), (113993486613649, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307213 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_13, prime_oneHundredSeventeenDK_17, prime_oneHundredSeventeenDK_73, prime_oneHundredSeventeenDK_83, prime_oneHundredSeventeenDK_906208483, prime_oneHundredSeventeenDK_113993486613649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307214 : Nat.totient 138325225440030224018829307214 = 67475719726844011716502101040 := by
  rw [← show ((([(2, 1), (41, 1), (1686892993171100292912552527, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307214 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_41, prime_oneHundredSeventeenDK_1686892993171100292912552527]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307215 : Nat.totient 138325225440030224018829307215 = 73769329132746767142208413696 := by
  rw [← show ((([(3, 1), (5, 1), (17903, 1), (19916623, 1), (25862387424264449, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307215 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_3, prime_oneHundredSeventeenDK_5, prime_oneHundredSeventeenDK_17903, prime_oneHundredSeventeenDK_19916623, prime_oneHundredSeventeenDK_25862387424264449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307216 : Nat.totient 138325225440030224018829307216 = 59282239474203788026021440000 := by
  rw [← show ((([(2, 4), (7, 1), (625014320243, 1), (1976029373590001, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307216 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_7, prime_oneHundredSeventeenDK_625014320243, prime_oneHundredSeventeenDK_1976029373590001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307217 : Nat.totient 138325225440030224018829307217 = 128777677272142256717725766400 := by
  rw [← show ((([(23, 1), (71, 1), (79, 1), (6911, 1), (425525917, 1), (364603809013, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307217 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_23, prime_oneHundredSeventeenDK_71, prime_oneHundredSeventeenDK_79, prime_oneHundredSeventeenDK_6911, prime_oneHundredSeventeenDK_425525917, prime_oneHundredSeventeenDK_364603809013]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307218 : Nat.totient 138325225440030224018829307218 = 45776692871141082857350134480 := by
  rw [← show ((([(2, 1), (3, 3), (139, 1), (104050223, 1), (177112743868002511, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307218 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_3, prime_oneHundredSeventeenDK_139, prime_oneHundredSeventeenDK_104050223, prime_oneHundredSeventeenDK_177112743868002511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307219 : Nat.totient 138325225440030224018829307219 = 137409075759451492558247414400 := by
  rw [← show ((([(151, 1), (1551157, 1), (590566329281522909617, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307219 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_151, prime_oneHundredSeventeenDK_1551157, prime_oneHundredSeventeenDK_590566329281522909617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307220 : Nat.totient 138325225440030224018829307220 = 48548154522303782140341872640 := by
  rw [← show ((([(2, 2), (5, 1), (11, 1), (29, 1), (2789, 1), (1697173, 1), (4580428198607927, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307220 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_5, prime_oneHundredSeventeenDK_11, prime_oneHundredSeventeenDK_29, prime_oneHundredSeventeenDK_2789, prime_oneHundredSeventeenDK_1697173, prime_oneHundredSeventeenDK_4580428198607927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307221 : Nat.totient 138325225440030224018829307221 = 90481886988344837872330752000 := by
  rw [← show ((([(3, 1), (97, 2), (233, 1), (239, 1), (7351, 1), (35410211, 1), (338070989, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307221 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_3, prime_oneHundredSeventeenDK_97, prime_oneHundredSeventeenDK_233, prime_oneHundredSeventeenDK_239, prime_oneHundredSeventeenDK_7351, prime_oneHundredSeventeenDK_35410211, prime_oneHundredSeventeenDK_338070989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307222 : Nat.totient 138325225440030224018829307222 = 67968543332582670445716153600 := by
  rw [← show ((([(2, 1), (61, 1), (1129, 1), (258343691, 1), (3887315177361709, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307222 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_61, prime_oneHundredSeventeenDK_1129, prime_oneHundredSeventeenDK_258343691, prime_oneHundredSeventeenDK_3887315177361709]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307223 : Nat.totient 138325225440030224018829307223 = 118482879166129272619692806400 := by
  rw [← show ((([(7, 2), (1453, 1), (34608107059, 1), (56138634761201, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307223 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_7, prime_oneHundredSeventeenDK_1453, prime_oneHundredSeventeenDK_34608107059, prime_oneHundredSeventeenDK_56138634761201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307224 : Nat.totient 138325225440030224018829307224 = 43681650138699257459869447680 := by
  rw [← show ((([(2, 3), (3, 1), (19, 1), (169551237041, 1), (1789103977804019, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307224 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_3, prime_oneHundredSeventeenDK_19, prime_oneHundredSeventeenDK_169551237041, prime_oneHundredSeventeenDK_1789103977804019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307225 : Nat.totient 138325225440030224018829307225 = 109955338438953961513056669120 := by
  rw [← show ((([(5, 2), (157, 1), (35242095653510885100338677, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307225 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_5, prime_oneHundredSeventeenDK_157, prime_oneHundredSeventeenDK_35242095653510885100338677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307226 : Nat.totient 138325225440030224018829307226 = 63842411741534934473606570544 := by
  rw [← show ((([(2, 1), (13, 1), (3662228970263, 1), (1452722104942727, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307226 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_13, prime_oneHundredSeventeenDK_3662228970263, prime_oneHundredSeventeenDK_1452722104942727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307227 : Nat.totient 138325225440030224018829307227 = 90254181750931538779640990976 := by
  rw [← show ((([(3, 2), (47, 1), (160183, 1), (7631857, 1), (267494201311979, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307227 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_3, prime_oneHundredSeventeenDK_47, prime_oneHundredSeventeenDK_160183, prime_oneHundredSeventeenDK_7631857, prime_oneHundredSeventeenDK_267494201311979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307228 : Nat.totient 138325225440030224018829307228 = 69162569749210994158361428224 := by
  rw [← show ((([(2, 2), (1611217, 1), (1533463643, 1), (13996320415397, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307228 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_1611217, prime_oneHundredSeventeenDK_1533463643, prime_oneHundredSeventeenDK_13996320415397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307229 : Nat.totient 138325225440030224018829307229 = 137863031800276843537157683200 := by
  rw [← show ((([(431, 1), (977, 1), (411751841, 1), (797799947097187, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307229 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_431, prime_oneHundredSeventeenDK_977, prime_oneHundredSeventeenDK_411751841, prime_oneHundredSeventeenDK_797799947097187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307230 : Nat.totient 138325225440030224018829307230 = 29035450280726825571385344000 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (7, 1), (17, 1), (43, 1), (1439, 1), (3001, 1), (38398499, 1), (5434050593, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307230 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_3, prime_oneHundredSeventeenDK_5, prime_oneHundredSeventeenDK_7, prime_oneHundredSeventeenDK_17, prime_oneHundredSeventeenDK_43, prime_oneHundredSeventeenDK_1439, prime_oneHundredSeventeenDK_3001, prime_oneHundredSeventeenDK_38398499, prime_oneHundredSeventeenDK_5434050593]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307231 : Nat.totient 138325225440030224018829307231 = 125750204945482021835299370100 := by
  rw [← show ((([(11, 2), (1143183681322563834866357911, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307231 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_11, prime_oneHundredSeventeenDK_1143183681322563834866357911]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307232 : Nat.totient 138325225440030224018829307232 = 68904249292999339890208964608 := by
  rw [← show ((([(2, 5), (293, 1), (3089, 1), (59130884849, 1), (80770263887, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307232 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_293, prime_oneHundredSeventeenDK_3089, prime_oneHundredSeventeenDK_59130884849, prime_oneHundredSeventeenDK_80770263887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307233 : Nat.totient 138325225440030224018829307233 = 89173485908598720434184600000 := by
  rw [← show ((([(3, 1), (31, 1), (1301, 1), (2851881371, 1), (400875657510611, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307233 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_3, prime_oneHundredSeventeenDK_31, prime_oneHundredSeventeenDK_1301, prime_oneHundredSeventeenDK_2851881371, prime_oneHundredSeventeenDK_400875657510611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307234 : Nat.totient 138325225440030224018829307234 = 69162569721088353515417802816 := by
  rw [← show ((([(2, 1), (1608473, 1), (42998926758493995242329, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307234 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_1608473, prime_oneHundredSeventeenDK_42998926758493995242329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307235 : Nat.totient 138325225440030224018829307235 = 109640589179388863624458695936 := by
  rw [← show ((([(5, 1), (109, 1), (25147, 1), (10092963498666755004889, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307235 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_5, prime_oneHundredSeventeenDK_109, prime_oneHundredSeventeenDK_25147, prime_oneHundredSeventeenDK_10092963498666755004889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307236 : Nat.totient 138325225440030224018829307236 = 46108408480008290810745329664 := by
  rw [← show ((([(2, 2), (3, 2), (33312673606897, 1), (115342509540833, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307236 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_3, prime_oneHundredSeventeenDK_33312673606897, prime_oneHundredSeventeenDK_115342509540833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307237 : Nat.totient 138325225440030224018829307237 = 118564321614263958725813065392 := by
  rw [← show ((([(7, 1), (753583, 1), (26222388896024577446077, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307237 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_7, prime_oneHundredSeventeenDK_753583, prime_oneHundredSeventeenDK_26222388896024577446077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307238 : Nat.totient 138325225440030224018829307238 = 69162452587235657283202046016 := by
  rw [← show ((([(2, 1), (431929, 1), (8846288837, 1), (18100805924303, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307238 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_431929, prime_oneHundredSeventeenDK_8846288837, prime_oneHundredSeventeenDK_18100805924303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307239 : Nat.totient 138325225440030224018829307239 = 82819931676784100601026153472 := by
  rw [← show ((([(3, 1), (13, 1), (37, 1), (31177, 1), (3074685732733041494149, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307239 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_3, prime_oneHundredSeventeenDK_13, prime_oneHundredSeventeenDK_37, prime_oneHundredSeventeenDK_31177, prime_oneHundredSeventeenDK_3074685732733041494149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307240 : Nat.totient 138325225440030224018829307240 = 52918513842314186283383147520 := by
  rw [← show ((([(2, 3), (5, 1), (23, 1), (11813, 1), (37087, 1), (4027627, 1), (85208399431, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307240 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_5, prime_oneHundredSeventeenDK_23, prime_oneHundredSeventeenDK_11813, prime_oneHundredSeventeenDK_37087, prime_oneHundredSeventeenDK_4027627, prime_oneHundredSeventeenDK_85208399431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307241 : Nat.totient 138325225440030224018829307241 = 138324821378460951546896282112 := by
  rw [← show ((([(342337, 1), (404061569272471932682793, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307241 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_342337, prime_oneHundredSeventeenDK_404061569272471932682793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307242 : Nat.totient 138325225440030224018829307242 = 41914449570182292504214060800 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (18341, 1), (114270582252405377601457, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307242 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_3, prime_oneHundredSeventeenDK_11, prime_oneHundredSeventeenDK_18341, prime_oneHundredSeventeenDK_114270582252405377601457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307243 : Nat.totient 138325225440030224018829307243 = 130732193971961739168153705288 := by
  rw [← show ((([(19, 1), (419, 1), (17375358050499965333353763, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307243 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_19, prime_oneHundredSeventeenDK_419, prime_oneHundredSeventeenDK_17375358050499965333353763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307244 : Nat.totient 138325225440030224018829307244 = 59282232306311917276463206656 := by
  rw [← show ((([(2, 2), (7, 1), (8270417, 1), (597332229180006556669, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307244 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_7, prime_oneHundredSeventeenDK_8270417, prime_oneHundredSeventeenDK_597332229180006556669]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307245 : Nat.totient 138325225440030224018829307245 = 73773453357232940345745808512 := by
  rw [← show ((([(3, 3), (5, 1), (349996873, 1), (2927544154246713619, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307245 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_3, prime_oneHundredSeventeenDK_5, prime_oneHundredSeventeenDK_349996873, prime_oneHundredSeventeenDK_2927544154246713619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307246 : Nat.totient 138325225440030224018829307246 = 67990364805145750068526965120 := by
  rw [← show ((([(2, 1), (59, 1), (430764149, 1), (1373986741, 1), (1980602333, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307246 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_59, prime_oneHundredSeventeenDK_430764149, prime_oneHundredSeventeenDK_1373986741, prime_oneHundredSeventeenDK_1980602333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307247 : Nat.totient 138325225440030224018829307247 = 130184411147790685644121113600 := by
  rw [← show ((([(17, 1), (36809, 1), (260651, 1), (848084353418624149, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307247 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_17, prime_oneHundredSeventeenDK_36809, prime_oneHundredSeventeenDK_260651, prime_oneHundredSeventeenDK_848084353418624149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307248 : Nat.totient 138325225440030224018829307248 = 45590336472944204386190929920 := by
  rw [← show ((([(2, 4), (3, 1), (89, 1), (27259443481, 1), (1187826903350189, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307248 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_3, prime_oneHundredSeventeenDK_89, prime_oneHundredSeventeenDK_27259443481, prime_oneHundredSeventeenDK_1187826903350189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307249 : Nat.totient 138325225440030224018829307249 = 131460118980007220359231746240 := by
  rw [← show ((([(29, 1), (67, 1), (1291, 1), (55144517844561571008773, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307249 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_29, prime_oneHundredSeventeenDK_67, prime_oneHundredSeventeenDK_1291, prime_oneHundredSeventeenDK_55144517844561571008773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307250 : Nat.totient 138325225440030224018829307250 = 55321872429067783638481958400 := by
  rw [← show ((([(2, 1), (5, 3), (6733, 1), (82177469443059690490913, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307250 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_5, prime_oneHundredSeventeenDK_6733, prime_oneHundredSeventeenDK_82177469443059690490913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307251 : Nat.totient 138325225440030224018829307251 = 78186424209721260734467584000 := by
  rw [← show ((([(3, 1), (7, 1), (149, 1), (241, 1), (266009, 1), (689576496218686451, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307251 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_3, prime_oneHundredSeventeenDK_7, prime_oneHundredSeventeenDK_149, prime_oneHundredSeventeenDK_241, prime_oneHundredSeventeenDK_266009, prime_oneHundredSeventeenDK_689576496218686451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307252 : Nat.totient 138325225440030224018829307252 = 63806528289284581026551241600 := by
  rw [← show ((([(2, 2), (13, 1), (2411, 1), (7039, 1), (188911, 1), (829722028640579, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307252 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_13, prime_oneHundredSeventeenDK_2411, prime_oneHundredSeventeenDK_7039, prime_oneHundredSeventeenDK_188911, prime_oneHundredSeventeenDK_829722028640579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307253 : Nat.totient 138325225440030224018829307253 = 125742275190714365289786240000 := by
  rw [← show ((([(11, 1), (23677, 1), (78301, 1), (204557, 1), (316847, 1), (104652781, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307253 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_11, prime_oneHundredSeventeenDK_23677, prime_oneHundredSeventeenDK_78301, prime_oneHundredSeventeenDK_204557, prime_oneHundredSeventeenDK_316847, prime_oneHundredSeventeenDK_104652781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307254 : Nat.totient 138325225440030224018829307254 = 45958212688842773439358531824 := by
  rw [← show ((([(2, 1), (3, 2), (307, 1), (8302403, 1), (3014995691311940443, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307254 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_3, prime_oneHundredSeventeenDK_307, prime_oneHundredSeventeenDK_8302403, prime_oneHundredSeventeenDK_3014995691311940443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307255 : Nat.totient 138325225440030224018829307255 = 107958384950659641802297171200 := by
  rw [← show ((([(5, 1), (41, 1), (39023, 1), (11801231711, 1), (1465208853187, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307255 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_5, prime_oneHundredSeventeenDK_41, prime_oneHundredSeventeenDK_39023, prime_oneHundredSeventeenDK_11801231711, prime_oneHundredSeventeenDK_1465208853187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307256 : Nat.totient 138325225440030224018829307256 = 69162612720015112009414653624 := by
  rw [← show ((([(2, 3), (17290653180003778002353663407, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307256 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_17290653180003778002353663407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307257 : Nat.totient 138325225440030224018829307257 = 92209308058712436606748822880 := by
  rw [← show ((([(3, 1), (12281, 1), (3754450653856369568678699, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307257 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_3, prime_oneHundredSeventeenDK_12281, prime_oneHundredSeventeenDK_3754450653856369568678699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307258 : Nat.totient 138325225440030224018829307258 = 59111397285611927761031212800 := by
  rw [← show ((([(2, 1), (7, 1), (347, 1), (28473698114456612601652801, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307258 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_7, prime_oneHundredSeventeenDK_347, prime_oneHundredSeventeenDK_28473698114456612601652801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307259 : Nat.totient 138325225440030224018829307259 = 138324975737929462358307491280 := by
  rw [← show ((([(553961, 1), (249702100761660521262019, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307259 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_553961, prime_oneHundredSeventeenDK_249702100761660521262019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307260 : Nat.totient 138325225440030224018829307260 = 36799109855780012090519904000 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (421, 1), (5476058014252977989660701, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307260 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_3, prime_oneHundredSeventeenDK_5, prime_oneHundredSeventeenDK_421, prime_oneHundredSeventeenDK_5476058014252977989660701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307261 : Nat.totient 138325225440030224018829307261 = 138325225440030224018829307260 := by
  rw [← show ((([(138325225440030224018829307261, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307261 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_138325225440030224018829307261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307262 : Nat.totient 138325225440030224018829307262 = 64279916632895875365180988800 := by
  rw [← show ((([(2, 1), (19, 1), (103, 1), (107, 1), (34148237, 1), (41838787, 1), (231179551, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307262 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_19, prime_oneHundredSeventeenDK_103, prime_oneHundredSeventeenDK_107, prime_oneHundredSeventeenDK_34148237, prime_oneHundredSeventeenDK_41838787, prime_oneHundredSeventeenDK_231179551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307263 : Nat.totient 138325225440030224018829307263 = 86542378136296975179972951552 := by
  rw [← show ((([(3, 2), (23, 1), (53, 1), (119929, 1), (105131039647847779157, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307263 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_3, prime_oneHundredSeventeenDK_23, prime_oneHundredSeventeenDK_53, prime_oneHundredSeventeenDK_119929, prime_oneHundredSeventeenDK_105131039647847779157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307264 : Nat.totient 138325225440030224018829307264 = 57015365112607572925494067200 := by
  rw [← show ((([(2, 7), (11, 1), (17, 1), (31, 1), (227, 1), (2152359269, 1), (381546518033, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307264 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_11, prime_oneHundredSeventeenDK_17, prime_oneHundredSeventeenDK_31, prime_oneHundredSeventeenDK_227, prime_oneHundredSeventeenDK_2152359269, prime_oneHundredSeventeenDK_381546518033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307265 : Nat.totient 138325225440030224018829307265 = 87551113367794798632527705088 := by
  rw [← show ((([(5, 1), (7, 1), (13, 1), (28403, 1), (79847, 1), (5816549, 1), (23046330287, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307265 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_5, prime_oneHundredSeventeenDK_7, prime_oneHundredSeventeenDK_13, prime_oneHundredSeventeenDK_28403, prime_oneHundredSeventeenDK_79847, prime_oneHundredSeventeenDK_5816549, prime_oneHundredSeventeenDK_23046330287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307266 : Nat.totient 138325225440030224018829307266 = 46108377178924457709301398000 := by
  rw [← show ((([(2, 1), (3, 1), (1473061, 1), (15650542808481819379151, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307266 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_3, prime_oneHundredSeventeenDK_1473061, prime_oneHundredSeventeenDK_15650542808481819379151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307267 : Nat.totient 138325225440030224018829307267 = 138228737626243494674674840800 := by
  rw [← show ((([(1459, 1), (82301, 1), (1151969505208148903813, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307267 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_1459, prime_oneHundredSeventeenDK_82301, prime_oneHundredSeventeenDK_1151969505208148903813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307268 : Nat.totient 138325225440030224018829307268 = 69162612448369696400560537440 := by
  rw [← show ((([(2, 2), (254606221, 1), (135822707804172451877, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307268 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_254606221, prime_oneHundredSeventeenDK_135822707804172451877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307269 : Nat.totient 138325225440030224018829307269 = 92216816960015310959141096400 := by
  rw [← show ((([(3, 1), (19211985866123, 1), (2399981386688101, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307269 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_3, prime_oneHundredSeventeenDK_19211985866123, prime_oneHundredSeventeenDK_2399981386688101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307270 : Nat.totient 138325225440030224018829307270 = 55330090174611624477402811360 := by
  rw [← show ((([(2, 1), (5, 1), (39508371347, 1), (350116243023856541, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307270 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_5, prime_oneHundredSeventeenDK_39508371347, prime_oneHundredSeventeenDK_350116243023856541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307271 : Nat.totient 138325225440030224018829307271 = 138325221351152580930129759168 := by
  rw [← show ((([(49557307, 1), (106596317, 1), (26184934309609, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307271 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_49557307, prime_oneHundredSeventeenDK_106596317, prime_oneHundredSeventeenDK_26184934309609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307272 : Nat.totient 138325225440030224018829307272 = 39516039485834887470234769344 := by
  rw [← show ((([(2, 3), (3, 4), (7, 2), (7247, 1), (601135034269270369663, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307272 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_3, prime_oneHundredSeventeenDK_7, prime_oneHundredSeventeenDK_7247, prime_oneHundredSeventeenDK_601135034269270369663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307273 : Nat.totient 138325225440030224018829307273 = 134481424525582341469462200000 := by
  rw [← show ((([(43, 1), (491, 1), (661, 1), (911, 1), (10880067820548607651, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307273 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_43, prime_oneHundredSeventeenDK_491, prime_oneHundredSeventeenDK_661, prime_oneHundredSeventeenDK_911, prime_oneHundredSeventeenDK_10880067820548607651]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307274 : Nat.totient 138325225440030224018829307274 = 67621282395162562887210467712 := by
  rw [← show ((([(2, 1), (47, 1), (1069, 1), (10463, 1), (131564767494176166793, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307274 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_47, prime_oneHundredSeventeenDK_1069, prime_oneHundredSeventeenDK_10463, prime_oneHundredSeventeenDK_131564767494176166793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307275 : Nat.totient 138325225440030224018829307275 = 66970924051212997252718400000 := by
  rw [← show ((([(3, 1), (5, 2), (11, 1), (701, 1), (374317, 1), (638983830804654331, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307275 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_3, prime_oneHundredSeventeenDK_5, prime_oneHundredSeventeenDK_11, prime_oneHundredSeventeenDK_701, prime_oneHundredSeventeenDK_374317, prime_oneHundredSeventeenDK_638983830804654331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307276 : Nat.totient 138325225440030224018829307276 = 67276987992676164363320828160 := by
  rw [← show ((([(2, 2), (37, 1), (4813, 1), (28229, 1), (6879047620673288231, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307276 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_37, prime_oneHundredSeventeenDK_4813, prime_oneHundredSeventeenDK_28229, prime_oneHundredSeventeenDK_6879047620673288231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307277 : Nat.totient 138325225440030224018829307277 = 137630123804653187717227149756 := by
  rw [← show ((([(199, 1), (695101635377036301602157323, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307277 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_199, prime_oneHundredSeventeenDK_695101635377036301602157323]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307278 : Nat.totient 138325225440030224018829307278 = 40639589391783839901740040192 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (29, 1), (113, 1), (449, 1), (1205269042013298899237, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307278 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_3, prime_oneHundredSeventeenDK_13, prime_oneHundredSeventeenDK_29, prime_oneHundredSeventeenDK_113, prime_oneHundredSeventeenDK_449, prime_oneHundredSeventeenDK_1205269042013298899237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307279 : Nat.totient 138325225440030224018829307279 = 118564478948597334873282263376 := by
  rw [← show ((([(7, 1), (19760746491432889145547043897, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307279 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_7, prime_oneHundredSeventeenDK_19760746491432889145547043897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307280 : Nat.totient 138325225440030224018829307280 = 54792077424692159165644800000 := by
  rw [← show ((([(2, 4), (5, 1), (193, 1), (331, 1), (647, 1), (271231, 1), (4302461, 1), (35848051, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307280 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_5, prime_oneHundredSeventeenDK_193, prime_oneHundredSeventeenDK_331, prime_oneHundredSeventeenDK_647, prime_oneHundredSeventeenDK_271231, prime_oneHundredSeventeenDK_4302461, prime_oneHundredSeventeenDK_35848051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307281 : Nat.totient 138325225440030224018829307281 = 81672982358474656050521610240 := by
  rw [← show ((([(3, 2), (17, 1), (19, 1), (163, 1), (1759, 1), (204859, 1), (810117218002061, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307281 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_3, prime_oneHundredSeventeenDK_17, prime_oneHundredSeventeenDK_19, prime_oneHundredSeventeenDK_163, prime_oneHundredSeventeenDK_1759, prime_oneHundredSeventeenDK_204859, prime_oneHundredSeventeenDK_810117218002061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307282 : Nat.totient 138325225440030224018829307282 = 68690907770630229751369729600 := by
  rw [← show ((([(2, 1), (167, 1), (1667, 1), (4211, 1), (113275949, 1), (520830452771, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307282 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_167, prime_oneHundredSeventeenDK_1667, prime_oneHundredSeventeenDK_4211, prime_oneHundredSeventeenDK_113275949, prime_oneHundredSeventeenDK_520830452771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307283 : Nat.totient 138325225440030224018829307283 = 136050053409415769706757248000 := by
  rw [← show ((([(61, 1), (18311, 1), (1182953, 1), (104686817909989841, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307283 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_61, prime_oneHundredSeventeenDK_18311, prime_oneHundredSeventeenDK_1182953, prime_oneHundredSeventeenDK_104686817909989841]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307284 : Nat.totient 138325225440030224018829307284 = 46012148754432187268673686400 := by
  rw [← show ((([(2, 2), (3, 1), (479, 1), (308181357101, 1), (78086914741933, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307284 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_3, prime_oneHundredSeventeenDK_479, prime_oneHundredSeventeenDK_308181357101, prime_oneHundredSeventeenDK_78086914741933]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307285 : Nat.totient 138325225440030224018829307285 = 110627030768894789099502182400 := by
  rw [← show ((([(5, 1), (3457, 1), (97301, 1), (51484163, 1), (1597500646127, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307285 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_5, prime_oneHundredSeventeenDK_3457, prime_oneHundredSeventeenDK_97301, prime_oneHundredSeventeenDK_51484163, prime_oneHundredSeventeenDK_1597500646127]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307286 : Nat.totient 138325225440030224018829307286 = 50733798749454277335174912000 := by
  rw [← show ((([(2, 1), (7, 1), (11, 1), (23, 1), (73, 1), (463, 1), (5792061817, 1), (199487547151, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307286 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_7, prime_oneHundredSeventeenDK_11, prime_oneHundredSeventeenDK_23, prime_oneHundredSeventeenDK_73, prime_oneHundredSeventeenDK_463, prime_oneHundredSeventeenDK_5792061817, prime_oneHundredSeventeenDK_199487547151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307287 : Nat.totient 138325225440030224018829307287 = 92216816960020149345886204856 := by
  rw [← show ((([(3, 1), (46108408480010074672943102429, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307287 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_3, prime_oneHundredSeventeenDK_46108408480010074672943102429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307288 : Nat.totient 138325225440030224018829307288 = 68187658821620693408896383520 := by
  rw [← show ((([(2, 3), (71, 1), (81899, 1), (2973544566831419806559, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307288 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_71, prime_oneHundredSeventeenDK_81899, prime_oneHundredSeventeenDK_2973544566831419806559]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307289 : Nat.totient 138325225440030224018829307289 = 137811005269160706503282176336 := by
  rw [← show ((([(269, 1), (70764736103, 1), (7266616075181627, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307289 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_269, prime_oneHundredSeventeenDK_70764736103, prime_oneHundredSeventeenDK_7266616075181627]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307290 : Nat.totient 138325225440030224018829307290 = 36617480603102891419096416768 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (137, 1), (11218590871048679969085913, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307290 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_3, prime_oneHundredSeventeenDK_5, prime_oneHundredSeventeenDK_137, prime_oneHundredSeventeenDK_11218590871048679969085913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307291 : Nat.totient 138325225440030224018829307291 = 127664629773871372096551786912 := by
  rw [← show ((([(13, 1), (6323, 1), (1682809102787506222932509, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307291 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_13, prime_oneHundredSeventeenDK_6323, prime_oneHundredSeventeenDK_1682809102787506222932509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307292 : Nat.totient 138325225440030224018829307292 = 69162608823652729235553609456 := by
  rw [← show ((([(2, 2), (20699779, 1), (124587563, 1), (13409142180199, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307292 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_20699779, prime_oneHundredSeventeenDK_124587563, prime_oneHundredSeventeenDK_13409142180199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307293 : Nat.totient 138325225440030224018829307293 = 78876424860327052550555979456 := by
  rw [← show ((([(3, 1), (7, 1), (659, 1), (1693, 1), (5903909875390047909359, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307293 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_3, prime_oneHundredSeventeenDK_7, prime_oneHundredSeventeenDK_659, prime_oneHundredSeventeenDK_1693, prime_oneHundredSeventeenDK_5903909875390047909359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307294 : Nat.totient 138325225440030224018829307294 = 69162585985409167759894377120 := by
  rw [← show ((([(2, 1), (2587007, 1), (26734605944249517689521, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307294 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_2587007, prime_oneHundredSeventeenDK_26734605944249517689521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307295 : Nat.totient 138325225440030224018829307295 = 107090497114862108917803334560 := by
  rw [← show ((([(5, 1), (31, 1), (892420809290517574315027789, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307295 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_5, prime_oneHundredSeventeenDK_31, prime_oneHundredSeventeenDK_892420809290517574315027789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307296 : Nat.totient 138325225440030224018829307296 = 43879037267856002830357708800 := by
  rw [← show ((([(2, 5), (3, 1), (41, 1), (79, 1), (83, 1), (177433, 1), (30206938939875931, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307296 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_3, prime_oneHundredSeventeenDK_41, prime_oneHundredSeventeenDK_79, prime_oneHundredSeventeenDK_83, prime_oneHundredSeventeenDK_177433, prime_oneHundredSeventeenDK_30206938939875931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307297 : Nat.totient 138325225440030224018829307297 = 125750204945140923047921840160 := by
  rw [← show ((([(11, 1), (368666113003, 1), (34109510071640009, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307297 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_11, prime_oneHundredSeventeenDK_368666113003, prime_oneHundredSeventeenDK_34109510071640009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307298 : Nat.totient 138325225440030224018829307298 = 65092723558481619746864715840 := by
  rw [← show ((([(2, 1), (17, 1), (43391, 1), (93761125199472257067967, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307298 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_17, prime_oneHundredSeventeenDK_43391, prime_oneHundredSeventeenDK_93761125199472257067967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307299 : Nat.totient 138325225440030224018829307299 = 92216816960020149345886204848 := by
  rw [← show ((([(3, 3), (5123156497778897185882566937, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307299 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_3, prime_oneHundredSeventeenDK_5123156497778897185882566937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307300 : Nat.totient 138325225440030224018829307300 = 44590152375476099751131136000 := by
  rw [← show ((([(2, 2), (5, 2), (7, 1), (19, 1), (197, 1), (401, 1), (131655542491839391273, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307300 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_2, prime_oneHundredSeventeenDK_5, prime_oneHundredSeventeenDK_7, prime_oneHundredSeventeenDK_19, prime_oneHundredSeventeenDK_197, prime_oneHundredSeventeenDK_401, prime_oneHundredSeventeenDK_131655542491839391273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSeventeenDK_138325225440030224018829307301 : Nat.totient 138325225440030224018829307301 = 138325225440030224018829307300 := by
  rw [← show ((([(138325225440030224018829307301, 1)] : List FactorBlock).map factorBlockValue).prod) = 138325225440030224018829307301 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSeventeenDK_138325225440030224018829307301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredSeventeenDK : certifiedKill 1 138325225440030224018829307199 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredSeventeenDK_138325225440030224018829307200, phi_oneHundredSeventeenDK_138325225440030224018829307201, phi_oneHundredSeventeenDK_138325225440030224018829307202,
    phi_oneHundredSeventeenDK_138325225440030224018829307203, phi_oneHundredSeventeenDK_138325225440030224018829307204, phi_oneHundredSeventeenDK_138325225440030224018829307205,
    phi_oneHundredSeventeenDK_138325225440030224018829307206, phi_oneHundredSeventeenDK_138325225440030224018829307207, phi_oneHundredSeventeenDK_138325225440030224018829307208,
    phi_oneHundredSeventeenDK_138325225440030224018829307209, phi_oneHundredSeventeenDK_138325225440030224018829307210, phi_oneHundredSeventeenDK_138325225440030224018829307211,
    phi_oneHundredSeventeenDK_138325225440030224018829307212, phi_oneHundredSeventeenDK_138325225440030224018829307213, phi_oneHundredSeventeenDK_138325225440030224018829307214,
    phi_oneHundredSeventeenDK_138325225440030224018829307215, phi_oneHundredSeventeenDK_138325225440030224018829307216, phi_oneHundredSeventeenDK_138325225440030224018829307217,
    phi_oneHundredSeventeenDK_138325225440030224018829307218, phi_oneHundredSeventeenDK_138325225440030224018829307219, phi_oneHundredSeventeenDK_138325225440030224018829307220,
    phi_oneHundredSeventeenDK_138325225440030224018829307221, phi_oneHundredSeventeenDK_138325225440030224018829307222, phi_oneHundredSeventeenDK_138325225440030224018829307223,
    phi_oneHundredSeventeenDK_138325225440030224018829307224, phi_oneHundredSeventeenDK_138325225440030224018829307225, phi_oneHundredSeventeenDK_138325225440030224018829307226,
    phi_oneHundredSeventeenDK_138325225440030224018829307227, phi_oneHundredSeventeenDK_138325225440030224018829307228, phi_oneHundredSeventeenDK_138325225440030224018829307229,
    phi_oneHundredSeventeenDK_138325225440030224018829307230, phi_oneHundredSeventeenDK_138325225440030224018829307231, phi_oneHundredSeventeenDK_138325225440030224018829307232,
    phi_oneHundredSeventeenDK_138325225440030224018829307233, phi_oneHundredSeventeenDK_138325225440030224018829307234, phi_oneHundredSeventeenDK_138325225440030224018829307235,
    phi_oneHundredSeventeenDK_138325225440030224018829307236, phi_oneHundredSeventeenDK_138325225440030224018829307237, phi_oneHundredSeventeenDK_138325225440030224018829307238,
    phi_oneHundredSeventeenDK_138325225440030224018829307239, phi_oneHundredSeventeenDK_138325225440030224018829307240, phi_oneHundredSeventeenDK_138325225440030224018829307241,
    phi_oneHundredSeventeenDK_138325225440030224018829307242, phi_oneHundredSeventeenDK_138325225440030224018829307243, phi_oneHundredSeventeenDK_138325225440030224018829307244,
    phi_oneHundredSeventeenDK_138325225440030224018829307245, phi_oneHundredSeventeenDK_138325225440030224018829307246, phi_oneHundredSeventeenDK_138325225440030224018829307247,
    phi_oneHundredSeventeenDK_138325225440030224018829307248, phi_oneHundredSeventeenDK_138325225440030224018829307249, phi_oneHundredSeventeenDK_138325225440030224018829307250,
    phi_oneHundredSeventeenDK_138325225440030224018829307251, phi_oneHundredSeventeenDK_138325225440030224018829307252, phi_oneHundredSeventeenDK_138325225440030224018829307253,
    phi_oneHundredSeventeenDK_138325225440030224018829307254, phi_oneHundredSeventeenDK_138325225440030224018829307255, phi_oneHundredSeventeenDK_138325225440030224018829307256,
    phi_oneHundredSeventeenDK_138325225440030224018829307257, phi_oneHundredSeventeenDK_138325225440030224018829307258, phi_oneHundredSeventeenDK_138325225440030224018829307259,
    phi_oneHundredSeventeenDK_138325225440030224018829307260, phi_oneHundredSeventeenDK_138325225440030224018829307261, phi_oneHundredSeventeenDK_138325225440030224018829307262,
    phi_oneHundredSeventeenDK_138325225440030224018829307263, phi_oneHundredSeventeenDK_138325225440030224018829307264, phi_oneHundredSeventeenDK_138325225440030224018829307265,
    phi_oneHundredSeventeenDK_138325225440030224018829307266, phi_oneHundredSeventeenDK_138325225440030224018829307267, phi_oneHundredSeventeenDK_138325225440030224018829307268,
    phi_oneHundredSeventeenDK_138325225440030224018829307269, phi_oneHundredSeventeenDK_138325225440030224018829307270, phi_oneHundredSeventeenDK_138325225440030224018829307271,
    phi_oneHundredSeventeenDK_138325225440030224018829307272, phi_oneHundredSeventeenDK_138325225440030224018829307273, phi_oneHundredSeventeenDK_138325225440030224018829307274,
    phi_oneHundredSeventeenDK_138325225440030224018829307275, phi_oneHundredSeventeenDK_138325225440030224018829307276, phi_oneHundredSeventeenDK_138325225440030224018829307277,
    phi_oneHundredSeventeenDK_138325225440030224018829307278, phi_oneHundredSeventeenDK_138325225440030224018829307279, phi_oneHundredSeventeenDK_138325225440030224018829307280,
    phi_oneHundredSeventeenDK_138325225440030224018829307281, phi_oneHundredSeventeenDK_138325225440030224018829307282, phi_oneHundredSeventeenDK_138325225440030224018829307283,
    phi_oneHundredSeventeenDK_138325225440030224018829307284, phi_oneHundredSeventeenDK_138325225440030224018829307285, phi_oneHundredSeventeenDK_138325225440030224018829307286,
    phi_oneHundredSeventeenDK_138325225440030224018829307287, phi_oneHundredSeventeenDK_138325225440030224018829307288, phi_oneHundredSeventeenDK_138325225440030224018829307289,
    phi_oneHundredSeventeenDK_138325225440030224018829307290, phi_oneHundredSeventeenDK_138325225440030224018829307291, phi_oneHundredSeventeenDK_138325225440030224018829307292,
    phi_oneHundredSeventeenDK_138325225440030224018829307293, phi_oneHundredSeventeenDK_138325225440030224018829307294, phi_oneHundredSeventeenDK_138325225440030224018829307295,
    phi_oneHundredSeventeenDK_138325225440030224018829307296, phi_oneHundredSeventeenDK_138325225440030224018829307297, phi_oneHundredSeventeenDK_138325225440030224018829307298,
    phi_oneHundredSeventeenDK_138325225440030224018829307299, phi_oneHundredSeventeenDK_138325225440030224018829307300, phi_oneHundredSeventeenDK_138325225440030224018829307301
    ]

end TotientTailPeriodKiller
end Erdos249257
