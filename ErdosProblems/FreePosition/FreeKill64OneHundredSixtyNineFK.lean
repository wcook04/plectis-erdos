import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredSixtyNineFKFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredSixtyNineFKFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredSixtyNineFKFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredSixtyNineFKFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredSixtyNineFKFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredSixtyNineFKFastPow a n * oneHundredSixtyNineFKFastPow a n * a else oneHundredSixtyNineFKFastPow a n * oneHundredSixtyNineFKFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredSixtyNineFK_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredSixtyNineFK_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredSixtyNineFK_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredSixtyNineFK_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredSixtyNineFK_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredSixtyNineFK_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredSixtyNineFK_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredSixtyNineFK_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredSixtyNineFK_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredSixtyNineFK_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredSixtyNineFK_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredSixtyNineFK_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredSixtyNineFK_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredSixtyNineFK_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredSixtyNineFK_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredSixtyNineFK_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredSixtyNineFK_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredSixtyNineFK_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredSixtyNineFK_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredSixtyNineFK_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredSixtyNineFK_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredSixtyNineFK_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredSixtyNineFK_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredSixtyNineFK_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredSixtyNineFK_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredSixtyNineFK_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredSixtyNineFK_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredSixtyNineFK_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredSixtyNineFK_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredSixtyNineFK_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredSixtyNineFK_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredSixtyNineFK_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredSixtyNineFK_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredSixtyNineFK_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredSixtyNineFK_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredSixtyNineFK_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredSixtyNineFK_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredSixtyNineFK_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredSixtyNineFK_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredSixtyNineFK_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredSixtyNineFK_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredSixtyNineFK_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredSixtyNineFK_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredSixtyNineFK_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredSixtyNineFK_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredSixtyNineFK_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredSixtyNineFK_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredSixtyNineFK_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredSixtyNineFK_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredSixtyNineFK_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredSixtyNineFK_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredSixtyNineFK_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredSixtyNineFK_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredSixtyNineFK_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredSixtyNineFK_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredSixtyNineFK_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredSixtyNineFK_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredSixtyNineFK_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredSixtyNineFK_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredSixtyNineFK_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredSixtyNineFK_331 : Nat.Prime 331 := by norm_num

private theorem prime_oneHundredSixtyNineFK_337 : Nat.Prime 337 := by norm_num

private theorem prime_oneHundredSixtyNineFK_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredSixtyNineFK_359 : Nat.Prime 359 := by norm_num

private theorem prime_oneHundredSixtyNineFK_367 : Nat.Prime 367 := by norm_num

private theorem prime_oneHundredSixtyNineFK_383 : Nat.Prime 383 := by norm_num

private theorem prime_oneHundredSixtyNineFK_409 : Nat.Prime 409 := by norm_num

private theorem prime_oneHundredSixtyNineFK_421 : Nat.Prime 421 := by norm_num

private theorem prime_oneHundredSixtyNineFK_439 : Nat.Prime 439 := by norm_num

private theorem prime_oneHundredSixtyNineFK_443 : Nat.Prime 443 := by norm_num

private theorem prime_oneHundredSixtyNineFK_449 : Nat.Prime 449 := by norm_num

private theorem prime_oneHundredSixtyNineFK_463 : Nat.Prime 463 := by norm_num

private theorem prime_oneHundredSixtyNineFK_467 : Nat.Prime 467 := by norm_num

private theorem prime_oneHundredSixtyNineFK_499 : Nat.Prime 499 := by norm_num

private theorem prime_oneHundredSixtyNineFK_503 : Nat.Prime 503 := by norm_num

private theorem prime_oneHundredSixtyNineFK_521 : Nat.Prime 521 := by norm_num

private theorem prime_oneHundredSixtyNineFK_523 : Nat.Prime 523 := by norm_num

private theorem prime_oneHundredSixtyNineFK_577 : Nat.Prime 577 := by norm_num

private theorem prime_oneHundredSixtyNineFK_587 : Nat.Prime 587 := by norm_num

private theorem prime_oneHundredSixtyNineFK_593 : Nat.Prime 593 := by norm_num

private theorem prime_oneHundredSixtyNineFK_607 : Nat.Prime 607 := by norm_num

private theorem prime_oneHundredSixtyNineFK_619 : Nat.Prime 619 := by norm_num

private theorem prime_oneHundredSixtyNineFK_647 : Nat.Prime 647 := by norm_num

private theorem prime_oneHundredSixtyNineFK_653 : Nat.Prime 653 := by norm_num

private theorem prime_oneHundredSixtyNineFK_661 : Nat.Prime 661 := by norm_num

private theorem prime_oneHundredSixtyNineFK_673 : Nat.Prime 673 := by norm_num

private theorem prime_oneHundredSixtyNineFK_677 : Nat.Prime 677 := by norm_num

private theorem prime_oneHundredSixtyNineFK_691 : Nat.Prime 691 := by norm_num

private theorem prime_oneHundredSixtyNineFK_701 : Nat.Prime 701 := by norm_num

private theorem prime_oneHundredSixtyNineFK_719 : Nat.Prime 719 := by norm_num

private theorem prime_oneHundredSixtyNineFK_727 : Nat.Prime 727 := by norm_num

private theorem prime_oneHundredSixtyNineFK_743 : Nat.Prime 743 := by norm_num

private theorem prime_oneHundredSixtyNineFK_757 : Nat.Prime 757 := by norm_num

private theorem prime_oneHundredSixtyNineFK_761 : Nat.Prime 761 := by norm_num

private theorem prime_oneHundredSixtyNineFK_787 : Nat.Prime 787 := by norm_num

private theorem prime_oneHundredSixtyNineFK_809 : Nat.Prime 809 := by norm_num

private theorem prime_oneHundredSixtyNineFK_811 : Nat.Prime 811 := by norm_num

private theorem prime_oneHundredSixtyNineFK_823 : Nat.Prime 823 := by norm_num

private theorem prime_oneHundredSixtyNineFK_941 : Nat.Prime 941 := by norm_num

private theorem prime_oneHundredSixtyNineFK_967 : Nat.Prime 967 := by norm_num

private theorem prime_oneHundredSixtyNineFK_971 : Nat.Prime 971 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1039 : Nat.Prime 1039 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1049 : Nat.Prime 1049 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1093 : Nat.Prime 1093 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1109 : Nat.Prime 1109 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1171 : Nat.Prime 1171 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1193 : Nat.Prime 1193 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1217 : Nat.Prime 1217 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1231 : Nat.Prime 1231 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1237 : Nat.Prime 1237 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1301 : Nat.Prime 1301 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1319 : Nat.Prime 1319 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1459 : Nat.Prime 1459 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1487 : Nat.Prime 1487 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1609 : Nat.Prime 1609 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1619 : Nat.Prime 1619 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1697 : Nat.Prime 1697 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1721 : Nat.Prime 1721 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1753 : Nat.Prime 1753 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1759 : Nat.Prime 1759 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1831 : Nat.Prime 1831 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1951 : Nat.Prime 1951 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1987 : Nat.Prime 1987 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1993 : Nat.Prime 1993 := by norm_num

private theorem prime_oneHundredSixtyNineFK_2011 : Nat.Prime 2011 := by norm_num

private theorem prime_oneHundredSixtyNineFK_2039 : Nat.Prime 2039 := by norm_num

private theorem prime_oneHundredSixtyNineFK_2069 : Nat.Prime 2069 := by norm_num

private theorem prime_oneHundredSixtyNineFK_2129 : Nat.Prime 2129 := by norm_num

private theorem prime_oneHundredSixtyNineFK_2131 : Nat.Prime 2131 := by norm_num

private theorem prime_oneHundredSixtyNineFK_2161 : Nat.Prime 2161 := by norm_num

private theorem prime_oneHundredSixtyNineFK_2243 : Nat.Prime 2243 := by norm_num

private theorem prime_oneHundredSixtyNineFK_2251 : Nat.Prime 2251 := by norm_num

private theorem prime_oneHundredSixtyNineFK_2267 : Nat.Prime 2267 := by norm_num

private theorem prime_oneHundredSixtyNineFK_2347 : Nat.Prime 2347 := by norm_num

private theorem prime_oneHundredSixtyNineFK_2467 : Nat.Prime 2467 := by norm_num

private theorem prime_oneHundredSixtyNineFK_2659 : Nat.Prime 2659 := by norm_num

private theorem prime_oneHundredSixtyNineFK_2663 : Nat.Prime 2663 := by norm_num

private theorem prime_oneHundredSixtyNineFK_2693 : Nat.Prime 2693 := by norm_num

private theorem prime_oneHundredSixtyNineFK_2713 : Nat.Prime 2713 := by norm_num

private theorem prime_oneHundredSixtyNineFK_2777 : Nat.Prime 2777 := by norm_num

private theorem prime_oneHundredSixtyNineFK_2803 : Nat.Prime 2803 := by norm_num

private theorem prime_oneHundredSixtyNineFK_2953 : Nat.Prime 2953 := by norm_num

private theorem prime_oneHundredSixtyNineFK_3011 : Nat.Prime 3011 := by norm_num

private theorem prime_oneHundredSixtyNineFK_3203 : Nat.Prime 3203 := by norm_num

private theorem prime_oneHundredSixtyNineFK_3361 : Nat.Prime 3361 := by norm_num

private theorem prime_oneHundredSixtyNineFK_3391 : Nat.Prime 3391 := by norm_num

private theorem prime_oneHundredSixtyNineFK_3469 : Nat.Prime 3469 := by norm_num

private theorem prime_oneHundredSixtyNineFK_3517 : Nat.Prime 3517 := by norm_num

private theorem prime_oneHundredSixtyNineFK_3727 : Nat.Prime 3727 := by norm_num

private theorem prime_oneHundredSixtyNineFK_3779 : Nat.Prime 3779 := by norm_num

private theorem prime_oneHundredSixtyNineFK_3881 : Nat.Prime 3881 := by norm_num

private theorem prime_oneHundredSixtyNineFK_3889 : Nat.Prime 3889 := by norm_num

private theorem prime_oneHundredSixtyNineFK_3989 : Nat.Prime 3989 := by norm_num

private theorem prime_oneHundredSixtyNineFK_4003 : Nat.Prime 4003 := by norm_num

private theorem prime_oneHundredSixtyNineFK_4253 : Nat.Prime 4253 := by norm_num

private theorem prime_oneHundredSixtyNineFK_4259 : Nat.Prime 4259 := by norm_num

private theorem prime_oneHundredSixtyNineFK_4357 : Nat.Prime 4357 := by norm_num

private theorem prime_oneHundredSixtyNineFK_4441 : Nat.Prime 4441 := by norm_num

private theorem prime_oneHundredSixtyNineFK_4451 : Nat.Prime 4451 := by norm_num

private theorem prime_oneHundredSixtyNineFK_4799 : Nat.Prime 4799 := by norm_num

private theorem prime_oneHundredSixtyNineFK_4919 : Nat.Prime 4919 := by norm_num

private theorem prime_oneHundredSixtyNineFK_4943 : Nat.Prime 4943 := by norm_num

private theorem prime_oneHundredSixtyNineFK_4973 : Nat.Prime 4973 := by norm_num

private theorem prime_oneHundredSixtyNineFK_5009 : Nat.Prime 5009 := by norm_num

private theorem prime_oneHundredSixtyNineFK_5101 : Nat.Prime 5101 := by norm_num

private theorem prime_oneHundredSixtyNineFK_5147 : Nat.Prime 5147 := by norm_num

private theorem prime_oneHundredSixtyNineFK_5209 : Nat.Prime 5209 := by norm_num

private theorem prime_oneHundredSixtyNineFK_5333 : Nat.Prime 5333 := by norm_num

private theorem prime_oneHundredSixtyNineFK_5387 : Nat.Prime 5387 := by norm_num

private theorem prime_oneHundredSixtyNineFK_5441 : Nat.Prime 5441 := by norm_num

private theorem prime_oneHundredSixtyNineFK_5477 : Nat.Prime 5477 := by norm_num

private theorem prime_oneHundredSixtyNineFK_5623 : Nat.Prime 5623 := by norm_num

private theorem prime_oneHundredSixtyNineFK_5647 : Nat.Prime 5647 := by norm_num

private theorem prime_oneHundredSixtyNineFK_5737 : Nat.Prime 5737 := by norm_num

private theorem prime_oneHundredSixtyNineFK_5791 : Nat.Prime 5791 := by norm_num

private theorem prime_oneHundredSixtyNineFK_5807 : Nat.Prime 5807 := by norm_num

private theorem prime_oneHundredSixtyNineFK_6067 : Nat.Prime 6067 := by norm_num

private theorem prime_oneHundredSixtyNineFK_6091 : Nat.Prime 6091 := by norm_num

private theorem prime_oneHundredSixtyNineFK_6247 : Nat.Prime 6247 := by norm_num

private theorem prime_oneHundredSixtyNineFK_6257 : Nat.Prime 6257 := by norm_num

private theorem prime_oneHundredSixtyNineFK_6397 : Nat.Prime 6397 := by norm_num

private theorem prime_oneHundredSixtyNineFK_6551 : Nat.Prime 6551 := by norm_num

private theorem prime_oneHundredSixtyNineFK_6569 : Nat.Prime 6569 := by norm_num

private theorem prime_oneHundredSixtyNineFK_6803 : Nat.Prime 6803 := by norm_num

private theorem prime_oneHundredSixtyNineFK_6899 : Nat.Prime 6899 := by norm_num

private theorem prime_oneHundredSixtyNineFK_7561 : Nat.Prime 7561 := by norm_num

private theorem prime_oneHundredSixtyNineFK_7669 : Nat.Prime 7669 := by norm_num

private theorem prime_oneHundredSixtyNineFK_8443 : Nat.Prime 8443 := by norm_num

private theorem prime_oneHundredSixtyNineFK_8647 : Nat.Prime 8647 := by norm_num

private theorem prime_oneHundredSixtyNineFK_8707 : Nat.Prime 8707 := by norm_num

private theorem prime_oneHundredSixtyNineFK_8831 : Nat.Prime 8831 := by norm_num

private theorem prime_oneHundredSixtyNineFK_9227 : Nat.Prime 9227 := by norm_num

private theorem prime_oneHundredSixtyNineFK_9467 : Nat.Prime 9467 := by norm_num

private theorem prime_oneHundredSixtyNineFK_9719 : Nat.Prime 9719 := by norm_num

private theorem prime_oneHundredSixtyNineFK_9829 : Nat.Prime 9829 := by norm_num

private theorem prime_oneHundredSixtyNineFK_10069 : Nat.Prime 10069 := by norm_num

private theorem prime_oneHundredSixtyNineFK_11119 : Nat.Prime 11119 := by norm_num

private theorem prime_oneHundredSixtyNineFK_11213 : Nat.Prime 11213 := by norm_num

private theorem prime_oneHundredSixtyNineFK_11311 : Nat.Prime 11311 := by norm_num

private theorem prime_oneHundredSixtyNineFK_11807 : Nat.Prime 11807 := by norm_num

private theorem prime_oneHundredSixtyNineFK_11813 : Nat.Prime 11813 := by norm_num

private theorem prime_oneHundredSixtyNineFK_11863 : Nat.Prime 11863 := by norm_num

private theorem prime_oneHundredSixtyNineFK_12197 : Nat.Prime 12197 := by norm_num

private theorem prime_oneHundredSixtyNineFK_12203 : Nat.Prime 12203 := by norm_num

private theorem prime_oneHundredSixtyNineFK_12251 : Nat.Prime 12251 := by norm_num

private theorem prime_oneHundredSixtyNineFK_12659 : Nat.Prime 12659 := by norm_num

private theorem prime_oneHundredSixtyNineFK_12757 : Nat.Prime 12757 := by norm_num

private theorem prime_oneHundredSixtyNineFK_12781 : Nat.Prime 12781 := by norm_num

private theorem prime_oneHundredSixtyNineFK_13441 : Nat.Prime 13441 := by norm_num

private theorem prime_oneHundredSixtyNineFK_13709 : Nat.Prime 13709 := by norm_num

private theorem prime_oneHundredSixtyNineFK_14051 : Nat.Prime 14051 := by norm_num

private theorem prime_oneHundredSixtyNineFK_14341 : Nat.Prime 14341 := by norm_num

private theorem prime_oneHundredSixtyNineFK_14783 : Nat.Prime 14783 := by norm_num

private theorem prime_oneHundredSixtyNineFK_15401 : Nat.Prime 15401 := by norm_num

private theorem prime_oneHundredSixtyNineFK_15583 : Nat.Prime 15583 := by norm_num

private theorem prime_oneHundredSixtyNineFK_15679 : Nat.Prime 15679 := by norm_num

private theorem prime_oneHundredSixtyNineFK_16061 : Nat.Prime 16061 := by norm_num

private theorem prime_oneHundredSixtyNineFK_16831 : Nat.Prime 16831 := by norm_num

private theorem prime_oneHundredSixtyNineFK_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredSixtyNineFK_17321 : Nat.Prime 17321 := by norm_num

private theorem prime_oneHundredSixtyNineFK_18367 : Nat.Prime 18367 := by norm_num

private theorem prime_oneHundredSixtyNineFK_18539 : Nat.Prime 18539 := by norm_num

private theorem prime_oneHundredSixtyNineFK_19013 : Nat.Prime 19013 := by norm_num

private theorem prime_oneHundredSixtyNineFK_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredSixtyNineFK_21757 : Nat.Prime 21757 := by norm_num

private theorem prime_oneHundredSixtyNineFK_21859 : Nat.Prime 21859 := by norm_num

private theorem prime_oneHundredSixtyNineFK_22259 : Nat.Prime 22259 := by norm_num

private theorem prime_oneHundredSixtyNineFK_23293 : Nat.Prime 23293 := by norm_num

private theorem prime_oneHundredSixtyNineFK_23531 : Nat.Prime 23531 := by norm_num

private theorem prime_oneHundredSixtyNineFK_24007 : Nat.Prime 24007 := by norm_num

private theorem prime_oneHundredSixtyNineFK_24247 : Nat.Prime 24247 := by norm_num

private theorem prime_oneHundredSixtyNineFK_24659 : Nat.Prime 24659 := by norm_num

private theorem prime_oneHundredSixtyNineFK_25693 : Nat.Prime 25693 := by norm_num

private theorem prime_oneHundredSixtyNineFK_26371 : Nat.Prime 26371 := by norm_num

private theorem prime_oneHundredSixtyNineFK_26597 : Nat.Prime 26597 := by norm_num

private theorem prime_oneHundredSixtyNineFK_27779 : Nat.Prime 27779 := by norm_num

private theorem prime_oneHundredSixtyNineFK_28109 : Nat.Prime 28109 := by norm_num

private theorem prime_oneHundredSixtyNineFK_28627 : Nat.Prime 28627 := by norm_num

private theorem prime_oneHundredSixtyNineFK_28729 : Nat.Prime 28729 := by norm_num

private theorem prime_oneHundredSixtyNineFK_28879 : Nat.Prime 28879 := by norm_num

private theorem prime_oneHundredSixtyNineFK_29059 : Nat.Prime 29059 := by norm_num

private theorem prime_oneHundredSixtyNineFK_29423 : Nat.Prime 29423 := by norm_num

private theorem prime_oneHundredSixtyNineFK_30133 : Nat.Prime 30133 := by norm_num

private theorem prime_oneHundredSixtyNineFK_30241 : Nat.Prime 30241 := by norm_num

private theorem prime_oneHundredSixtyNineFK_31081 : Nat.Prime 31081 := by norm_num

private theorem prime_oneHundredSixtyNineFK_31547 : Nat.Prime 31547 := by norm_num

private theorem prime_oneHundredSixtyNineFK_32887 : Nat.Prime 32887 := by norm_num

private theorem prime_oneHundredSixtyNineFK_34841 : Nat.Prime 34841 := by norm_num

private theorem prime_oneHundredSixtyNineFK_36007 : Nat.Prime 36007 := by norm_num

private theorem prime_oneHundredSixtyNineFK_37951 : Nat.Prime 37951 := by norm_num

private theorem prime_oneHundredSixtyNineFK_38561 : Nat.Prime 38561 := by norm_num

private theorem prime_oneHundredSixtyNineFK_41983 : Nat.Prime 41983 := by norm_num

private theorem prime_oneHundredSixtyNineFK_43271 : Nat.Prime 43271 := by norm_num

private theorem prime_oneHundredSixtyNineFK_44633 : Nat.Prime 44633 := by norm_num

private theorem prime_oneHundredSixtyNineFK_46337 : Nat.Prime 46337 := by norm_num

private theorem prime_oneHundredSixtyNineFK_47363 : Nat.Prime 47363 := by norm_num

private theorem prime_oneHundredSixtyNineFK_47969 : Nat.Prime 47969 := by norm_num

private theorem prime_oneHundredSixtyNineFK_48023 : Nat.Prime 48023 := by norm_num

private theorem prime_oneHundredSixtyNineFK_48197 : Nat.Prime 48197 := by norm_num

private theorem prime_oneHundredSixtyNineFK_50741 : Nat.Prime 50741 := by norm_num

private theorem prime_oneHundredSixtyNineFK_50923 : Nat.Prime 50923 := by norm_num

private theorem prime_oneHundredSixtyNineFK_51343 : Nat.Prime 51343 := by norm_num

private theorem prime_oneHundredSixtyNineFK_53089 : Nat.Prime 53089 := by norm_num

private theorem prime_oneHundredSixtyNineFK_53897 : Nat.Prime 53897 := by norm_num

private theorem prime_oneHundredSixtyNineFK_54419 : Nat.Prime 54419 := by norm_num

private theorem prime_oneHundredSixtyNineFK_55631 : Nat.Prime 55631 := by norm_num

private theorem prime_oneHundredSixtyNineFK_56269 : Nat.Prime 56269 := by norm_num

private theorem prime_oneHundredSixtyNineFK_56431 : Nat.Prime 56431 := by norm_num

private theorem prime_oneHundredSixtyNineFK_60139 : Nat.Prime 60139 := by norm_num

private theorem prime_oneHundredSixtyNineFK_60217 : Nat.Prime 60217 := by norm_num

private theorem prime_oneHundredSixtyNineFK_62099 : Nat.Prime 62099 := by norm_num

private theorem prime_oneHundredSixtyNineFK_64879 : Nat.Prime 64879 := by norm_num

private theorem prime_oneHundredSixtyNineFK_66463 : Nat.Prime 66463 := by norm_num

private theorem prime_oneHundredSixtyNineFK_68947 : Nat.Prime 68947 := by norm_num

private theorem prime_oneHundredSixtyNineFK_69877 : Nat.Prime 69877 := by norm_num

private theorem prime_oneHundredSixtyNineFK_71171 : Nat.Prime 71171 := by norm_num

private theorem prime_oneHundredSixtyNineFK_71719 : Nat.Prime 71719 := by norm_num

private theorem prime_oneHundredSixtyNineFK_72047 : Nat.Prime 72047 := by norm_num

private theorem prime_oneHundredSixtyNineFK_72949 : Nat.Prime 72949 := by norm_num

private theorem prime_oneHundredSixtyNineFK_77351 : Nat.Prime 77351 := by norm_num

private theorem prime_oneHundredSixtyNineFK_81359 : Nat.Prime 81359 := by norm_num

private theorem prime_oneHundredSixtyNineFK_82471 : Nat.Prime 82471 := by norm_num

private theorem prime_oneHundredSixtyNineFK_84127 : Nat.Prime 84127 := by norm_num

private theorem prime_oneHundredSixtyNineFK_84221 : Nat.Prime 84221 := by norm_num

private theorem prime_oneHundredSixtyNineFK_86729 : Nat.Prime 86729 := by norm_num

private theorem prime_oneHundredSixtyNineFK_88589 : Nat.Prime 88589 := by norm_num

private theorem prime_oneHundredSixtyNineFK_95737 : Nat.Prime 95737 := by norm_num

private theorem prime_oneHundredSixtyNineFK_99149 : Nat.Prime 99149 := by norm_num

private theorem prime_oneHundredSixtyNineFK_103787 : Nat.Prime 103787 := by norm_num

private theorem prime_oneHundredSixtyNineFK_106441 : Nat.Prime 106441 := by norm_num

private theorem prime_oneHundredSixtyNineFK_106541 : Nat.Prime 106541 := by norm_num

private theorem prime_oneHundredSixtyNineFK_107837 : Nat.Prime 107837 := by norm_num

private theorem prime_oneHundredSixtyNineFK_111127 : Nat.Prime 111127 := by norm_num

private theorem prime_oneHundredSixtyNineFK_112913 : Nat.Prime 112913 := by norm_num

private theorem prime_oneHundredSixtyNineFK_119929 : Nat.Prime 119929 := by norm_num

private theorem prime_oneHundredSixtyNineFK_121931 : Nat.Prime 121931 := by norm_num

private theorem prime_oneHundredSixtyNineFK_155627 : Nat.Prime 155627 := by norm_num

private theorem prime_oneHundredSixtyNineFK_160183 : Nat.Prime 160183 := by norm_num

private theorem prime_oneHundredSixtyNineFK_163193 : Nat.Prime 163193 := by norm_num

private theorem prime_oneHundredSixtyNineFK_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredSixtyNineFK_185897 : Nat.Prime 185897 := by norm_num

private theorem prime_oneHundredSixtyNineFK_220189 : Nat.Prime 220189 := by norm_num

private theorem prime_oneHundredSixtyNineFK_220301 : Nat.Prime 220301 := by norm_num

private theorem prime_oneHundredSixtyNineFK_235117 : Nat.Prime 235117 := by norm_num

private theorem prime_oneHundredSixtyNineFK_238079 : Nat.Prime 238079 := by norm_num

private theorem prime_oneHundredSixtyNineFK_244261 : Nat.Prime 244261 := by norm_num

private theorem prime_oneHundredSixtyNineFK_246539 : Nat.Prime 246539 := by norm_num

private theorem prime_oneHundredSixtyNineFK_267373 : Nat.Prime 267373 := by norm_num

private theorem prime_oneHundredSixtyNineFK_272971 : Nat.Prime 272971 := by norm_num

private theorem prime_oneHundredSixtyNineFK_279883 : Nat.Prime 279883 := by norm_num

private theorem prime_oneHundredSixtyNineFK_321187 : Nat.Prime 321187 := by norm_num

private theorem prime_oneHundredSixtyNineFK_327289 : Nat.Prime 327289 := by norm_num

private theorem prime_oneHundredSixtyNineFK_328271 : Nat.Prime 328271 := by norm_num

private theorem prime_oneHundredSixtyNineFK_333439 : Nat.Prime 333439 := by norm_num

private theorem prime_oneHundredSixtyNineFK_343601 : Nat.Prime 343601 := by norm_num

private theorem prime_oneHundredSixtyNineFK_380447 : Nat.Prime 380447 := by norm_num

private theorem prime_oneHundredSixtyNineFK_389479 : Nat.Prime 389479 := by norm_num

private theorem prime_oneHundredSixtyNineFK_422557 : Nat.Prime 422557 := by norm_num

private theorem prime_oneHundredSixtyNineFK_450943 : Nat.Prime 450943 := by norm_num

private theorem prime_oneHundredSixtyNineFK_467261 : Nat.Prime 467261 := by norm_num

private theorem prime_oneHundredSixtyNineFK_473383 : Nat.Prime 473383 := by norm_num

private theorem prime_oneHundredSixtyNineFK_475327 : Nat.Prime 475327 := by norm_num

private theorem prime_oneHundredSixtyNineFK_495799 : Nat.Prime 495799 := by norm_num

private theorem prime_oneHundredSixtyNineFK_496631 : Nat.Prime 496631 := by norm_num

private theorem prime_oneHundredSixtyNineFK_500741 : Nat.Prime 500741 := by norm_num

private theorem prime_oneHundredSixtyNineFK_517043 : Nat.Prime 517043 := by norm_num

private theorem prime_oneHundredSixtyNineFK_553873 : Nat.Prime 553873 := by norm_num

private theorem prime_oneHundredSixtyNineFK_593179 : Nat.Prime 593179 := by norm_num

private theorem prime_oneHundredSixtyNineFK_634573 : Nat.Prime 634573 := by norm_num

private theorem prime_oneHundredSixtyNineFK_636241 : Nat.Prime 636241 := by norm_num

private theorem prime_oneHundredSixtyNineFK_646339 : Nat.Prime 646339 := by norm_num

private theorem prime_oneHundredSixtyNineFK_678593 : Nat.Prime 678593 := by norm_num

private theorem prime_oneHundredSixtyNineFK_714677 : Nat.Prime 714677 := by norm_num

private theorem prime_oneHundredSixtyNineFK_729749 : Nat.Prime 729749 := by norm_num

private theorem prime_oneHundredSixtyNineFK_750863 : Nat.Prime 750863 := by norm_num

private theorem prime_oneHundredSixtyNineFK_767537 : Nat.Prime 767537 := by norm_num

private theorem prime_oneHundredSixtyNineFK_814937 : Nat.Prime 814937 := by norm_num

private theorem prime_oneHundredSixtyNineFK_842279 : Nat.Prime 842279 := by norm_num

private theorem prime_oneHundredSixtyNineFK_965749 : Nat.Prime 965749 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1037327 : Nat.Prime 1037327 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1053083 : Nat.Prime 1053083 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1118317 : Nat.Prime 1118317 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1142083 : Nat.Prime 1142083 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1153769 : Nat.Prime 1153769 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1191979 : Nat.Prime 1191979 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1280737 : Nat.Prime 1280737 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1281503 : Nat.Prime 1281503 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1344727 : Nat.Prime 1344727 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1426231 : Nat.Prime 1426231 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1570501 : Nat.Prime 1570501 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1623977 : Nat.Prime 1623977 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1662347 : Nat.Prime 1662347 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1944143 : Nat.Prime 1944143 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1952729 : Nat.Prime 1952729 := by norm_num

private theorem prime_oneHundredSixtyNineFK_1991461 : Nat.Prime 1991461 := by norm_num

private theorem prime_oneHundredSixtyNineFK_2039417 : Nat.Prime 2039417 := by norm_num

private theorem prime_oneHundredSixtyNineFK_2131859 : Nat.Prime 2131859 := by norm_num

private theorem prime_oneHundredSixtyNineFK_2161199 : Nat.Prime 2161199 := by norm_num

private theorem prime_oneHundredSixtyNineFK_2192579 : Nat.Prime 2192579 := by norm_num

private theorem prime_oneHundredSixtyNineFK_2197189 : Nat.Prime 2197189 := by norm_num

private theorem prime_oneHundredSixtyNineFK_2224961 : Nat.Prime 2224961 := by norm_num

private theorem prime_oneHundredSixtyNineFK_2335057 : Nat.Prime 2335057 := by norm_num

private theorem prime_oneHundredSixtyNineFK_2381657 : Nat.Prime 2381657 := by norm_num

private theorem prime_oneHundredSixtyNineFK_2398597 : Nat.Prime 2398597 := by norm_num

private theorem prime_oneHundredSixtyNineFK_2477851 : Nat.Prime 2477851 := by norm_num

private theorem prime_oneHundredSixtyNineFK_2489183 : Nat.Prime 2489183 := by norm_num

private theorem prime_oneHundredSixtyNineFK_2539073 : Nat.Prime 2539073 := by norm_num

private theorem prime_oneHundredSixtyNineFK_2579191 : Nat.Prime 2579191 := by norm_num

private theorem prime_oneHundredSixtyNineFK_2596739 : Nat.Prime 2596739 := by norm_num

private theorem prime_oneHundredSixtyNineFK_2727379 : Nat.Prime 2727379 := by norm_num

private theorem prime_oneHundredSixtyNineFK_3059143 : Nat.Prime 3059143 := by norm_num

private theorem prime_oneHundredSixtyNineFK_3091219 : Nat.Prime 3091219 := by norm_num

private theorem prime_oneHundredSixtyNineFK_3289757 : Nat.Prime 3289757 := by norm_num

private theorem prime_oneHundredSixtyNineFK_3384593 : Nat.Prime 3384593 := by norm_num

private theorem prime_oneHundredSixtyNineFK_3399503 : Nat.Prime 3399503 := by norm_num

private theorem prime_oneHundredSixtyNineFK_3578573 : Nat.Prime 3578573 := by norm_num

private theorem prime_oneHundredSixtyNineFK_3690961 : Nat.Prime 3690961 := by norm_num

private theorem prime_oneHundredSixtyNineFK_3757267 : Nat.Prime 3757267 := by norm_num

private theorem prime_oneHundredSixtyNineFK_4235947 : Nat.Prime 4235947 := by norm_num

private theorem prime_oneHundredSixtyNineFK_4458877 : Nat.Prime 4458877 := by norm_num

private theorem prime_oneHundredSixtyNineFK_4723049 : Nat.Prime 4723049 := by norm_num

private theorem prime_oneHundredSixtyNineFK_4872337 : Nat.Prime 4872337 := by norm_num

private theorem prime_oneHundredSixtyNineFK_5202511 : Nat.Prime 5202511 := by norm_num

private theorem prime_oneHundredSixtyNineFK_5221327 : Nat.Prime 5221327 := by norm_num

private theorem prime_oneHundredSixtyNineFK_5425733 : Nat.Prime 5425733 := by norm_num

private theorem prime_oneHundredSixtyNineFK_5448323 : Nat.Prime 5448323 := by norm_num

private theorem prime_oneHundredSixtyNineFK_5468899 : Nat.Prime 5468899 := by norm_num

private theorem prime_oneHundredSixtyNineFK_5984963 : Nat.Prime 5984963 := by norm_num

private theorem prime_oneHundredSixtyNineFK_6125023 : Nat.Prime 6125023 := by norm_num

private theorem prime_oneHundredSixtyNineFK_6267139 : Nat.Prime 6267139 := by norm_num

private theorem prime_oneHundredSixtyNineFK_6294031 : Nat.Prime 6294031 := by norm_num

private theorem prime_oneHundredSixtyNineFK_6395327 : Nat.Prime 6395327 := by norm_num

private theorem prime_oneHundredSixtyNineFK_6510731 : Nat.Prime 6510731 := by norm_num

private theorem prime_oneHundredSixtyNineFK_7023647 : Nat.Prime 7023647 := by norm_num

private theorem prime_oneHundredSixtyNineFK_7631857 : Nat.Prime 7631857 := by norm_num

private theorem prime_oneHundredSixtyNineFK_8302403 : Nat.Prime 8302403 := by norm_num

private theorem prime_oneHundredSixtyNineFK_8415577 : Nat.Prime 8415577 := by norm_num

private theorem prime_oneHundredSixtyNineFK_8461913 : Nat.Prime 8461913 := by norm_num

private theorem prime_oneHundredSixtyNineFK_8589331 : Nat.Prime 8589331 := by norm_num

private theorem prime_oneHundredSixtyNineFK_8755073 : Nat.Prime 8755073 := by norm_num

private theorem prime_oneHundredSixtyNineFK_9080177 : Nat.Prime 9080177 := by norm_num

private theorem prime_oneHundredSixtyNineFK_9890501 : Nat.Prime 9890501 := by norm_num

private theorem prime_oneHundredSixtyNineFK_10012403 : Nat.Prime 10012403 := by norm_num

private theorem prime_oneHundredSixtyNineFK_10320283 : Nat.Prime 10320283 := by norm_num

private theorem prime_oneHundredSixtyNineFK_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredSixtyNineFK_11019809 : Nat.Prime 11019809 := by norm_num

private theorem prime_oneHundredSixtyNineFK_11197493 : Nat.Prime 11197493 := by norm_num

private theorem prime_oneHundredSixtyNineFK_11603143 : Nat.Prime 11603143 := by norm_num

private theorem prime_oneHundredSixtyNineFK_11678341 : Nat.Prime 11678341 := by norm_num

private theorem prime_oneHundredSixtyNineFK_12569723 : Nat.Prime 12569723 := by norm_num

private theorem prime_oneHundredSixtyNineFK_12617369 : Nat.Prime 12617369 := by norm_num

private theorem prime_oneHundredSixtyNineFK_12907421 : Nat.Prime 12907421 := by norm_num

private theorem prime_oneHundredSixtyNineFK_13702301 : Nat.Prime 13702301 := by norm_num

private theorem prime_oneHundredSixtyNineFK_14403967 : Nat.Prime 14403967 := by norm_num

private theorem prime_oneHundredSixtyNineFK_15780377 : Nat.Prime 15780377 := by norm_num

private theorem prime_oneHundredSixtyNineFK_16932521 : Nat.Prime 16932521 := by norm_num

private theorem prime_oneHundredSixtyNineFK_17212693 : Nat.Prime 17212693 := by norm_num

private theorem prime_oneHundredSixtyNineFK_17842091 : Nat.Prime 17842091 := by norm_num

private theorem prime_oneHundredSixtyNineFK_18134537 : Nat.Prime 18134537 := by norm_num

private theorem prime_oneHundredSixtyNineFK_18536447 : Nat.Prime 18536447 := by norm_num

private theorem prime_oneHundredSixtyNineFK_18559133 : Nat.Prime 18559133 := by norm_num

private theorem prime_oneHundredSixtyNineFK_19146287 : Nat.Prime 19146287 := by norm_num

private theorem prime_oneHundredSixtyNineFK_20279179 : Nat.Prime 20279179 := by norm_num

private theorem prime_oneHundredSixtyNineFK_22459337 : Nat.Prime 22459337 := by norm_num

private theorem prime_oneHundredSixtyNineFK_22497403 : Nat.Prime 22497403 := by norm_num

private theorem prime_oneHundredSixtyNineFK_29331353 : Nat.Prime 29331353 := by norm_num

private theorem prime_oneHundredSixtyNineFK_30913481 : Nat.Prime 30913481 := by
  apply lucas_primality 30913481 (3 : ZMod 30913481)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 2), (17, 1), (269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 2), (17, 1), (269, 1)] : List FactorBlock).map factorBlockValue).prod) = 30913481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_13
      · exact prime_oneHundredSixtyNineFK_17
      · exact prime_oneHundredSixtyNineFK_269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 30913481) ^ 15456740 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 30913481) ^ 6182696 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 30913481) ^ 2377960 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 30913481) ^ 1818440 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 30913481) ^ 114920 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_33662309 : Nat.Prime 33662309 := by
  apply lucas_primality 33662309 (2 : ZMod 33662309)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (8415577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (8415577, 1)] : List FactorBlock).map factorBlockValue).prod) = 33662309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_8415577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 33662309) ^ 16831154 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 33662309) ^ 4 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_34022383 : Nat.Prime 34022383 := by
  apply lucas_primality 34022383 (5 : ZMod 34022383)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (246539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (246539, 1)] : List FactorBlock).map factorBlockValue).prod) = 34022383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_23
      · exact prime_oneHundredSixtyNineFK_246539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 34022383) ^ 17011191 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 34022383) ^ 11340794 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 34022383) ^ 1479234 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 34022383) ^ 138 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_36512669 : Nat.Prime 36512669 := by
  apply lucas_primality 36512669 (2 : ZMod 36512669)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (31, 1), (17321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (31, 1), (17321, 1)] : List FactorBlock).map factorBlockValue).prod) = 36512669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_17
      · exact prime_oneHundredSixtyNineFK_31
      · exact prime_oneHundredSixtyNineFK_17321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 36512669) ^ 18256334 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 36512669) ^ 2147804 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 36512669) ^ 1177828 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 36512669) ^ 2108 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_37288723 : Nat.Prime 37288723 := by
  apply lucas_primality 37288723 (3 : ZMod 37288723)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (31, 2), (223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (31, 2), (223, 1)] : List FactorBlock).map factorBlockValue).prod) = 37288723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_29
      · exact prime_oneHundredSixtyNineFK_31
      · exact prime_oneHundredSixtyNineFK_223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 37288723) ^ 18644361 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 37288723) ^ 12429574 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 37288723) ^ 1285818 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 37288723) ^ 1202862 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 37288723) ^ 167214 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_38083603 : Nat.Prime 38083603 := by
  apply lucas_primality 38083603 (2 : ZMod 38083603)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (463, 1), (13709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (463, 1), (13709, 1)] : List FactorBlock).map factorBlockValue).prod) = 38083603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_463
      · exact prime_oneHundredSixtyNineFK_13709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 38083603) ^ 19041801 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 38083603) ^ 12694534 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 38083603) ^ 82254 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 38083603) ^ 2778 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_38926313 : Nat.Prime 38926313 := by
  apply lucas_primality 38926313 (3 : ZMod 38926313)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (59, 1), (82471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (59, 1), (82471, 1)] : List FactorBlock).map factorBlockValue).prod) = 38926313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_59
      · exact prime_oneHundredSixtyNineFK_82471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 38926313) ^ 19463156 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 38926313) ^ 659768 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 38926313) ^ 472 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_43832023 : Nat.Prime 43832023 := by
  apply lucas_primality 43832023 (3 : ZMod 43832023)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (113, 1), (4973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (113, 1), (4973, 1)] : List FactorBlock).map factorBlockValue).prod) = 43832023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_13
      · exact prime_oneHundredSixtyNineFK_113
      · exact prime_oneHundredSixtyNineFK_4973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 43832023) ^ 21916011 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 43832023) ^ 14610674 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 43832023) ^ 3371694 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 43832023) ^ 387894 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 43832023) ^ 8814 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_45432131 : Nat.Prime 45432131 := by
  apply lucas_primality 45432131 (6 : ZMod 45432131)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (53, 1), (3727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (53, 1), (3727, 1)] : List FactorBlock).map factorBlockValue).prod) = 45432131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_23
      · exact prime_oneHundredSixtyNineFK_53
      · exact prime_oneHundredSixtyNineFK_3727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 45432131) ^ 22716065 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 45432131) ^ 9086426 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 45432131) ^ 1975310 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 45432131) ^ 857210 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 45432131) ^ 12190 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_52025111 : Nat.Prime 52025111 := by
  apply lucas_primality 52025111 (13 : ZMod 52025111)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (5202511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (5202511, 1)] : List FactorBlock).map factorBlockValue).prod) = 52025111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_5202511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 52025111) ^ 26012555 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (13 : ZMod 52025111) ^ 10405022 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (13 : ZMod 52025111) ^ 10 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_54512723 : Nat.Prime 54512723 := by
  apply lucas_primality 54512723 (2 : ZMod 54512723)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (2477851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (2477851, 1)] : List FactorBlock).map factorBlockValue).prod) = 54512723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_11
      · exact prime_oneHundredSixtyNineFK_2477851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 54512723) ^ 27256361 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 54512723) ^ 4955702 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 54512723) ^ 22 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_57110887 : Nat.Prime 57110887 := by
  apply lucas_primality 57110887 (5 : ZMod 57110887)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (23, 1), (6569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (23, 1), (6569, 1)] : List FactorBlock).map factorBlockValue).prod) = 57110887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_23
      · exact prime_oneHundredSixtyNineFK_6569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 57110887) ^ 28555443 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 57110887) ^ 19036962 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 57110887) ^ 8158698 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 57110887) ^ 2483082 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 57110887) ^ 8694 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_62675629 : Nat.Prime 62675629 := by
  apply lucas_primality 62675629 (14 : ZMod 62675629)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (47, 1), (111127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (47, 1), (111127, 1)] : List FactorBlock).map factorBlockValue).prod) = 62675629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_47
      · exact prime_oneHundredSixtyNineFK_111127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 62675629) ^ 31337814 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (14 : ZMod 62675629) ^ 20891876 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (14 : ZMod 62675629) ^ 1333524 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (14 : ZMod 62675629) ^ 564 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_63971657 : Nat.Prime 63971657 := by
  apply lucas_primality 63971657 (3 : ZMod 63971657)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (163193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (163193, 1)] : List FactorBlock).map factorBlockValue).prod) = 63971657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_163193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 63971657) ^ 31985828 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 63971657) ^ 9138808 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 63971657) ^ 392 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_71438987 : Nat.Prime 71438987 := by
  apply lucas_primality 71438987 (2 : ZMod 71438987)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3011, 1), (11863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3011, 1), (11863, 1)] : List FactorBlock).map factorBlockValue).prod) = 71438987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3011
      · exact prime_oneHundredSixtyNineFK_11863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 71438987) ^ 35719493 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 71438987) ^ 23726 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 71438987) ^ 6022 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_76366613 : Nat.Prime 76366613 := by
  apply lucas_primality 76366613 (2 : ZMod 76366613)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (2727379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (2727379, 1)] : List FactorBlock).map factorBlockValue).prod) = 76366613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_2727379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 76366613) ^ 38183306 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 76366613) ^ 10909516 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 76366613) ^ 28 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_77444527 : Nat.Prime 77444527 := by
  apply lucas_primality 77444527 (3 : ZMod 77444527)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (12907421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (12907421, 1)] : List FactorBlock).map factorBlockValue).prod) = 77444527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_12907421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 77444527) ^ 38722263 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 77444527) ^ 25814842 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 77444527) ^ 6 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_89538079 : Nat.Prime 89538079 := by
  apply lucas_primality 89538079 (3 : ZMod 89538079)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (2131859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (2131859, 1)] : List FactorBlock).map factorBlockValue).prod) = 89538079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_2131859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 89538079) ^ 44769039 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 89538079) ^ 29846026 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 89538079) ^ 12791154 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 89538079) ^ 42 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_104050223 : Nat.Prime 104050223 := by
  apply lucas_primality 104050223 (5 : ZMod 104050223)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (52025111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (52025111, 1)] : List FactorBlock).map factorBlockValue).prod) = 104050223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_52025111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 104050223) ^ 52025111 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 104050223) ^ 2 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_108585041 : Nat.Prime 108585041 := by
  apply lucas_primality 108585041 (3 : ZMod 108585041)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (47, 1), (28879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (47, 1), (28879, 1)] : List FactorBlock).map factorBlockValue).prod) = 108585041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_47
      · exact prime_oneHundredSixtyNineFK_28879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 108585041) ^ 54292520 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 108585041) ^ 21717008 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 108585041) ^ 2310320 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 108585041) ^ 3760 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_111327703 : Nat.Prime 111327703 := by
  apply lucas_primality 111327703 (3 : ZMod 111327703)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2131, 1), (8707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2131, 1), (8707, 1)] : List FactorBlock).map factorBlockValue).prod) = 111327703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_2131
      · exact prime_oneHundredSixtyNineFK_8707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 111327703) ^ 55663851 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 111327703) ^ 37109234 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 111327703) ^ 52242 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 111327703) ^ 12786 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_117910999 : Nat.Prime 117910999 := by
  apply lucas_primality 117910999 (3 : ZMod 117910999)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (19, 1), (41, 1), (2803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (19, 1), (41, 1), (2803, 1)] : List FactorBlock).map factorBlockValue).prod) = 117910999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_19
      · exact prime_oneHundredSixtyNineFK_41
      · exact prime_oneHundredSixtyNineFK_2803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 117910999) ^ 58955499 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 117910999) ^ 39303666 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 117910999) ^ 6205842 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 117910999) ^ 2875878 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 117910999) ^ 42066 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_142736729 : Nat.Prime 142736729 := by
  apply lucas_primality 142736729 (3 : ZMod 142736729)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17842091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17842091, 1)] : List FactorBlock).map factorBlockValue).prod) = 142736729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_17842091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 142736729) ^ 71368364 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 142736729) ^ 8 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_148226437 : Nat.Prime 148226437 := by
  apply lucas_primality 148226437 (2 : ZMod 148226437)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (79, 1), (5791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (79, 1), (5791, 1)] : List FactorBlock).map factorBlockValue).prod) = 148226437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_79
      · exact prime_oneHundredSixtyNineFK_5791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 148226437) ^ 74113218 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 148226437) ^ 49408812 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 148226437) ^ 1876284 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 148226437) ^ 25596 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_151180487 : Nat.Prime 151180487 := by
  apply lucas_primality 151180487 (5 : ZMod 151180487)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (1426231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (1426231, 1)] : List FactorBlock).map factorBlockValue).prod) = 151180487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_53
      · exact prime_oneHundredSixtyNineFK_1426231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 151180487) ^ 75590243 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 151180487) ^ 2852462 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 151180487) ^ 106 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_161629603 : Nat.Prime 161629603 := by
  apply lucas_primality 161629603 (2 : ZMod 161629603)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 2), (50923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 2), (50923, 1)] : List FactorBlock).map factorBlockValue).prod) = 161629603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_23
      · exact prime_oneHundredSixtyNineFK_50923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 161629603) ^ 80814801 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 161629603) ^ 53876534 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 161629603) ^ 7027374 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 161629603) ^ 3174 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_172126931 : Nat.Prime 172126931 := by
  apply lucas_primality 172126931 (2 : ZMod 172126931)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17212693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17212693, 1)] : List FactorBlock).map factorBlockValue).prod) = 172126931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_17212693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 172126931) ^ 86063465 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 172126931) ^ 34425386 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 172126931) ^ 10 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_177525119 : Nat.Prime 177525119 := by
  apply lucas_primality 177525119 (7 : ZMod 177525119)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (5221327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (5221327, 1)] : List FactorBlock).map factorBlockValue).prod) = 177525119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_17
      · exact prime_oneHundredSixtyNineFK_5221327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 177525119) ^ 88762559 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 177525119) ^ 10442654 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 177525119) ^ 34 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_179808203 : Nat.Prime 179808203 := by
  apply lucas_primality 179808203 (2 : ZMod 179808203)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (577, 1), (22259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (577, 1), (22259, 1)] : List FactorBlock).map factorBlockValue).prod) = 179808203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_577
      · exact prime_oneHundredSixtyNineFK_22259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 179808203) ^ 89904101 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 179808203) ^ 25686886 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 179808203) ^ 311626 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 179808203) ^ 8078 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_185423809 : Nat.Prime 185423809 := by
  apply lucas_primality 185423809 (11 : ZMod 185423809)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (965749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (965749, 1)] : List FactorBlock).map factorBlockValue).prod) = 185423809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_965749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 185423809) ^ 92711904 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (11 : ZMod 185423809) ^ 61807936 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (11 : ZMod 185423809) ^ 192 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_188872133 : Nat.Prime 188872133 := by
  apply lucas_primality 188872133 (2 : ZMod 188872133)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (131, 1), (7669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (131, 1), (7669, 1)] : List FactorBlock).map factorBlockValue).prod) = 188872133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_47
      · exact prime_oneHundredSixtyNineFK_131
      · exact prime_oneHundredSixtyNineFK_7669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 188872133) ^ 94436066 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 188872133) ^ 4018556 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 188872133) ^ 1441772 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 188872133) ^ 24628 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_190881659 : Nat.Prime 190881659 := by
  apply lucas_primality 190881659 (2 : ZMod 190881659)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (2467, 1), (3517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (2467, 1), (3517, 1)] : List FactorBlock).map factorBlockValue).prod) = 190881659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_11
      · exact prime_oneHundredSixtyNineFK_2467
      · exact prime_oneHundredSixtyNineFK_3517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 190881659) ^ 95440829 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 190881659) ^ 17352878 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 190881659) ^ 77374 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 190881659) ^ 54274 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_208981189 : Nat.Prime 208981189 := by
  apply lucas_primality 208981189 (6 : ZMod 208981189)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (13, 1), (73, 1), (2039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (13, 1), (73, 1), (2039, 1)] : List FactorBlock).map factorBlockValue).prod) = 208981189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_13
      · exact prime_oneHundredSixtyNineFK_73
      · exact prime_oneHundredSixtyNineFK_2039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 208981189) ^ 104490594 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 208981189) ^ 69660396 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 208981189) ^ 16075476 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 208981189) ^ 2862756 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 208981189) ^ 102492 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_217516333 : Nat.Prime 217516333 := by
  apply lucas_primality 217516333 (2 : ZMod 217516333)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (19, 1), (86729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (19, 1), (86729, 1)] : List FactorBlock).map factorBlockValue).prod) = 217516333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_11
      · exact prime_oneHundredSixtyNineFK_19
      · exact prime_oneHundredSixtyNineFK_86729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 217516333) ^ 108758166 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 217516333) ^ 72505444 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 217516333) ^ 19774212 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 217516333) ^ 11448228 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 217516333) ^ 2508 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_228443549 : Nat.Prime 228443549 := by
  apply lucas_primality 228443549 (2 : ZMod 228443549)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (57110887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (57110887, 1)] : List FactorBlock).map factorBlockValue).prod) = 228443549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_57110887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 228443549) ^ 114221774 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 228443549) ^ 4 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_271696417 : Nat.Prime 271696417 := by
  apply lucas_primality 271696417 (13 : ZMod 271696417)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (59, 1), (47969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (59, 1), (47969, 1)] : List FactorBlock).map factorBlockValue).prod) = 271696417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_59
      · exact prime_oneHundredSixtyNineFK_47969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 271696417) ^ 135848208 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (13 : ZMod 271696417) ^ 90565472 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (13 : ZMod 271696417) ^ 4605024 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (13 : ZMod 271696417) ^ 5664 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_278795717 : Nat.Prime 278795717 := by
  apply lucas_primality 278795717 (2 : ZMod 278795717)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (941, 1), (4357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (941, 1), (4357, 1)] : List FactorBlock).map factorBlockValue).prod) = 278795717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_17
      · exact prime_oneHundredSixtyNineFK_941
      · exact prime_oneHundredSixtyNineFK_4357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 278795717) ^ 139397858 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 278795717) ^ 16399748 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 278795717) ^ 296276 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 278795717) ^ 63988 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_280261253 : Nat.Prime 280261253 := by
  apply lucas_primality 280261253 (2 : ZMod 280261253)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (139, 1), (149, 1), (199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (139, 1), (149, 1), (199, 1)] : List FactorBlock).map factorBlockValue).prod) = 280261253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_17
      · exact prime_oneHundredSixtyNineFK_139
      · exact prime_oneHundredSixtyNineFK_149
      · exact prime_oneHundredSixtyNineFK_199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 280261253) ^ 140130626 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 280261253) ^ 16485956 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 280261253) ^ 2016268 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 280261253) ^ 1880948 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 280261253) ^ 1408348 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_303220441 : Nat.Prime 303220441 := by
  apply lucas_primality 303220441 (11 : ZMod 303220441)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (842279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (842279, 1)] : List FactorBlock).map factorBlockValue).prod) = 303220441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_842279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 303220441) ^ 151610220 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (11 : ZMod 303220441) ^ 101073480 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (11 : ZMod 303220441) ^ 60644088 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (11 : ZMod 303220441) ^ 360 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_322545397 : Nat.Prime 322545397 := by
  apply lucas_primality 322545397 (6 : ZMod 322545397)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (47, 1), (337, 1), (1697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (47, 1), (337, 1), (1697, 1)] : List FactorBlock).map factorBlockValue).prod) = 322545397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_47
      · exact prime_oneHundredSixtyNineFK_337
      · exact prime_oneHundredSixtyNineFK_1697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 322545397) ^ 161272698 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 322545397) ^ 107515132 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 322545397) ^ 6862668 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 322545397) ^ 957108 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 322545397) ^ 190068 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_340011313 : Nat.Prime 340011313 := by
  apply lucas_primality 340011313 (7 : ZMod 340011313)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (29, 1), (244261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (29, 1), (244261, 1)] : List FactorBlock).map factorBlockValue).prod) = 340011313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_29
      · exact prime_oneHundredSixtyNineFK_244261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 340011313) ^ 170005656 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 340011313) ^ 113337104 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 340011313) ^ 11724528 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 340011313) ^ 1392 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_344253863 : Nat.Prime 344253863 := by
  apply lucas_primality 344253863 (5 : ZMod 344253863)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (172126931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (172126931, 1)] : List FactorBlock).map factorBlockValue).prod) = 344253863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_172126931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 344253863) ^ 172126931 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 344253863) ^ 2 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_345695209 : Nat.Prime 345695209 := by
  apply lucas_primality 345695209 (13 : ZMod 345695209)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (14403967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (14403967, 1)] : List FactorBlock).map factorBlockValue).prod) = 345695209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_14403967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 345695209) ^ 172847604 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (13 : ZMod 345695209) ^ 115231736 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (13 : ZMod 345695209) ^ 24 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_349996873 : Nat.Prime 349996873 := by
  apply lucas_primality 349996873 (11 : ZMod 349996873)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (767537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (767537, 1)] : List FactorBlock).map factorBlockValue).prod) = 349996873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_19
      · exact prime_oneHundredSixtyNineFK_767537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 349996873) ^ 174998436 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (11 : ZMod 349996873) ^ 116665624 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (11 : ZMod 349996873) ^ 18420888 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (11 : ZMod 349996873) ^ 456 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_380836031 : Nat.Prime 380836031 := by
  apply lucas_primality 380836031 (7 : ZMod 380836031)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (38083603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (38083603, 1)] : List FactorBlock).map factorBlockValue).prod) = 380836031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_38083603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 380836031) ^ 190418015 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 380836031) ^ 76167206 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 380836031) ^ 10 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_381092209 : Nat.Prime 381092209 := by
  apply lucas_primality 381092209 (23 : ZMod 381092209)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 3), (79, 1), (293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 3), (79, 1), (293, 1)] : List FactorBlock).map factorBlockValue).prod) = 381092209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_79
      · exact prime_oneHundredSixtyNineFK_293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 381092209) ^ 190546104 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (23 : ZMod 381092209) ^ 127030736 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (23 : ZMod 381092209) ^ 54441744 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (23 : ZMod 381092209) ^ 4823952 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (23 : ZMod 381092209) ^ 1300656 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_390825023 : Nat.Prime 390825023 := by
  apply lucas_primality 390825023 (5 : ZMod 390825023)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (43, 1), (47, 1), (727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (43, 1), (47, 1), (727, 1)] : List FactorBlock).map factorBlockValue).prod) = 390825023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_19
      · exact prime_oneHundredSixtyNineFK_43
      · exact prime_oneHundredSixtyNineFK_47
      · exact prime_oneHundredSixtyNineFK_727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 390825023) ^ 195412511 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 390825023) ^ 55832146 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 390825023) ^ 20569738 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 390825023) ^ 9088954 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 390825023) ^ 8315426 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 390825023) ^ 537586 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_397943603 : Nat.Prime 397943603 := by
  apply lucas_primality 397943603 (5 : ZMod 397943603)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (359, 1), (11311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (359, 1), (11311, 1)] : List FactorBlock).map factorBlockValue).prod) = 397943603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_359
      · exact prime_oneHundredSixtyNineFK_11311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 397943603) ^ 198971801 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 397943603) ^ 56849086 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 397943603) ^ 1108478 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 397943603) ^ 35182 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_420081737 : Nat.Prime 420081737 := by
  apply lucas_primality 420081737 (3 : ZMod 420081737)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (41, 1), (1280737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (41, 1), (1280737, 1)] : List FactorBlock).map factorBlockValue).prod) = 420081737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_41
      · exact prime_oneHundredSixtyNineFK_1280737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 420081737) ^ 210040868 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 420081737) ^ 10245896 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 420081737) ^ 328 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_425074411 : Nat.Prime 425074411 := by
  apply lucas_primality 425074411 (3 : ZMod 425074411)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (4723049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (4723049, 1)] : List FactorBlock).map factorBlockValue).prod) = 425074411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_4723049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 425074411) ^ 212537205 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 425074411) ^ 141691470 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 425074411) ^ 85014882 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 425074411) ^ 90 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_429543953 : Nat.Prime 429543953 := by
  apply lucas_primality 429543953 (3 : ZMod 429543953)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (23, 1), (37, 1), (31547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (23, 1), (37, 1), (31547, 1)] : List FactorBlock).map factorBlockValue).prod) = 429543953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_23
      · exact prime_oneHundredSixtyNineFK_37
      · exact prime_oneHundredSixtyNineFK_31547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 429543953) ^ 214771976 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 429543953) ^ 18675824 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 429543953) ^ 11609296 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 429543953) ^ 13616 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_475279939 : Nat.Prime 475279939 := by
  apply lucas_primality 475279939 (3 : ZMod 475279939)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (53, 1), (71171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (53, 1), (71171, 1)] : List FactorBlock).map factorBlockValue).prod) = 475279939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_53
      · exact prime_oneHundredSixtyNineFK_71171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 475279939) ^ 237639969 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 475279939) ^ 158426646 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 475279939) ^ 67897134 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 475279939) ^ 8967546 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 475279939) ^ 6678 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_534260401 : Nat.Prime 534260401 := by
  apply lucas_primality 534260401 (14 : ZMod 534260401)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 2), (139, 1), (3203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 2), (139, 1), (3203, 1)] : List FactorBlock).map factorBlockValue).prod) = 534260401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_139
      · exact prime_oneHundredSixtyNineFK_3203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 534260401) ^ 267130200 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (14 : ZMod 534260401) ^ 178086800 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (14 : ZMod 534260401) ^ 106852080 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (14 : ZMod 534260401) ^ 3843600 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (14 : ZMod 534260401) ^ 166800 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_540354739 : Nat.Prime 540354739 := by
  apply lucas_primality 540354739 (3 : ZMod 540354739)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (29, 1), (31, 1), (1301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (29, 1), (31, 1), (1301, 1)] : List FactorBlock).map factorBlockValue).prod) = 540354739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_11
      · exact prime_oneHundredSixtyNineFK_29
      · exact prime_oneHundredSixtyNineFK_31
      · exact prime_oneHundredSixtyNineFK_1301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 540354739) ^ 270177369 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 540354739) ^ 180118246 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 540354739) ^ 77193534 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 540354739) ^ 49123158 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 540354739) ^ 18632922 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 540354739) ^ 17430798 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 540354739) ^ 415338 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_540669361 : Nat.Prime 540669361 := by
  apply lucas_primality 540669361 (13 : ZMod 540669361)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (7, 1), (11, 1), (17, 1), (1721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (7, 1), (11, 1), (17, 1), (1721, 1)] : List FactorBlock).map factorBlockValue).prod) = 540669361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_11
      · exact prime_oneHundredSixtyNineFK_17
      · exact prime_oneHundredSixtyNineFK_1721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 540669361) ^ 270334680 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (13 : ZMod 540669361) ^ 180223120 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (13 : ZMod 540669361) ^ 108133872 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (13 : ZMod 540669361) ^ 77238480 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (13 : ZMod 540669361) ^ 49151760 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (13 : ZMod 540669361) ^ 31804080 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (13 : ZMod 540669361) ^ 314160 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_560792161 : Nat.Prime 560792161 := by
  apply lucas_primality 560792161 (7 : ZMod 560792161)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 4), (5, 1), (43271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 4), (5, 1), (43271, 1)] : List FactorBlock).map factorBlockValue).prod) = 560792161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_43271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 560792161) ^ 280396080 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 560792161) ^ 186930720 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 560792161) ^ 112158432 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 560792161) ^ 12960 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_570725087 : Nat.Prime 570725087 := by
  apply lucas_primality 570725087 (5 : ZMod 570725087)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12251, 1), (23293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12251, 1), (23293, 1)] : List FactorBlock).map factorBlockValue).prod) = 570725087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_12251
      · exact prime_oneHundredSixtyNineFK_23293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 570725087) ^ 285362543 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 570725087) ^ 46586 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 570725087) ^ 24502 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_576225343 : Nat.Prime 576225343 := by
  apply lucas_primality 576225343 (3 : ZMod 576225343)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (11, 1), (83, 1), (5009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (11, 1), (83, 1), (5009, 1)] : List FactorBlock).map factorBlockValue).prod) = 576225343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_11
      · exact prime_oneHundredSixtyNineFK_83
      · exact prime_oneHundredSixtyNineFK_5009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 576225343) ^ 288112671 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 576225343) ^ 192075114 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 576225343) ^ 82317906 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 576225343) ^ 52384122 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 576225343) ^ 6942474 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 576225343) ^ 115038 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_646518413 : Nat.Prime 646518413 := by
  apply lucas_primality 646518413 (2 : ZMod 646518413)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (161629603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (161629603, 1)] : List FactorBlock).map factorBlockValue).prod) = 646518413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_161629603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 646518413) ^ 323259206 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 646518413) ^ 4 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_656032253 : Nat.Prime 656032253 := by
  apply lucas_primality 656032253 (2 : ZMod 656032253)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (701, 1), (5441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (701, 1), (5441, 1)] : List FactorBlock).map factorBlockValue).prod) = 656032253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_43
      · exact prime_oneHundredSixtyNineFK_701
      · exact prime_oneHundredSixtyNineFK_5441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 656032253) ^ 328016126 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 656032253) ^ 15256564 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 656032253) ^ 935852 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 656032253) ^ 120572 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_686518747 : Nat.Prime 686518747 := by
  apply lucas_primality 686518747 (3 : ZMod 686518747)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (3690961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (3690961, 1)] : List FactorBlock).map factorBlockValue).prod) = 686518747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_31
      · exact prime_oneHundredSixtyNineFK_3690961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 686518747) ^ 343259373 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 686518747) ^ 228839582 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 686518747) ^ 22145766 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 686518747) ^ 186 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_17203
      · exact prime_oneHundredSixtyNineFK_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_719749531 : Nat.Prime 719749531 := by
  apply lucas_primality 719749531 (2 : ZMod 719749531)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (37, 1), (72047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (37, 1), (72047, 1)] : List FactorBlock).map factorBlockValue).prod) = 719749531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_37
      · exact prime_oneHundredSixtyNineFK_72047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 719749531) ^ 359874765 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 719749531) ^ 239916510 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 719749531) ^ 143949906 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 719749531) ^ 19452690 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 719749531) ^ 9990 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_820351907 : Nat.Prime 820351907 := by
  apply lucas_primality 820351907 (2 : ZMod 820351907)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (37288723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (37288723, 1)] : List FactorBlock).map factorBlockValue).prod) = 820351907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_11
      · exact prime_oneHundredSixtyNineFK_37288723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 820351907) ^ 410175953 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 820351907) ^ 74577446 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 820351907) ^ 22 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_870065333 : Nat.Prime 870065333 := by
  apply lucas_primality 870065333 (2 : ZMod 870065333)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (217516333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (217516333, 1)] : List FactorBlock).map factorBlockValue).prod) = 870065333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_217516333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 870065333) ^ 435032666 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 870065333) ^ 4 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_988735051 : Nat.Prime 988735051 := by
  apply lucas_primality 988735051 (12 : ZMod 988735051)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (2197189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (2197189, 1)] : List FactorBlock).map factorBlockValue).prod) = 988735051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_2197189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (12 : ZMod 988735051) ^ 494367525 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (12 : ZMod 988735051) ^ 329578350 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (12 : ZMod 988735051) ^ 197747010 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (12 : ZMod 988735051) ^ 450 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_1090254461 : Nat.Prime 1090254461 := by
  apply lucas_primality 1090254461 (2 : ZMod 1090254461)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (54512723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (54512723, 1)] : List FactorBlock).map factorBlockValue).prod) = 1090254461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_54512723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1090254461) ^ 545127230 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1090254461) ^ 218050892 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1090254461) ^ 20 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_1104994447 : Nat.Prime 1104994447 := by
  apply lucas_primality 1104994447 (5 : ZMod 1104994447)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3469, 1), (53089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3469, 1), (53089, 1)] : List FactorBlock).map factorBlockValue).prod) = 1104994447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_3469
      · exact prime_oneHundredSixtyNineFK_53089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1104994447) ^ 552497223 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1104994447) ^ 368331482 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1104994447) ^ 318534 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1104994447) ^ 20814 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_1133232799 : Nat.Prime 1133232799 := by
  apply lucas_primality 1133232799 (3 : ZMod 1133232799)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (188872133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (188872133, 1)] : List FactorBlock).map factorBlockValue).prod) = 1133232799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_188872133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1133232799) ^ 566616399 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1133232799) ^ 377744266 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1133232799) ^ 6 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_1155669637 : Nat.Prime 1155669637 := by
  apply lucas_primality 1155669637 (5 : ZMod 1155669637)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (8755073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (8755073, 1)] : List FactorBlock).map factorBlockValue).prod) = 1155669637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_11
      · exact prime_oneHundredSixtyNineFK_8755073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1155669637) ^ 577834818 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1155669637) ^ 385223212 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1155669637) ^ 105060876 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1155669637) ^ 132 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_1251818357 : Nat.Prime 1251818357 := by
  apply lucas_primality 1251818357 (2 : ZMod 1251818357)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (10069, 1), (31081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (10069, 1), (31081, 1)] : List FactorBlock).map factorBlockValue).prod) = 1251818357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_10069
      · exact prime_oneHundredSixtyNineFK_31081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1251818357) ^ 625909178 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1251818357) ^ 124324 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1251818357) ^ 40276 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_1439833793 : Nat.Prime 1439833793 := by
  apply lucas_primality 1439833793 (3 : ZMod 1439833793)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (22497403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (22497403, 1)] : List FactorBlock).map factorBlockValue).prod) = 1439833793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_22497403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1439833793) ^ 719916896 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1439833793) ^ 64 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_1449169259 : Nat.Prime 1449169259 := by
  apply lucas_primality 1449169259 (2 : ZMod 1449169259)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1459, 1), (496631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1459, 1), (496631, 1)] : List FactorBlock).map factorBlockValue).prod) = 1449169259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_1459
      · exact prime_oneHundredSixtyNineFK_496631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1449169259) ^ 724584629 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1449169259) ^ 993262 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1449169259) ^ 2918 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_1456991891 : Nat.Prime 1456991891 := by
  apply lucas_primality 1456991891 (2 : ZMod 1456991891)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (229, 1), (636241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (229, 1), (636241, 1)] : List FactorBlock).map factorBlockValue).prod) = 1456991891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_229
      · exact prime_oneHundredSixtyNineFK_636241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1456991891) ^ 728495945 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1456991891) ^ 291398378 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1456991891) ^ 6362410 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1456991891) ^ 2290 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_1636666841 : Nat.Prime 1636666841 := by
  apply lucas_primality 1636666841 (6 : ZMod 1636666841)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (17, 1), (19, 1), (131, 1), (967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (17, 1), (19, 1), (131, 1), (967, 1)] : List FactorBlock).map factorBlockValue).prod) = 1636666841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_17
      · exact prime_oneHundredSixtyNineFK_19
      · exact prime_oneHundredSixtyNineFK_131
      · exact prime_oneHundredSixtyNineFK_967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1636666841) ^ 818333420 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1636666841) ^ 327333368 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1636666841) ^ 96274520 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1636666841) ^ 86140360 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1636666841) ^ 12493640 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1636666841) ^ 1692520 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_1690142863 : Nat.Prime 1690142863 := by
  apply lucas_primality 1690142863 (5 : ZMod 1690142863)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (103, 1), (449, 1), (6091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (103, 1), (449, 1), (6091, 1)] : List FactorBlock).map factorBlockValue).prod) = 1690142863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_103
      · exact prime_oneHundredSixtyNineFK_449
      · exact prime_oneHundredSixtyNineFK_6091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1690142863) ^ 845071431 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1690142863) ^ 563380954 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1690142863) ^ 16409154 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1690142863) ^ 3764238 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1690142863) ^ 277482 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_1798922659 : Nat.Prime 1798922659 := by
  apply lucas_primality 1798922659 (7 : ZMod 1798922659)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (383, 1), (60217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (383, 1), (60217, 1)] : List FactorBlock).map factorBlockValue).prod) = 1798922659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_13
      · exact prime_oneHundredSixtyNineFK_383
      · exact prime_oneHundredSixtyNineFK_60217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1798922659) ^ 899461329 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 1798922659) ^ 599640886 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 1798922659) ^ 138378666 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 1798922659) ^ 4696926 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 1798922659) ^ 29874 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_1946743373 : Nat.Prime 1946743373 := by
  apply lucas_primality 1946743373 (2 : ZMod 1946743373)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (17, 1), (139, 1), (29423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (17, 1), (139, 1), (29423, 1)] : List FactorBlock).map factorBlockValue).prod) = 1946743373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_17
      · exact prime_oneHundredSixtyNineFK_139
      · exact prime_oneHundredSixtyNineFK_29423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1946743373) ^ 973371686 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1946743373) ^ 278106196 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1946743373) ^ 114514316 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1946743373) ^ 14005348 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1946743373) ^ 66164 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_2034430429 : Nat.Prime 2034430429 := by
  apply lucas_primality 2034430429 (2 : ZMod 2034430429)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (31, 1), (5468899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (31, 1), (5468899, 1)] : List FactorBlock).map factorBlockValue).prod) = 2034430429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_31
      · exact prime_oneHundredSixtyNineFK_5468899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2034430429) ^ 1017215214 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2034430429) ^ 678143476 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2034430429) ^ 65626788 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2034430429) ^ 372 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_2341024841 : Nat.Prime 2341024841 := by
  apply lucas_primality 2341024841 (3 : ZMod 2341024841)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (11, 1), (53, 1), (14341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (11, 1), (53, 1), (14341, 1)] : List FactorBlock).map factorBlockValue).prod) = 2341024841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_11
      · exact prime_oneHundredSixtyNineFK_53
      · exact prime_oneHundredSixtyNineFK_14341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2341024841) ^ 1170512420 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2341024841) ^ 468204968 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2341024841) ^ 334432120 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2341024841) ^ 212820440 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2341024841) ^ 44170280 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2341024841) ^ 163240 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_2470527071 : Nat.Prime 2470527071 := by
  apply lucas_primality 2470527071 (17 : ZMod 2470527071)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (22459337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (22459337, 1)] : List FactorBlock).map factorBlockValue).prod) = 2470527071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_11
      · exact prime_oneHundredSixtyNineFK_22459337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 2470527071) ^ 1235263535 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (17 : ZMod 2470527071) ^ 494105414 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (17 : ZMod 2470527071) ^ 224593370 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (17 : ZMod 2470527071) ^ 110 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_3153829117 : Nat.Prime 3153829117 := by
  apply lucas_primality 3153829117 (2 : ZMod 3153829117)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1193, 1), (220301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1193, 1), (220301, 1)] : List FactorBlock).map factorBlockValue).prod) = 3153829117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_1193
      · exact prime_oneHundredSixtyNineFK_220301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3153829117) ^ 1576914558 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3153829117) ^ 1051276372 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3153829117) ^ 2643612 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3153829117) ^ 14316 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_3205562407 : Nat.Prime 3205562407 := by
  apply lucas_primality 3205562407 (3 : ZMod 3205562407)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (534260401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (534260401, 1)] : List FactorBlock).map factorBlockValue).prod) = 3205562407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_534260401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3205562407) ^ 1602781203 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3205562407) ^ 1068520802 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3205562407) ^ 6 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_4576435033 : Nat.Prime 4576435033 := by
  apply lucas_primality 4576435033 (5 : ZMod 4576435033)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (421, 1), (34841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (421, 1), (34841, 1)] : List FactorBlock).map factorBlockValue).prod) = 4576435033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_13
      · exact prime_oneHundredSixtyNineFK_421
      · exact prime_oneHundredSixtyNineFK_34841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4576435033) ^ 2288217516 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 4576435033) ^ 1525478344 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 4576435033) ^ 352033464 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 4576435033) ^ 10870392 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 4576435033) ^ 131352 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_4888699063 : Nat.Prime 4888699063 := by
  apply lucas_primality 4888699063 (3 : ZMod 4888699063)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (62675629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (62675629, 1)] : List FactorBlock).map factorBlockValue).prod) = 4888699063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_13
      · exact prime_oneHundredSixtyNineFK_62675629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4888699063) ^ 2444349531 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 4888699063) ^ 1629566354 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 4888699063) ^ 376053774 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 4888699063) ^ 78 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_5220391999 : Nat.Prime 5220391999 := by
  apply lucas_primality 5220391999 (3 : ZMod 5220391999)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (870065333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (870065333, 1)] : List FactorBlock).map factorBlockValue).prod) = 5220391999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_870065333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5220391999) ^ 2610195999 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5220391999) ^ 1740130666 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5220391999) ^ 6 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_5350556923 : Nat.Prime 5350556923 := by
  apply lucas_primality 5350556923 (2 : ZMod 5350556923)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (149, 1), (5984963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (149, 1), (5984963, 1)] : List FactorBlock).map factorBlockValue).prod) = 5350556923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_149
      · exact prime_oneHundredSixtyNineFK_5984963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5350556923) ^ 2675278461 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5350556923) ^ 1783518974 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5350556923) ^ 35909778 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5350556923) ^ 894 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_31
      · exact prime_oneHundredSixtyNineFK_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_6247479877 : Nat.Prime 6247479877 := by
  apply lucas_primality 6247479877 (2 : ZMod 6247479877)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (787, 1), (60139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (787, 1), (60139, 1)] : List FactorBlock).map factorBlockValue).prod) = 6247479877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_11
      · exact prime_oneHundredSixtyNineFK_787
      · exact prime_oneHundredSixtyNineFK_60139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6247479877) ^ 3123739938 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6247479877) ^ 2082493292 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6247479877) ^ 567952716 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6247479877) ^ 7938348 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6247479877) ^ 103884 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_6998309863 : Nat.Prime 6998309863 := by
  apply lucas_primality 6998309863 (3 : ZMod 6998309863)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (19, 1), (67, 1), (53897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (19, 1), (67, 1), (53897, 1)] : List FactorBlock).map factorBlockValue).prod) = 6998309863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_17
      · exact prime_oneHundredSixtyNineFK_19
      · exact prime_oneHundredSixtyNineFK_67
      · exact prime_oneHundredSixtyNineFK_53897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6998309863) ^ 3499154931 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 6998309863) ^ 2332769954 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 6998309863) ^ 411665286 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 6998309863) ^ 368332098 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 6998309863) ^ 104452386 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 6998309863) ^ 129846 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_7072164523 : Nat.Prime 7072164523 := by
  apply lucas_primality 7072164523 (2 : ZMod 7072164523)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (23, 1), (443, 1), (38561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (23, 1), (443, 1), (38561, 1)] : List FactorBlock).map factorBlockValue).prod) = 7072164523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_23
      · exact prime_oneHundredSixtyNineFK_443
      · exact prime_oneHundredSixtyNineFK_38561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7072164523) ^ 3536082261 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 7072164523) ^ 2357388174 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 7072164523) ^ 307485414 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 7072164523) ^ 15964254 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 7072164523) ^ 183402 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_9257508937 : Nat.Prime 9257508937 := by
  apply lucas_primality 9257508937 (5 : ZMod 9257508937)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (13, 1), (9890501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (13, 1), (9890501, 1)] : List FactorBlock).map factorBlockValue).prod) = 9257508937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_13
      · exact prime_oneHundredSixtyNineFK_9890501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9257508937) ^ 4628754468 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 9257508937) ^ 3085836312 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 9257508937) ^ 712116072 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 9257508937) ^ 936 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_10464804083 : Nat.Prime 10464804083 := by
  apply lucas_primality 10464804083 (2 : ZMod 10464804083)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (111327703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (111327703, 1)] : List FactorBlock).map factorBlockValue).prod) = 10464804083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_47
      · exact prime_oneHundredSixtyNineFK_111327703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 10464804083) ^ 5232402041 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 10464804083) ^ 222655406 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 10464804083) ^ 94 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_10966543499 : Nat.Prime 10966543499 := by
  apply lucas_primality 10966543499 (2 : ZMod 10966543499)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (322545397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (322545397, 1)] : List FactorBlock).map factorBlockValue).prod) = 10966543499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_17
      · exact prime_oneHundredSixtyNineFK_322545397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 10966543499) ^ 5483271749 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 10966543499) ^ 645090794 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 10966543499) ^ 34 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_12886318591 : Nat.Prime 12886318591 := by
  apply lucas_primality 12886318591 (6 : ZMod 12886318591)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (429543953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (429543953, 1)] : List FactorBlock).map factorBlockValue).prod) = 12886318591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_429543953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 12886318591) ^ 6443159295 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 12886318591) ^ 4295439530 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 12886318591) ^ 2577263718 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 12886318591) ^ 30 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_13232933419 : Nat.Prime 13232933419 := by
  apply lucas_primality 13232933419 (10 : ZMod 13232933419)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (97, 1), (2693, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (97, 1), (2693, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod) = 13232933419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_97
      · exact prime_oneHundredSixtyNineFK_2693
      · exact prime_oneHundredSixtyNineFK_8443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 13232933419) ^ 6616466709 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (10 : ZMod 13232933419) ^ 4410977806 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (10 : ZMod 13232933419) ^ 136421994 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (10 : ZMod 13232933419) ^ 4913826 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (10 : ZMod 13232933419) ^ 1567326 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_13402470019 : Nat.Prime 13402470019 := by
  apply lucas_primality 13402470019 (2 : ZMod 13402470019)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (97, 1), (3289757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (97, 1), (3289757, 1)] : List FactorBlock).map factorBlockValue).prod) = 13402470019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_97
      · exact prime_oneHundredSixtyNineFK_3289757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13402470019) ^ 6701235009 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 13402470019) ^ 4467490006 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 13402470019) ^ 1914638574 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 13402470019) ^ 138169794 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 13402470019) ^ 4074 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_13517518187 : Nat.Prime 13517518187 := by
  apply lucas_primality 13517518187 (2 : ZMod 13517518187)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (73, 1), (359, 1), (11213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (73, 1), (359, 1), (11213, 1)] : List FactorBlock).map factorBlockValue).prod) = 13517518187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_23
      · exact prime_oneHundredSixtyNineFK_73
      · exact prime_oneHundredSixtyNineFK_359
      · exact prime_oneHundredSixtyNineFK_11213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13517518187) ^ 6758759093 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 13517518187) ^ 587718182 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 13517518187) ^ 185171482 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 13517518187) ^ 37653254 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 13517518187) ^ 1205522 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_14671606519 : Nat.Prime 14671606519 := by
  apply lucas_primality 14671606519 (6 : ZMod 14671606519)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (271696417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (271696417, 1)] : List FactorBlock).map factorBlockValue).prod) = 14671606519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_271696417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 14671606519) ^ 7335803259 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 14671606519) ^ 4890535506 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 14671606519) ^ 54 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_20848327873 : Nat.Prime 20848327873 := by
  apply lucas_primality 20848327873 (5 : ZMod 20848327873)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (108585041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (108585041, 1)] : List FactorBlock).map factorBlockValue).prod) = 20848327873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_108585041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 20848327873) ^ 10424163936 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 20848327873) ^ 6949442624 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 20848327873) ^ 192 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_24989919509 : Nat.Prime 24989919509 := by
  apply lucas_primality 24989919509 (2 : ZMod 24989919509)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (6247479877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (6247479877, 1)] : List FactorBlock).map factorBlockValue).prod) = 24989919509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_6247479877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 24989919509) ^ 12494959754 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 24989919509) ^ 4 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_25681749661 : Nat.Prime 25681749661 := by
  apply lucas_primality 25681749661 (2 : ZMod 25681749661)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (7, 2), (173, 1), (16831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (7, 2), (173, 1), (16831, 1)] : List FactorBlock).map factorBlockValue).prod) = 25681749661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_173
      · exact prime_oneHundredSixtyNineFK_16831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 25681749661) ^ 12840874830 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 25681749661) ^ 8560583220 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 25681749661) ^ 5136349932 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 25681749661) ^ 3668821380 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 25681749661) ^ 148449420 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 25681749661) ^ 1525860 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_26702345737 : Nat.Prime 26702345737 := by
  apply lucas_primality 26702345737 (5 : ZMod 26702345737)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (11, 1), (163, 1), (68947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (11, 1), (163, 1), (68947, 1)] : List FactorBlock).map factorBlockValue).prod) = 26702345737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_11
      · exact prime_oneHundredSixtyNineFK_163
      · exact prime_oneHundredSixtyNineFK_68947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 26702345737) ^ 13351172868 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 26702345737) ^ 8900781912 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 26702345737) ^ 2427485976 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 26702345737) ^ 163818072 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 26702345737) ^ 387288 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_28563801229 : Nat.Prime 28563801229 := by
  apply lucas_primality 28563801229 (2 : ZMod 28563801229)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (4259, 1), (62099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (4259, 1), (62099, 1)] : List FactorBlock).map factorBlockValue).prod) = 28563801229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_4259
      · exact prime_oneHundredSixtyNineFK_62099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 28563801229) ^ 14281900614 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 28563801229) ^ 9521267076 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 28563801229) ^ 6706692 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 28563801229) ^ 459972 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_29392746433 : Nat.Prime 29392746433 := by
  apply lucas_primality 29392746433 (5 : ZMod 29392746433)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (7, 2), (607, 1), (5147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (7, 2), (607, 1), (5147, 1)] : List FactorBlock).map factorBlockValue).prod) = 29392746433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_607
      · exact prime_oneHundredSixtyNineFK_5147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 29392746433) ^ 14696373216 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 29392746433) ^ 9797582144 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 29392746433) ^ 4198963776 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 29392746433) ^ 48422976 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 29392746433) ^ 5710656 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_33222407093 : Nat.Prime 33222407093 := by
  apply lucas_primality 33222407093 (2 : ZMod 33222407093)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (41, 1), (223, 1), (18539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (41, 1), (223, 1), (18539, 1)] : List FactorBlock).map factorBlockValue).prod) = 33222407093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_41
      · exact prime_oneHundredSixtyNineFK_223
      · exact prime_oneHundredSixtyNineFK_18539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 33222407093) ^ 16611203546 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 33222407093) ^ 4746058156 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 33222407093) ^ 810302612 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 33222407093) ^ 148979404 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 33222407093) ^ 1792028 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_37519202209 : Nat.Prime 37519202209 := by
  apply lucas_primality 37519202209 (7 : ZMod 37519202209)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (390825023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (390825023, 1)] : List FactorBlock).map factorBlockValue).prod) = 37519202209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_390825023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 37519202209) ^ 18759601104 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 37519202209) ^ 12506400736 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 37519202209) ^ 96 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_38081267057 : Nat.Prime 38081267057 := by
  apply lucas_primality 38081267057 (3 : ZMod 38081267057)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (340011313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (340011313, 1)] : List FactorBlock).map factorBlockValue).prod) = 38081267057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_340011313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 38081267057) ^ 19040633528 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 38081267057) ^ 5440181008 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 38081267057) ^ 112 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_39165895343 : Nat.Prime 39165895343 := by
  apply lucas_primality 39165895343 (5 : ZMod 39165895343)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (101, 1), (149, 1), (185897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (101, 1), (149, 1), (185897, 1)] : List FactorBlock).map factorBlockValue).prod) = 39165895343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_101
      · exact prime_oneHundredSixtyNineFK_149
      · exact prime_oneHundredSixtyNineFK_185897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 39165895343) ^ 19582947671 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 39165895343) ^ 5595127906 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 39165895343) ^ 387781142 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 39165895343) ^ 262858358 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 39165895343) ^ 210686 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_52931733677 : Nat.Prime 52931733677 := by
  apply lucas_primality 52931733677 (2 : ZMod 52931733677)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13232933419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13232933419, 1)] : List FactorBlock).map factorBlockValue).prod) = 52931733677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_13232933419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 52931733677) ^ 26465866838 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 52931733677) ^ 4 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_55365691859 : Nat.Prime 55365691859 := by
  apply lucas_primality 55365691859 (2 : ZMod 55365691859)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (1456991891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (1456991891, 1)] : List FactorBlock).map factorBlockValue).prod) = 55365691859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_19
      · exact prime_oneHundredSixtyNineFK_1456991891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 55365691859) ^ 27682845929 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 55365691859) ^ 2913983782 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 55365691859) ^ 38 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_58928105549 : Nat.Prime 58928105549 := by
  apply lucas_primality 58928105549 (2 : ZMod 58928105549)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (1133232799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (1133232799, 1)] : List FactorBlock).map factorBlockValue).prod) = 58928105549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_13
      · exact prime_oneHundredSixtyNineFK_1133232799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 58928105549) ^ 29464052774 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 58928105549) ^ 4532931196 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 58928105549) ^ 52 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_82854009379 : Nat.Prime 82854009379 := by
  apply lucas_primality 82854009379 (3 : ZMod 82854009379)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (163, 1), (1344727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (163, 1), (1344727, 1)] : List FactorBlock).map factorBlockValue).prod) = 82854009379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_163
      · exact prime_oneHundredSixtyNineFK_1344727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 82854009379) ^ 41427004689 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 82854009379) ^ 27618003126 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 82854009379) ^ 11836287054 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 82854009379) ^ 508306806 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 82854009379) ^ 61614 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_90978926309 : Nat.Prime 90978926309 := by
  apply lucas_primality 90978926309 (2 : ZMod 90978926309)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5101, 1), (4458877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5101, 1), (4458877, 1)] : List FactorBlock).map factorBlockValue).prod) = 90978926309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5101
      · exact prime_oneHundredSixtyNineFK_4458877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 90978926309) ^ 45489463154 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 90978926309) ^ 17835508 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 90978926309) ^ 20404 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_112225536263 : Nat.Prime 112225536263 := by
  apply lucas_primality 112225536263 (5 : ZMod 112225536263)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (29, 1), (2267, 1), (121931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (29, 1), (2267, 1), (121931, 1)] : List FactorBlock).map factorBlockValue).prod) = 112225536263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_29
      · exact prime_oneHundredSixtyNineFK_2267
      · exact prime_oneHundredSixtyNineFK_121931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 112225536263) ^ 56112768131 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 112225536263) ^ 16032219466 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 112225536263) ^ 3869846078 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 112225536263) ^ 49503986 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 112225536263) ^ 920402 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_118662433481 : Nat.Prime 118662433481 := by
  apply lucas_primality 118662433481 (6 : ZMod 118662433481)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (71, 1), (79, 1), (263, 1), (2011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (71, 1), (79, 1), (263, 1), (2011, 1)] : List FactorBlock).map factorBlockValue).prod) = 118662433481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_71
      · exact prime_oneHundredSixtyNineFK_79
      · exact prime_oneHundredSixtyNineFK_263
      · exact prime_oneHundredSixtyNineFK_2011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 118662433481) ^ 59331216740 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 118662433481) ^ 23732486696 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 118662433481) ^ 1671301880 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 118662433481) ^ 1502056120 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 118662433481) ^ 451187960 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 118662433481) ^ 59006680 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_119452937729 : Nat.Prime 119452937729 := by
  apply lucas_primality 119452937729 (3 : ZMod 119452937729)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (43, 1), (5425733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (43, 1), (5425733, 1)] : List FactorBlock).map factorBlockValue).prod) = 119452937729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_43
      · exact prime_oneHundredSixtyNineFK_5425733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 119452937729) ^ 59726468864 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 119452937729) ^ 2777975296 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 119452937729) ^ 22016 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_125936620919 : Nat.Prime 125936620919 := by
  apply lucas_primality 125936620919 (7 : ZMod 125936620919)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (79, 1), (18536447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (79, 1), (18536447, 1)] : List FactorBlock).map factorBlockValue).prod) = 125936620919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_43
      · exact prime_oneHundredSixtyNineFK_79
      · exact prime_oneHundredSixtyNineFK_18536447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 125936620919) ^ 62968310459 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 125936620919) ^ 2928758626 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 125936620919) ^ 1594134442 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 125936620919) ^ 6794 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_133432513219 : Nat.Prime 133432513219 := by
  apply lucas_primality 133432513219 (2 : ZMod 133432513219)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (691, 1), (1191979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (691, 1), (1191979, 1)] : List FactorBlock).map factorBlockValue).prod) = 133432513219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_691
      · exact prime_oneHundredSixtyNineFK_1191979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 133432513219) ^ 66716256609 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 133432513219) ^ 44477504406 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 133432513219) ^ 193100598 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 133432513219) ^ 111942 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_151056467951 : Nat.Prime 151056467951 := by
  apply lucas_primality 151056467951 (7 : ZMod 151056467951)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (103, 1), (29331353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (103, 1), (29331353, 1)] : List FactorBlock).map factorBlockValue).prod) = 151056467951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_103
      · exact prime_oneHundredSixtyNineFK_29331353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 151056467951) ^ 75528233975 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 151056467951) ^ 30211293590 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 151056467951) ^ 1466567650 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 151056467951) ^ 5150 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_182492735329 : Nat.Prime 182492735329 := by
  apply lucas_primality 182492735329 (13 : ZMod 182492735329)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (17, 2), (2192579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (17, 2), (2192579, 1)] : List FactorBlock).map factorBlockValue).prod) = 182492735329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_17
      · exact prime_oneHundredSixtyNineFK_2192579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 182492735329) ^ 91246367664 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (13 : ZMod 182492735329) ^ 60830911776 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (13 : ZMod 182492735329) ^ 10734866784 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (13 : ZMod 182492735329) ^ 83232 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_200465325763 : Nat.Prime 200465325763 := by
  apply lucas_primality 200465325763 (2 : ZMod 200465325763)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (17, 1), (151180487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (17, 1), (151180487, 1)] : List FactorBlock).map factorBlockValue).prod) = 200465325763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_13
      · exact prime_oneHundredSixtyNineFK_17
      · exact prime_oneHundredSixtyNineFK_151180487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 200465325763) ^ 100232662881 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 200465325763) ^ 66821775254 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 200465325763) ^ 15420409674 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 200465325763) ^ 11792077986 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 200465325763) ^ 1326 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_264756139831 : Nat.Prime 264756139831 := by
  apply lucas_primality 264756139831 (3 : ZMod 264756139831)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (13, 1), (83, 1), (389479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (13, 1), (83, 1), (389479, 1)] : List FactorBlock).map factorBlockValue).prod) = 264756139831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_13
      · exact prime_oneHundredSixtyNineFK_83
      · exact prime_oneHundredSixtyNineFK_389479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 264756139831) ^ 132378069915 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 264756139831) ^ 88252046610 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 264756139831) ^ 52951227966 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 264756139831) ^ 37822305690 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 264756139831) ^ 20365856910 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 264756139831) ^ 3189833010 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 264756139831) ^ 679770 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_297039925097 : Nat.Prime 297039925097 := by
  apply lucas_primality 297039925097 (3 : ZMod 297039925097)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (127, 1), (2251, 1), (5647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (127, 1), (2251, 1), (5647, 1)] : List FactorBlock).map factorBlockValue).prod) = 297039925097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_23
      · exact prime_oneHundredSixtyNineFK_127
      · exact prime_oneHundredSixtyNineFK_2251
      · exact prime_oneHundredSixtyNineFK_5647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 297039925097) ^ 148519962548 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 297039925097) ^ 12914779352 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 297039925097) ^ 2338897048 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 297039925097) ^ 131959096 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 297039925097) ^ 52601368 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_312756700759 : Nat.Prime 312756700759 := by
  apply lucas_primality 312756700759 (3 : ZMod 312756700759)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (15401, 1), (3384593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (15401, 1), (3384593, 1)] : List FactorBlock).map factorBlockValue).prod) = 312756700759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_15401
      · exact prime_oneHundredSixtyNineFK_3384593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 312756700759) ^ 156378350379 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 312756700759) ^ 104252233586 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 312756700759) ^ 20307558 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 312756700759) ^ 92406 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_325319568059 : Nat.Prime 325319568059 := by
  apply lucas_primality 325319568059 (2 : ZMod 325319568059)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (7072164523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (7072164523, 1)] : List FactorBlock).map factorBlockValue).prod) = 325319568059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_23
      · exact prime_oneHundredSixtyNineFK_7072164523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 325319568059) ^ 162659784029 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 325319568059) ^ 14144329046 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 325319568059) ^ 46 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_375192022091 : Nat.Prime 375192022091 := by
  apply lucas_primality 375192022091 (6 : ZMod 375192022091)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37519202209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37519202209, 1)] : List FactorBlock).map factorBlockValue).prod) = 375192022091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_37519202209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 375192022091) ^ 187596011045 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 375192022091) ^ 75038404418 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 375192022091) ^ 10 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_385238749183 : Nat.Prime 385238749183 := by
  apply lucas_primality 385238749183 (3 : ZMod 385238749183)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (23, 1), (37, 1), (191, 1), (56431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (23, 1), (37, 1), (191, 1), (56431, 1)] : List FactorBlock).map factorBlockValue).prod) = 385238749183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_23
      · exact prime_oneHundredSixtyNineFK_37
      · exact prime_oneHundredSixtyNineFK_191
      · exact prime_oneHundredSixtyNineFK_56431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 385238749183) ^ 192619374591 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 385238749183) ^ 128412916394 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 385238749183) ^ 55034107026 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 385238749183) ^ 16749510834 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 385238749183) ^ 10411858086 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 385238749183) ^ 2016956802 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 385238749183) ^ 6826722 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_398079114803 : Nat.Prime 398079114803 := by
  apply lucas_primality 398079114803 (2 : ZMod 398079114803)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (1609, 1), (6510731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (1609, 1), (6510731, 1)] : List FactorBlock).map factorBlockValue).prod) = 398079114803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_19
      · exact prime_oneHundredSixtyNineFK_1609
      · exact prime_oneHundredSixtyNineFK_6510731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 398079114803) ^ 199039557401 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 398079114803) ^ 20951532358 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 398079114803) ^ 247407778 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 398079114803) ^ 61142 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_431434771973 : Nat.Prime 431434771973 := by
  apply lucas_primality 431434771973 (2 : ZMod 431434771973)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (30133, 1), (155627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (30133, 1), (155627, 1)] : List FactorBlock).map factorBlockValue).prod) = 431434771973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_23
      · exact prime_oneHundredSixtyNineFK_30133
      · exact prime_oneHundredSixtyNineFK_155627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 431434771973) ^ 215717385986 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 431434771973) ^ 18758033564 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 431434771973) ^ 14317684 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 431434771973) ^ 2772236 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_498834621647 : Nat.Prime 498834621647 := by
  apply lucas_primality 498834621647 (10 : ZMod 498834621647)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (14671606519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (14671606519, 1)] : List FactorBlock).map factorBlockValue).prod) = 498834621647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_17
      · exact prime_oneHundredSixtyNineFK_14671606519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 498834621647) ^ 249417310823 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (10 : ZMod 498834621647) ^ 29343213038 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (10 : ZMod 498834621647) ^ 34 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_541095641077 : Nat.Prime 541095641077 := by
  apply lucas_primality 541095641077 (2 : ZMod 541095641077)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2663, 1), (16932521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2663, 1), (16932521, 1)] : List FactorBlock).map factorBlockValue).prod) = 541095641077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_2663
      · exact prime_oneHundredSixtyNineFK_16932521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 541095641077) ^ 270547820538 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 541095641077) ^ 180365213692 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 541095641077) ^ 203190252 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 541095641077) ^ 31956 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_563802335893 : Nat.Prime 563802335893 := by
  apply lucas_primality 563802335893 (5 : ZMod 563802335893)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5220391999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5220391999, 1)] : List FactorBlock).map factorBlockValue).prod) = 563802335893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_5220391999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 563802335893) ^ 281901167946 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 563802335893) ^ 187934111964 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 563802335893) ^ 108 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_577353822359 : Nat.Prime 577353822359 := by
  apply lucas_primality 577353822359 (13 : ZMod 577353822359)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (1301, 1), (11678341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (1301, 1), (11678341, 1)] : List FactorBlock).map factorBlockValue).prod) = 577353822359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_19
      · exact prime_oneHundredSixtyNineFK_1301
      · exact prime_oneHundredSixtyNineFK_11678341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 577353822359) ^ 288676911179 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (13 : ZMod 577353822359) ^ 30387043282 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (13 : ZMod 577353822359) ^ 443776958 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (13 : ZMod 577353822359) ^ 49438 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_693292230451 : Nat.Prime 693292230451 := by
  apply lucas_primality 693292230451 (7 : ZMod 693292230451)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (37, 1), (811, 1), (51343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (37, 1), (811, 1), (51343, 1)] : List FactorBlock).map factorBlockValue).prod) = 693292230451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_37
      · exact prime_oneHundredSixtyNineFK_811
      · exact prime_oneHundredSixtyNineFK_51343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 693292230451) ^ 346646115225 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 693292230451) ^ 231097410150 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 693292230451) ^ 138658446090 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 693292230451) ^ 18737627850 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 693292230451) ^ 854860950 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 693292230451) ^ 13503150 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_1187823636907 : Nat.Prime 1187823636907 := by
  apply lucas_primality 1187823636907 (2 : ZMod 1187823636907)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (5350556923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (5350556923, 1)] : List FactorBlock).map factorBlockValue).prod) = 1187823636907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_37
      · exact prime_oneHundredSixtyNineFK_5350556923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1187823636907) ^ 593911818453 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1187823636907) ^ 395941212302 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1187823636907) ^ 32103341538 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1187823636907) ^ 222 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_1501079606857 : Nat.Prime 1501079606857 := by
  apply lucas_primality 1501079606857 (5 : ZMod 1501079606857)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (20848327873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (20848327873, 1)] : List FactorBlock).map factorBlockValue).prod) = 1501079606857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_20848327873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1501079606857) ^ 750539803428 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1501079606857) ^ 500359868952 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1501079606857) ^ 72 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_1564506913061 : Nat.Prime 1564506913061 := by
  apply lucas_primality 1564506913061 (2 : ZMod 1564506913061)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (13, 1), (281, 1), (3059143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (13, 1), (281, 1), (3059143, 1)] : List FactorBlock).map factorBlockValue).prod) = 1564506913061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_13
      · exact prime_oneHundredSixtyNineFK_281
      · exact prime_oneHundredSixtyNineFK_3059143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1564506913061) ^ 782253456530 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1564506913061) ^ 312901382612 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1564506913061) ^ 223500987580 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1564506913061) ^ 120346685620 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1564506913061) ^ 5567640260 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1564506913061) ^ 511420 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_1919105882641 : Nat.Prime 1919105882641 := by
  apply lucas_primality 1919105882641 (11 : ZMod 1919105882641)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (73, 1), (36512669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (73, 1), (36512669, 1)] : List FactorBlock).map factorBlockValue).prod) = 1919105882641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_73
      · exact prime_oneHundredSixtyNineFK_36512669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1919105882641) ^ 959552941320 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (11 : ZMod 1919105882641) ^ 639701960880 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (11 : ZMod 1919105882641) ^ 383821176528 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (11 : ZMod 1919105882641) ^ 26289121680 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (11 : ZMod 1919105882641) ^ 52560 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_2007721290649 : Nat.Prime 2007721290649 := by
  apply lucas_primality 2007721290649 (19 : ZMod 2007721290649)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1171, 1), (71438987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1171, 1), (71438987, 1)] : List FactorBlock).map factorBlockValue).prod) = 2007721290649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_1171
      · exact prime_oneHundredSixtyNineFK_71438987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 2007721290649) ^ 1003860645324 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (19 : ZMod 2007721290649) ^ 669240430216 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (19 : ZMod 2007721290649) ^ 1714535688 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (19 : ZMod 2007721290649) ^ 28104 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_2162003974441 : Nat.Prime 2162003974441 := by
  apply lucas_primality 2162003974441 (14 : ZMod 2162003974441)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (59, 1), (16061, 1), (19013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (59, 1), (16061, 1), (19013, 1)] : List FactorBlock).map factorBlockValue).prod) = 2162003974441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_59
      · exact prime_oneHundredSixtyNineFK_16061
      · exact prime_oneHundredSixtyNineFK_19013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 2162003974441) ^ 1081001987220 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (14 : ZMod 2162003974441) ^ 720667991480 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (14 : ZMod 2162003974441) ^ 432400794888 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (14 : ZMod 2162003974441) ^ 36644135160 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (14 : ZMod 2162003974441) ^ 134612040 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (14 : ZMod 2162003974441) ^ 113711880 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_2189912823949 : Nat.Prime 2189912823949 := by
  apply lucas_primality 2189912823949 (2 : ZMod 2189912823949)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (182492735329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (182492735329, 1)] : List FactorBlock).map factorBlockValue).prod) = 2189912823949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_182492735329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2189912823949) ^ 1094956411974 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2189912823949) ^ 729970941316 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2189912823949) ^ 12 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_2676546708113 : Nat.Prime 2676546708113 := by
  apply lucas_primality 2676546708113 (3 : ZMod 2676546708113)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (107, 1), (28729, 1), (54419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (107, 1), (28729, 1), (54419, 1)] : List FactorBlock).map factorBlockValue).prod) = 2676546708113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_107
      · exact prime_oneHundredSixtyNineFK_28729
      · exact prime_oneHundredSixtyNineFK_54419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2676546708113) ^ 1338273354056 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2676546708113) ^ 25014455216 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2676546708113) ^ 93165328 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2676546708113) ^ 49184048 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_2768284592951 : Nat.Prime 2768284592951 := by
  apply lucas_primality 2768284592951 (11 : ZMod 2768284592951)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (55365691859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (55365691859, 1)] : List FactorBlock).map factorBlockValue).prod) = 2768284592951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_55365691859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 2768284592951) ^ 1384142296475 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (11 : ZMod 2768284592951) ^ 553656918590 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (11 : ZMod 2768284592951) ^ 50 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_3109531609057 : Nat.Prime 3109531609057 := by
  apply lucas_primality 3109531609057 (10 : ZMod 3109531609057)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (12757, 1), (2539073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (12757, 1), (2539073, 1)] : List FactorBlock).map factorBlockValue).prod) = 3109531609057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_12757
      · exact prime_oneHundredSixtyNineFK_2539073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 3109531609057) ^ 1554765804528 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (10 : ZMod 3109531609057) ^ 1036510536352 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (10 : ZMod 3109531609057) ^ 243751008 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (10 : ZMod 3109531609057) ^ 1224672 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_3512225810531 : Nat.Prime 3512225810531 := by
  apply lucas_primality 3512225810531 (2 : ZMod 3512225810531)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (257, 1), (283, 1), (409, 1), (11807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (257, 1), (283, 1), (409, 1), (11807, 1)] : List FactorBlock).map factorBlockValue).prod) = 3512225810531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_257
      · exact prime_oneHundredSixtyNineFK_283
      · exact prime_oneHundredSixtyNineFK_409
      · exact prime_oneHundredSixtyNineFK_11807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3512225810531) ^ 1756112905265 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3512225810531) ^ 702445162106 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3512225810531) ^ 13666248290 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3512225810531) ^ 12410691910 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3512225810531) ^ 8587349170 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3512225810531) ^ 297469790 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_3705752800063 : Nat.Prime 3705752800063 := by
  apply lucas_primality 3705752800063 (5 : ZMod 3705752800063)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (127, 1), (540354739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (127, 1), (540354739, 1)] : List FactorBlock).map factorBlockValue).prod) = 3705752800063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_127
      · exact prime_oneHundredSixtyNineFK_540354739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3705752800063) ^ 1852876400031 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 3705752800063) ^ 1235250933354 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 3705752800063) ^ 29179155906 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 3705752800063) ^ 6858 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_4111222750693 : Nat.Prime 4111222750693 := by
  apply lucas_primality 4111222750693 (13 : ZMod 4111222750693)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (31, 1), (381092209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (31, 1), (381092209, 1)] : List FactorBlock).map factorBlockValue).prod) = 4111222750693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_29
      · exact prime_oneHundredSixtyNineFK_31
      · exact prime_oneHundredSixtyNineFK_381092209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 4111222750693) ^ 2055611375346 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (13 : ZMod 4111222750693) ^ 1370407583564 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (13 : ZMod 4111222750693) ^ 141766301748 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (13 : ZMod 4111222750693) ^ 132620088732 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (13 : ZMod 4111222750693) ^ 10788 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_4136964945977 : Nat.Prime 4136964945977 := by
  apply lucas_primality 4136964945977 (3 : ZMod 4136964945977)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1231, 1), (420081737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1231, 1), (420081737, 1)] : List FactorBlock).map factorBlockValue).prod) = 4136964945977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_1231
      · exact prime_oneHundredSixtyNineFK_420081737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4136964945977) ^ 2068482472988 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 4136964945977) ^ 3360653896 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 4136964945977) ^ 9848 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_4686675374681 : Nat.Prime 4686675374681 := by
  apply lucas_primality 4686675374681 (3 : ZMod 4686675374681)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (41, 1), (439, 1), (500741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (41, 1), (439, 1), (500741, 1)] : List FactorBlock).map factorBlockValue).prod) = 4686675374681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_13
      · exact prime_oneHundredSixtyNineFK_41
      · exact prime_oneHundredSixtyNineFK_439
      · exact prime_oneHundredSixtyNineFK_500741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4686675374681) ^ 2343337687340 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 4686675374681) ^ 937335074936 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 4686675374681) ^ 360513490360 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 4686675374681) ^ 114309155480 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 4686675374681) ^ 10675798120 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 4686675374681) ^ 9359480 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_4741914110413 : Nat.Prime 4741914110413 := by
  apply lucas_primality 4741914110413 (5 : ZMod 4741914110413)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (61, 1), (647, 1), (10012403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (61, 1), (647, 1), (10012403, 1)] : List FactorBlock).map factorBlockValue).prod) = 4741914110413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_61
      · exact prime_oneHundredSixtyNineFK_647
      · exact prime_oneHundredSixtyNineFK_10012403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4741914110413) ^ 2370957055206 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 4741914110413) ^ 1580638036804 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 4741914110413) ^ 77736296892 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 4741914110413) ^ 7329078996 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 4741914110413) ^ 473604 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_4828411988963 : Nat.Prime 4828411988963 := by
  apply lucas_primality 4828411988963 (2 : ZMod 4828411988963)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (211, 1), (15679, 1), (729749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (211, 1), (15679, 1), (729749, 1)] : List FactorBlock).map factorBlockValue).prod) = 4828411988963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_211
      · exact prime_oneHundredSixtyNineFK_15679
      · exact prime_oneHundredSixtyNineFK_729749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4828411988963) ^ 2414205994481 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4828411988963) ^ 22883469142 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4828411988963) ^ 307954078 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4828411988963) ^ 6616538 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_5029733657089 : Nat.Prime 5029733657089 := by
  apply lucas_primality 5029733657089 (13 : ZMod 5029733657089)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 6), (7, 1), (73, 1), (26371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 6), (7, 1), (73, 1), (26371, 1)] : List FactorBlock).map factorBlockValue).prod) = 5029733657089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_73
      · exact prime_oneHundredSixtyNineFK_26371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 5029733657089) ^ 2514866828544 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (13 : ZMod 5029733657089) ^ 1676577885696 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (13 : ZMod 5029733657089) ^ 718533379584 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (13 : ZMod 5029733657089) ^ 68900461056 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (13 : ZMod 5029733657089) ^ 190729728 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_5612932028239 : Nat.Prime 5612932028239 := by
  apply lucas_primality 5612932028239 (6 : ZMod 5612932028239)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (101, 1), (3889, 1), (2381657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (101, 1), (3889, 1), (2381657, 1)] : List FactorBlock).map factorBlockValue).prod) = 5612932028239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_101
      · exact prime_oneHundredSixtyNineFK_3889
      · exact prime_oneHundredSixtyNineFK_2381657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 5612932028239) ^ 2806466014119 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 5612932028239) ^ 1870977342746 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 5612932028239) ^ 55573584438 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 5612932028239) ^ 1443284142 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 5612932028239) ^ 2356734 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_5801927572277 : Nat.Prime 5801927572277 := by
  apply lucas_primality 5801927572277 (2 : ZMod 5801927572277)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (15583, 1), (8461913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (15583, 1), (8461913, 1)] : List FactorBlock).map factorBlockValue).prod) = 5801927572277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_11
      · exact prime_oneHundredSixtyNineFK_15583
      · exact prime_oneHundredSixtyNineFK_8461913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5801927572277) ^ 2900963786138 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5801927572277) ^ 527447961116 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5801927572277) ^ 372324172 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5801927572277) ^ 685652 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_6344875045567 : Nat.Prime 6344875045567 := by
  apply lucas_primality 6344875045567 (6 : ZMod 6344875045567)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (39165895343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (39165895343, 1)] : List FactorBlock).map factorBlockValue).prod) = 6344875045567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_39165895343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 6344875045567) ^ 3172437522783 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 6344875045567) ^ 2114958348522 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 6344875045567) ^ 162 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_7506160818217 : Nat.Prime 7506160818217 := by
  apply lucas_primality 7506160818217 (5 : ZMod 7506160818217)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (312756700759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (312756700759, 1)] : List FactorBlock).map factorBlockValue).prod) = 7506160818217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_312756700759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 7506160818217) ^ 3753080409108 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 7506160818217) ^ 2502053606072 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 7506160818217) ^ 24 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_8257447839607 : Nat.Prime 8257447839607 := by
  apply lucas_primality 8257447839607 (7 : ZMod 8257447839607)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (19, 1), (21859, 1), (473383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (19, 1), (21859, 1), (473383, 1)] : List FactorBlock).map factorBlockValue).prod) = 8257447839607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_19
      · exact prime_oneHundredSixtyNineFK_21859
      · exact prime_oneHundredSixtyNineFK_473383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 8257447839607) ^ 4128723919803 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 8257447839607) ^ 2752482613202 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 8257447839607) ^ 1179635405658 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 8257447839607) ^ 434602517874 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 8257447839607) ^ 377759634 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 8257447839607) ^ 17443482 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_8511209226703 : Nat.Prime 8511209226703 := by
  apply lucas_primality 8511209226703 (5 : ZMod 8511209226703)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (13, 1), (23, 1), (53, 1), (743, 1), (5737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (13, 1), (23, 1), (53, 1), (743, 1), (5737, 1)] : List FactorBlock).map factorBlockValue).prod) = 8511209226703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_13
      · exact prime_oneHundredSixtyNineFK_23
      · exact prime_oneHundredSixtyNineFK_53
      · exact prime_oneHundredSixtyNineFK_743
      · exact prime_oneHundredSixtyNineFK_5737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 8511209226703) ^ 4255604613351 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 8511209226703) ^ 2837069742234 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 8511209226703) ^ 1215887032386 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 8511209226703) ^ 654708402054 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 8511209226703) ^ 370052575074 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 8511209226703) ^ 160588853334 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 8511209226703) ^ 11455194114 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 8511209226703) ^ 1483564446 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_8770715472553 : Nat.Prime 8770715472553 := by
  apply lucas_primality 8770715472553 (10 : ZMod 8770715472553)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (33222407093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (33222407093, 1)] : List FactorBlock).map factorBlockValue).prod) = 8770715472553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_11
      · exact prime_oneHundredSixtyNineFK_33222407093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 8770715472553) ^ 4385357736276 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (10 : ZMod 8770715472553) ^ 2923571824184 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (10 : ZMod 8770715472553) ^ 797337770232 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (10 : ZMod 8770715472553) ^ 264 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_9625329027931 : Nat.Prime 9625329027931 := by
  apply lucas_primality 9625329027931 (10 : ZMod 9625329027931)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (1109, 1), (3757267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (1109, 1), (3757267, 1)] : List FactorBlock).map factorBlockValue).prod) = 9625329027931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_11
      · exact prime_oneHundredSixtyNineFK_1109
      · exact prime_oneHundredSixtyNineFK_3757267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 9625329027931) ^ 4812664513965 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (10 : ZMod 9625329027931) ^ 3208443009310 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (10 : ZMod 9625329027931) ^ 1925065805586 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (10 : ZMod 9625329027931) ^ 1375047003990 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (10 : ZMod 9625329027931) ^ 875029911630 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (10 : ZMod 9625329027931) ^ 8679286770 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (10 : ZMod 9625329027931) ^ 2561790 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_9927557170763 : Nat.Prime 9927557170763 := by
  apply lucas_primality 9927557170763 (5 : ZMod 9927557170763)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (31, 1), (67, 1), (1319, 1), (23531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (31, 1), (67, 1), (1319, 1), (23531, 1)] : List FactorBlock).map factorBlockValue).prod) = 9927557170763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_11
      · exact prime_oneHundredSixtyNineFK_31
      · exact prime_oneHundredSixtyNineFK_67
      · exact prime_oneHundredSixtyNineFK_1319
      · exact prime_oneHundredSixtyNineFK_23531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 9927557170763) ^ 4963778585381 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 9927557170763) ^ 1418222452966 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 9927557170763) ^ 902505197342 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 9927557170763) ^ 320243779702 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 9927557170763) ^ 148172495086 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 9927557170763) ^ 7526578598 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 9927557170763) ^ 421892702 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_15245273347631 : Nat.Prime 15245273347631 := by
  apply lucas_primality 15245273347631 (13 : ZMod 15245273347631)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (77351, 1), (1037327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (77351, 1), (1037327, 1)] : List FactorBlock).map factorBlockValue).prod) = 15245273347631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_19
      · exact prime_oneHundredSixtyNineFK_77351
      · exact prime_oneHundredSixtyNineFK_1037327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 15245273347631) ^ 7622636673815 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (13 : ZMod 15245273347631) ^ 3049054669526 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (13 : ZMod 15245273347631) ^ 802382807770 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (13 : ZMod 15245273347631) ^ 197092130 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (13 : ZMod 15245273347631) ^ 14696690 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_18669323107343 : Nat.Prime 18669323107343 := by
  apply lucas_primality 18669323107343 (5 : ZMod 18669323107343)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (1753, 1), (280261253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (1753, 1), (280261253, 1)] : List FactorBlock).map factorBlockValue).prod) = 18669323107343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_19
      · exact prime_oneHundredSixtyNineFK_1753
      · exact prime_oneHundredSixtyNineFK_280261253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 18669323107343) ^ 9334661553671 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 18669323107343) ^ 982595953018 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 18669323107343) ^ 10649927614 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 18669323107343) ^ 66614 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_19078341164711 : Nat.Prime 19078341164711 := by
  apply lucas_primality 19078341164711 (11 : ZMod 19078341164711)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (112225536263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (112225536263, 1)] : List FactorBlock).map factorBlockValue).prod) = 19078341164711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_17
      · exact prime_oneHundredSixtyNineFK_112225536263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 19078341164711) ^ 9539170582355 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (11 : ZMod 19078341164711) ^ 3815668232942 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (11 : ZMod 19078341164711) ^ 1122255362630 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (11 : ZMod 19078341164711) ^ 170 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_21025232975533 : Nat.Prime 21025232975533 := by
  apply lucas_primality 21025232975533 (2 : ZMod 21025232975533)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (67, 1), (137, 1), (190881659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (67, 1), (137, 1), (190881659, 1)] : List FactorBlock).map factorBlockValue).prod) = 21025232975533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_67
      · exact prime_oneHundredSixtyNineFK_137
      · exact prime_oneHundredSixtyNineFK_190881659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 21025232975533) ^ 10512616487766 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 21025232975533) ^ 7008410991844 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 21025232975533) ^ 313809447396 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 21025232975533) ^ 153468853836 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 21025232975533) ^ 110148 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_30490546695263 : Nat.Prime 30490546695263 := by
  apply lucas_primality 30490546695263 (5 : ZMod 30490546695263)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (15245273347631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (15245273347631, 1)] : List FactorBlock).map factorBlockValue).prod) = 30490546695263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_15245273347631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 30490546695263) ^ 15245273347631 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 30490546695263) ^ 2 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_33312673606897 : Nat.Prime 33312673606897 := by
  apply lucas_primality 33312673606897 (7 : ZMod 33312673606897)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (31, 1), (151, 2), (327289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (31, 1), (151, 2), (327289, 1)] : List FactorBlock).map factorBlockValue).prod) = 33312673606897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_31
      · exact prime_oneHundredSixtyNineFK_151
      · exact prime_oneHundredSixtyNineFK_327289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 33312673606897) ^ 16656336803448 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 33312673606897) ^ 11104224535632 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 33312673606897) ^ 1074602374416 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 33312673606897) ^ 220613732496 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 33312673606897) ^ 101783664 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_34044836906813 : Nat.Prime 34044836906813 := by
  apply lucas_primality 34044836906813 (2 : ZMod 34044836906813)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (8511209226703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (8511209226703, 1)] : List FactorBlock).map factorBlockValue).prod) = 34044836906813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_8511209226703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 34044836906813) ^ 17022418453406 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 34044836906813) ^ 4 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_49334673008317 : Nat.Prime 49334673008317 := by
  apply lucas_primality 49334673008317 (2 : ZMod 49334673008317)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (4111222750693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (4111222750693, 1)] : List FactorBlock).map factorBlockValue).prod) = 49334673008317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_4111222750693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 49334673008317) ^ 24667336504158 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 49334673008317) ^ 16444891002772 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 49334673008317) ^ 12 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_50437601740481 : Nat.Prime 50437601740481 := by
  apply lucas_primality 50437601740481 (6 : ZMod 50437601740481)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (17, 1), (19, 1), (251, 1), (1944143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (17, 1), (19, 1), (251, 1), (1944143, 1)] : List FactorBlock).map factorBlockValue).prod) = 50437601740481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_17
      · exact prime_oneHundredSixtyNineFK_19
      · exact prime_oneHundredSixtyNineFK_251
      · exact prime_oneHundredSixtyNineFK_1944143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 50437601740481) ^ 25218800870240 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 50437601740481) ^ 10087520348096 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 50437601740481) ^ 2966917749440 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 50437601740481) ^ 2654610617920 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 50437601740481) ^ 200946620480 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 50437601740481) ^ 25943360 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_56916859996319 : Nat.Prime 56916859996319 := by
  apply lucas_primality 56916859996319 (7 : ZMod 56916859996319)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (37, 1), (56269, 1), (1952729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (37, 1), (56269, 1), (1952729, 1)] : List FactorBlock).map factorBlockValue).prod) = 56916859996319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_37
      · exact prime_oneHundredSixtyNineFK_56269
      · exact prime_oneHundredSixtyNineFK_1952729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 56916859996319) ^ 28458429998159 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 56916859996319) ^ 8130979999474 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 56916859996319) ^ 1538293513414 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 56916859996319) ^ 1011513622 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 56916859996319) ^ 29147342 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_60981093390527 : Nat.Prime 60981093390527 := by
  apply lucas_primality 60981093390527 (5 : ZMod 60981093390527)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (30490546695263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (30490546695263, 1)] : List FactorBlock).map factorBlockValue).prod) = 60981093390527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_30490546695263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 60981093390527) ^ 30490546695263 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 60981093390527) ^ 2 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_68291425731899 : Nat.Prime 68291425731899 := by
  apply lucas_primality 68291425731899 (2 : ZMod 68291425731899)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (31, 1), (9829, 1), (4872337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (31, 1), (9829, 1), (4872337, 1)] : List FactorBlock).map factorBlockValue).prod) = 68291425731899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_23
      · exact prime_oneHundredSixtyNineFK_31
      · exact prime_oneHundredSixtyNineFK_9829
      · exact prime_oneHundredSixtyNineFK_4872337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 68291425731899) ^ 34145712865949 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 68291425731899) ^ 2969192423126 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 68291425731899) ^ 2202949217158 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 68291425731899) ^ 6947952562 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 68291425731899) ^ 14016154 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_105481689672703 : Nat.Prime 105481689672703 := by
  apply lucas_primality 105481689672703 (6 : ZMod 105481689672703)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (32887, 1), (76366613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (32887, 1), (76366613, 1)] : List FactorBlock).map factorBlockValue).prod) = 105481689672703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_32887
      · exact prime_oneHundredSixtyNineFK_76366613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 105481689672703) ^ 52740844836351 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 105481689672703) ^ 35160563224234 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 105481689672703) ^ 15068812810386 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 105481689672703) ^ 3207397746 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 105481689672703) ^ 1381254 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_115342509540833 : Nat.Prime 115342509540833 := by
  apply lucas_primality 115342509540833 (3 : ZMod 115342509540833)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (2777, 1), (185423809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (2777, 1), (185423809, 1)] : List FactorBlock).map factorBlockValue).prod) = 115342509540833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_2777
      · exact prime_oneHundredSixtyNineFK_185423809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 115342509540833) ^ 57671254770416 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 115342509540833) ^ 16477501362976 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 115342509540833) ^ 41534933216 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 115342509540833) ^ 622048 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_120061447069121 : Nat.Prime 120061447069121 := by
  apply lucas_primality 120061447069121 (3 : ZMod 120061447069121)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (375192022091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (375192022091, 1)] : List FactorBlock).map factorBlockValue).prod) = 120061447069121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_375192022091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 120061447069121) ^ 60030723534560 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 120061447069121) ^ 24012289413824 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 120061447069121) ^ 320 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_188538805577147 : Nat.Prime 188538805577147 := by
  apply lucas_primality 188538805577147 (2 : ZMod 188538805577147)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (46337, 1), (2034430429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (46337, 1), (2034430429, 1)] : List FactorBlock).map factorBlockValue).prod) = 188538805577147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_46337
      · exact prime_oneHundredSixtyNineFK_2034430429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 188538805577147) ^ 94269402788573 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 188538805577147) ^ 4068860858 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 188538805577147) ^ 92674 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_222755298876899 : Nat.Prime 222755298876899 := by
  apply lucas_primality 222755298876899 (2 : ZMod 222755298876899)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (279883, 1), (397943603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (279883, 1), (397943603, 1)] : List FactorBlock).map factorBlockValue).prod) = 222755298876899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_279883
      · exact prime_oneHundredSixtyNineFK_397943603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 222755298876899) ^ 111377649438449 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 222755298876899) ^ 795887206 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 222755298876899) ^ 559766 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_234010206150683 : Nat.Prime 234010206150683 := by
  apply lucas_primality 234010206150683 (2 : ZMod 234010206150683)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (267373, 1), (33662309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (267373, 1), (33662309, 1)] : List FactorBlock).map factorBlockValue).prod) = 234010206150683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_13
      · exact prime_oneHundredSixtyNineFK_267373
      · exact prime_oneHundredSixtyNineFK_33662309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 234010206150683) ^ 117005103075341 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 234010206150683) ^ 18000785088514 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 234010206150683) ^ 875220034 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 234010206150683) ^ 6951698 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_267494201311979 : Nat.Prime 267494201311979 := by
  apply lucas_primality 267494201311979 (6 : ZMod 267494201311979)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (97, 1), (107, 1), (12886318591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (97, 1), (107, 1), (12886318591, 1)] : List FactorBlock).map factorBlockValue).prod) = 267494201311979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_97
      · exact prime_oneHundredSixtyNineFK_107
      · exact prime_oneHundredSixtyNineFK_12886318591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 267494201311979) ^ 133747100655989 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 267494201311979) ^ 2757672178474 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 267494201311979) ^ 2499945806654 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 267494201311979) ^ 20758 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_273039686434483 : Nat.Prime 273039686434483 := by
  apply lucas_primality 273039686434483 (3 : ZMod 273039686434483)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (4136964945977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (4136964945977, 1)] : List FactorBlock).map factorBlockValue).prod) = 273039686434483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_11
      · exact prime_oneHundredSixtyNineFK_4136964945977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 273039686434483) ^ 136519843217241 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 273039686434483) ^ 91013228811494 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 273039686434483) ^ 24821789675862 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 273039686434483) ^ 66 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_448063754576233 : Nat.Prime 448063754576233 := by
  apply lucas_primality 448063754576233 (7 : ZMod 448063754576233)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (18669323107343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (18669323107343, 1)] : List FactorBlock).map factorBlockValue).prod) = 448063754576233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_18669323107343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 448063754576233) ^ 224031877288116 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 448063754576233) ^ 149354584858744 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 448063754576233) ^ 24 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_448768306116197 : Nat.Prime 448768306116197 := by
  apply lucas_primality 448768306116197 (3 : ZMod 448768306116197)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (761, 1), (13402470019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (761, 1), (13402470019, 1)] : List FactorBlock).map factorBlockValue).prod) = 448768306116197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_11
      · exact prime_oneHundredSixtyNineFK_761
      · exact prime_oneHundredSixtyNineFK_13402470019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 448768306116197) ^ 224384153058098 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 448768306116197) ^ 40797118737836 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 448768306116197) ^ 589708680836 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 448768306116197) ^ 33484 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_636082306604681 : Nat.Prime 636082306604681 := by
  apply lucas_primality 636082306604681 (3 : ZMod 636082306604681)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (6803, 1), (179808203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (6803, 1), (179808203, 1)] : List FactorBlock).map factorBlockValue).prod) = 636082306604681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_13
      · exact prime_oneHundredSixtyNineFK_6803
      · exact prime_oneHundredSixtyNineFK_179808203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 636082306604681) ^ 318041153302340 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 636082306604681) ^ 127216461320936 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 636082306604681) ^ 48929408200360 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 636082306604681) ^ 93500265560 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 636082306604681) ^ 3537560 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_673962600156371 : Nat.Prime 673962600156371 := by
  apply lucas_primality 673962600156371 (2 : ZMod 673962600156371)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (8831, 1), (1090254461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (8831, 1), (1090254461, 1)] : List FactorBlock).map factorBlockValue).prod) = 673962600156371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_8831
      · exact prime_oneHundredSixtyNineFK_1090254461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 673962600156371) ^ 336981300078185 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 673962600156371) ^ 134792520031274 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 673962600156371) ^ 96280371450910 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 673962600156371) ^ 76317812270 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 673962600156371) ^ 618170 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_853822175964071 : Nat.Prime 853822175964071 := by
  apply lucas_primality 853822175964071 (13 : ZMod 853822175964071)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (61, 1), (719, 1), (1946743373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (61, 1), (719, 1), (1946743373, 1)] : List FactorBlock).map factorBlockValue).prod) = 853822175964071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_61
      · exact prime_oneHundredSixtyNineFK_719
      · exact prime_oneHundredSixtyNineFK_1946743373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 853822175964071) ^ 426911087982035 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (13 : ZMod 853822175964071) ^ 170764435192814 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (13 : ZMod 853822175964071) ^ 13997084851870 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (13 : ZMod 853822175964071) ^ 1187513457530 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (13 : ZMod 853822175964071) ^ 438590 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_1563597756299587 : Nat.Prime 1563597756299587 := by
  apply lucas_primality 1563597756299587 (3 : ZMod 1563597756299587)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (17, 1), (2189912823949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (17, 1), (2189912823949, 1)] : List FactorBlock).map factorBlockValue).prod) = 1563597756299587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_17
      · exact prime_oneHundredSixtyNineFK_2189912823949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1563597756299587) ^ 781798878149793 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1563597756299587) ^ 521199252099862 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1563597756299587) ^ 223371108042798 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1563597756299587) ^ 91976338605858 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1563597756299587) ^ 714 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_1644715724703787 : Nat.Prime 1644715724703787 := by
  apply lucas_primality 1644715724703787 (3 : ZMod 1644715724703787)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (11813, 1), (1104994447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (11813, 1), (1104994447, 1)] : List FactorBlock).map factorBlockValue).prod) = 1644715724703787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_11813
      · exact prime_oneHundredSixtyNineFK_1104994447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1644715724703787) ^ 822357862351893 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1644715724703787) ^ 548238574901262 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1644715724703787) ^ 234959389243398 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1644715724703787) ^ 139229300322 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1644715724703787) ^ 1488438 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_1925613163622321 : Nat.Prime 1925613163622321 := by
  apply lucas_primality 1925613163622321 (6 : ZMod 1925613163622321)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (19, 1), (23, 1), (4919, 1), (11197493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (19, 1), (23, 1), (4919, 1), (11197493, 1)] : List FactorBlock).map factorBlockValue).prod) = 1925613163622321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_19
      · exact prime_oneHundredSixtyNineFK_23
      · exact prime_oneHundredSixtyNineFK_4919
      · exact prime_oneHundredSixtyNineFK_11197493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1925613163622321) ^ 962806581811160 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1925613163622321) ^ 385122632724464 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1925613163622321) ^ 101348061243280 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1925613163622321) ^ 83722311461840 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1925613163622321) ^ 391464355280 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1925613163622321) ^ 171968240 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_1953018132419141 : Nat.Prime 1953018132419141 := by
  apply lucas_primality 1953018132419141 (2 : ZMod 1953018132419141)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (36007, 1), (142736729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (36007, 1), (142736729, 1)] : List FactorBlock).map factorBlockValue).prod) = 1953018132419141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_19
      · exact prime_oneHundredSixtyNineFK_36007
      · exact prime_oneHundredSixtyNineFK_142736729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1953018132419141) ^ 976509066209570 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1953018132419141) ^ 390603626483828 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1953018132419141) ^ 102790428022060 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1953018132419141) ^ 54239957020 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1953018132419141) ^ 13682660 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_2343570757683731 : Nat.Prime 2343570757683731 := by
  apply lucas_primality 2343570757683731 (2 : ZMod 2343570757683731)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (41, 1), (97, 1), (58928105549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (41, 1), (97, 1), (58928105549, 1)] : List FactorBlock).map factorBlockValue).prod) = 2343570757683731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_41
      · exact prime_oneHundredSixtyNineFK_97
      · exact prime_oneHundredSixtyNineFK_58928105549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2343570757683731) ^ 1171785378841865 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2343570757683731) ^ 468714151536746 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2343570757683731) ^ 57160262382530 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2343570757683731) ^ 24160523275090 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2343570757683731) ^ 39770 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_2723838083453899 : Nat.Prime 2723838083453899 := by
  apply lucas_primality 2723838083453899 (2 : ZMod 2723838083453899)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (37, 1), (149, 1), (179, 1), (1759, 1), (29059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (37, 1), (149, 1), (179, 1), (1759, 1), (29059, 1)] : List FactorBlock).map factorBlockValue).prod) = 2723838083453899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_37
      · exact prime_oneHundredSixtyNineFK_149
      · exact prime_oneHundredSixtyNineFK_179
      · exact prime_oneHundredSixtyNineFK_1759
      · exact prime_oneHundredSixtyNineFK_29059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2723838083453899) ^ 1361919041726949 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2723838083453899) ^ 907946027817966 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2723838083453899) ^ 73617245498754 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2723838083453899) ^ 18280792506402 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2723838083453899) ^ 15216972533262 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2723838083453899) ^ 1548515112822 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2723838083453899) ^ 93734749422 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_3167671651896989 : Nat.Prime 3167671651896989 := by
  apply lucas_primality 3167671651896989 (2 : ZMod 3167671651896989)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (823, 1), (750863, 1), (1281503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (823, 1), (750863, 1), (1281503, 1)] : List FactorBlock).map factorBlockValue).prod) = 3167671651896989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_823
      · exact prime_oneHundredSixtyNineFK_750863
      · exact prime_oneHundredSixtyNineFK_1281503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3167671651896989) ^ 1583835825948494 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3167671651896989) ^ 3848932748356 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3167671651896989) ^ 4218707876 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3167671651896989) ^ 2471840996 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_4804039943204891 : Nat.Prime 4804039943204891 := by
  apply lucas_primality 4804039943204891 (6 : ZMod 4804039943204891)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (47, 1), (1623977, 1), (6294031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (47, 1), (1623977, 1), (6294031, 1)] : List FactorBlock).map factorBlockValue).prod) = 4804039943204891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_47
      · exact prime_oneHundredSixtyNineFK_1623977
      · exact prime_oneHundredSixtyNineFK_6294031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 4804039943204891) ^ 2402019971602445 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 4804039943204891) ^ 960807988640978 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 4804039943204891) ^ 102213615812870 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 4804039943204891) ^ 2958194570 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 4804039943204891) ^ 763269190 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_5391700801250969 : Nat.Prime 5391700801250969 := by
  apply lucas_primality 5391700801250969 (3 : ZMod 5391700801250969)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (673962600156371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (673962600156371, 1)] : List FactorBlock).map factorBlockValue).prod) = 5391700801250969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_673962600156371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 5391700801250969) ^ 2695850400625484 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5391700801250969) ^ 8 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_5698723949233277 : Nat.Prime 5698723949233277 := by
  apply lucas_primality 5698723949233277 (2 : ZMod 5698723949233277)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (233, 1), (3989, 1), (117910999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (233, 1), (3989, 1), (117910999, 1)] : List FactorBlock).map factorBlockValue).prod) = 5698723949233277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_13
      · exact prime_oneHundredSixtyNineFK_233
      · exact prime_oneHundredSixtyNineFK_3989
      · exact prime_oneHundredSixtyNineFK_117910999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5698723949233277) ^ 2849361974616638 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5698723949233277) ^ 438363380710252 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5698723949233277) ^ 24458042700572 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5698723949233277) ^ 1428609663884 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5698723949233277) ^ 48330724 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_8217269742492379 : Nat.Prime 8217269742492379 := by
  apply lucas_primality 8217269742492379 (2 : ZMod 8217269742492379)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (367, 1), (1619, 1), (5333, 1), (48023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (367, 1), (1619, 1), (5333, 1), (48023, 1)] : List FactorBlock).map factorBlockValue).prod) = 8217269742492379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_367
      · exact prime_oneHundredSixtyNineFK_1619
      · exact prime_oneHundredSixtyNineFK_5333
      · exact prime_oneHundredSixtyNineFK_48023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8217269742492379) ^ 4108634871246189 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8217269742492379) ^ 2739089914164126 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8217269742492379) ^ 22390380769734 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8217269742492379) ^ 5075521768062 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8217269742492379) ^ 1540834378866 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8217269742492379) ^ 171111128886 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_8560070626452379 : Nat.Prime 8560070626452379 := by
  apply lucas_primality 8560070626452379 (2 : ZMod 8560070626452379)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (1093, 1), (118662433481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (1093, 1), (118662433481, 1)] : List FactorBlock).map factorBlockValue).prod) = 8560070626452379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_11
      · exact prime_oneHundredSixtyNineFK_1093
      · exact prime_oneHundredSixtyNineFK_118662433481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8560070626452379) ^ 4280035313226189 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8560070626452379) ^ 2853356875484126 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8560070626452379) ^ 778188238768398 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8560070626452379) ^ 7831720609746 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8560070626452379) ^ 72138 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_17053195632415487 : Nat.Prime 17053195632415487 := by
  apply lucas_primality 17053195632415487 (5 : ZMod 17053195632415487)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (448768306116197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (448768306116197, 1)] : List FactorBlock).map factorBlockValue).prod) = 17053195632415487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_19
      · exact prime_oneHundredSixtyNineFK_448768306116197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 17053195632415487) ^ 8526597816207743 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 17053195632415487) ^ 897536612232394 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 17053195632415487) ^ 38 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_18253829013077291 : Nat.Prime 18253829013077291 := by
  apply lucas_primality 18253829013077291 (7 : ZMod 18253829013077291)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37, 1), (49334673008317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37, 1), (49334673008317, 1)] : List FactorBlock).map factorBlockValue).prod) = 18253829013077291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_37
      · exact prime_oneHundredSixtyNineFK_49334673008317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 18253829013077291) ^ 9126914506538645 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 18253829013077291) ^ 3650765802615458 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 18253829013077291) ^ 493346730083170 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 18253829013077291) ^ 370 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_19225944268456169 : Nat.Prime 19225944268456169 := by
  apply lucas_primality 19225944268456169 (3 : ZMod 19225944268456169)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (21757, 1), (95737, 1), (1153769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (21757, 1), (95737, 1), (1153769, 1)] : List FactorBlock).map factorBlockValue).prod) = 19225944268456169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_21757
      · exact prime_oneHundredSixtyNineFK_95737
      · exact prime_oneHundredSixtyNineFK_1153769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 19225944268456169) ^ 9612972134228084 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 19225944268456169) ^ 883667062024 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 19225944268456169) ^ 200820417064 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 19225944268456169) ^ 16663599272 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_24734864410068361 : Nat.Prime 24734864410068361 := by
  apply lucas_primality 24734864410068361 (11 : ZMod 24734864410068361)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (241, 1), (343601, 1), (2489183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (241, 1), (343601, 1), (2489183, 1)] : List FactorBlock).map factorBlockValue).prod) = 24734864410068361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_241
      · exact prime_oneHundredSixtyNineFK_343601
      · exact prime_oneHundredSixtyNineFK_2489183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 24734864410068361) ^ 12367432205034180 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (11 : ZMod 24734864410068361) ^ 8244954803356120 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (11 : ZMod 24734864410068361) ^ 4946972882013672 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (11 : ZMod 24734864410068361) ^ 102634292157960 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (11 : ZMod 24734864410068361) ^ 71987172360 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (11 : ZMod 24734864410068361) ^ 9936940920 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_51758507535017051 : Nat.Prime 51758507535017051 := by
  apply lucas_primality 51758507535017051 (2 : ZMod 51758507535017051)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (523, 1), (467261, 1), (4235947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (523, 1), (467261, 1), (4235947, 1)] : List FactorBlock).map factorBlockValue).prod) = 51758507535017051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_523
      · exact prime_oneHundredSixtyNineFK_467261
      · exact prime_oneHundredSixtyNineFK_4235947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 51758507535017051) ^ 25879253767508525 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 51758507535017051) ^ 10351701507003410 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 51758507535017051) ^ 98964641558350 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 51758507535017051) ^ 110770014050 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 51758507535017051) ^ 12218875150 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_83289324010206373 : Nat.Prime 83289324010206373 := by
  apply lucas_primality 83289324010206373 (2 : ZMod 83289324010206373)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (31, 2), (59, 1), (103, 1), (24659, 1), (48197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (31, 2), (59, 1), (103, 1), (24659, 1), (48197, 1)] : List FactorBlock).map factorBlockValue).prod) = 83289324010206373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_31
      · exact prime_oneHundredSixtyNineFK_59
      · exact prime_oneHundredSixtyNineFK_103
      · exact prime_oneHundredSixtyNineFK_24659
      · exact prime_oneHundredSixtyNineFK_48197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 83289324010206373) ^ 41644662005103186 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 83289324010206373) ^ 27763108003402124 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 83289324010206373) ^ 2686752387426012 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 83289324010206373) ^ 1411683457800108 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 83289324010206373) ^ 808634213691324 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 83289324010206373) ^ 3377644024908 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 83289324010206373) ^ 1728101832276 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_84442982488096217 : Nat.Prime 84442982488096217 := by
  apply lucas_primality 84442982488096217 (3 : ZMod 84442982488096217)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (69877, 1), (151056467951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (69877, 1), (151056467951, 1)] : List FactorBlock).map factorBlockValue).prod) = 84442982488096217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_69877
      · exact prime_oneHundredSixtyNineFK_151056467951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 84442982488096217) ^ 42221491244048108 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 84442982488096217) ^ 1208451743608 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 84442982488096217) ^ 559016 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_121890955072991669 : Nat.Prime 121890955072991669 := by
  apply lucas_primality 121890955072991669 (2 : ZMod 121890955072991669)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1987, 1), (6551, 1), (2341024841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1987, 1), (6551, 1), (2341024841, 1)] : List FactorBlock).map factorBlockValue).prod) = 121890955072991669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_1987
      · exact prime_oneHundredSixtyNineFK_6551
      · exact prime_oneHundredSixtyNineFK_2341024841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 121890955072991669) ^ 60945477536495834 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 121890955072991669) ^ 61344214933564 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 121890955072991669) ^ 18606465436268 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 121890955072991669) ^ 52067348 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_177112743868002511 : Nat.Prime 177112743868002511 := by
  apply lucas_primality 177112743868002511 (6 : ZMod 177112743868002511)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (281, 1), (678593, 1), (10320283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (281, 1), (678593, 1), (10320283, 1)] : List FactorBlock).map factorBlockValue).prod) = 177112743868002511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_281
      · exact prime_oneHundredSixtyNineFK_678593
      · exact prime_oneHundredSixtyNineFK_10320283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 177112743868002511) ^ 88556371934001255 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 177112743868002511) ^ 59037581289334170 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 177112743868002511) ^ 35422548773600502 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 177112743868002511) ^ 630294462163710 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 177112743868002511) ^ 260999957070 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 177112743868002511) ^ 17161616970 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_226648136811482209 : Nat.Prime 226648136811482209 := by
  apply lucas_primality 226648136811482209 (7 : ZMod 226648136811482209)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 5), (1570501, 1), (18559133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 5), (1570501, 1), (18559133, 1)] : List FactorBlock).map factorBlockValue).prod) = 226648136811482209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_1570501
      · exact prime_oneHundredSixtyNineFK_18559133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 226648136811482209) ^ 113324068405741104 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 226648136811482209) ^ 75549378937160736 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 226648136811482209) ^ 144315818208 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 226648136811482209) ^ 12212215776 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_281089575032107711 : Nat.Prime 281089575032107711 := by
  apply lucas_primality 281089575032107711 (7 : ZMod 281089575032107711)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (17, 1), (1951, 1), (25681749661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (17, 1), (1951, 1), (25681749661, 1)] : List FactorBlock).map factorBlockValue).prod) = 281089575032107711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_11
      · exact prime_oneHundredSixtyNineFK_17
      · exact prime_oneHundredSixtyNineFK_1951
      · exact prime_oneHundredSixtyNineFK_25681749661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 281089575032107711) ^ 140544787516053855 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 281089575032107711) ^ 93696525010702570 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 281089575032107711) ^ 56217915006421542 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 281089575032107711) ^ 25553597730191610 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 281089575032107711) ^ 16534680884241630 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 281089575032107711) ^ 144074615598210 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 281089575032107711) ^ 10945110 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_346066996832211043 : Nat.Prime 346066996832211043 := by
  apply lucas_primality 346066996832211043 (3 : ZMod 346066996832211043)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19225944268456169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19225944268456169, 1)] : List FactorBlock).map factorBlockValue).prod) = 346066996832211043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_19225944268456169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 346066996832211043) ^ 173033498416105521 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 346066996832211043) ^ 115355665610737014 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 346066996832211043) ^ 18 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_394348780433911507 : Nat.Prime 394348780433911507 := by
  apply lucas_primality 394348780433911507 (3 : ZMod 394348780433911507)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (29, 1), (467, 1), (693292230451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (29, 1), (467, 1), (693292230451, 1)] : List FactorBlock).map factorBlockValue).prod) = 394348780433911507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_29
      · exact prime_oneHundredSixtyNineFK_467
      · exact prime_oneHundredSixtyNineFK_693292230451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 394348780433911507) ^ 197174390216955753 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 394348780433911507) ^ 131449593477970502 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 394348780433911507) ^ 56335540061987358 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 394348780433911507) ^ 13598233808065914 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 394348780433911507) ^ 844429936689318 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 394348780433911507) ^ 568806 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_527894619647632591 : Nat.Prime 527894619647632591 := by
  apply lucas_primality 527894619647632591 (3 : ZMod 527894619647632591)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (66463, 1), (264756139831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (66463, 1), (264756139831, 1)] : List FactorBlock).map factorBlockValue).prod) = 527894619647632591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_66463
      · exact prime_oneHundredSixtyNineFK_264756139831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 527894619647632591) ^ 263947309823816295 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 527894619647632591) ^ 175964873215877530 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 527894619647632591) ^ 105578923929526518 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 527894619647632591) ^ 7942684194930 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 527894619647632591) ^ 1993890 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_853398778419484457 : Nat.Prime 853398778419484457 := by
  apply lucas_primality 853398778419484457 (3 : ZMod 853398778419484457)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (6397, 1), (380447, 1), (43832023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (6397, 1), (380447, 1), (43832023, 1)] : List FactorBlock).map factorBlockValue).prod) = 853398778419484457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_6397
      · exact prime_oneHundredSixtyNineFK_380447
      · exact prime_oneHundredSixtyNineFK_43832023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 853398778419484457) ^ 426699389209742228 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 853398778419484457) ^ 133406093234248 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 853398778419484457) ^ 2243147609048 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 853398778419484457) ^ 19469755672 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_974378561702492509 : Nat.Prime 974378561702492509 := by
  apply lucas_primality 974378561702492509 (7 : ZMod 974378561702492509)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (43, 1), (229, 1), (55631, 1), (148226437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (43, 1), (229, 1), (55631, 1), (148226437, 1)] : List FactorBlock).map factorBlockValue).prod) = 974378561702492509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_43
      · exact prime_oneHundredSixtyNineFK_229
      · exact prime_oneHundredSixtyNineFK_55631
      · exact prime_oneHundredSixtyNineFK_148226437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 974378561702492509) ^ 487189280851246254 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 974378561702492509) ^ 324792853900830836 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 974378561702492509) ^ 22659966551220756 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 974378561702492509) ^ 4254928217041452 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 974378561702492509) ^ 17515028701668 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 974378561702492509) ^ 6573581484 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_1480372332234303967 : Nat.Prime 1480372332234303967 := by
  apply lucas_primality 1480372332234303967 (3 : ZMod 1480372332234303967)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (83, 1), (1487, 1), (5807, 1), (344253863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (83, 1), (1487, 1), (5807, 1), (344253863, 1)] : List FactorBlock).map factorBlockValue).prod) = 1480372332234303967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_83
      · exact prime_oneHundredSixtyNineFK_1487
      · exact prime_oneHundredSixtyNineFK_5807
      · exact prime_oneHundredSixtyNineFK_344253863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1480372332234303967) ^ 740186166117151983 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1480372332234303967) ^ 493457444078101322 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1480372332234303967) ^ 17835811231738602 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1480372332234303967) ^ 995542926855618 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1480372332234303967) ^ 254928936151938 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1480372332234303967) ^ 4300234482 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_1484091864604101661 : Nat.Prime 1484091864604101661 := by
  apply lucas_primality 1484091864604101661 (2 : ZMod 1484091864604101661)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (24734864410068361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (24734864410068361, 1)] : List FactorBlock).map factorBlockValue).prod) = 1484091864604101661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_24734864410068361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1484091864604101661) ^ 742045932302050830 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1484091864604101661) ^ 494697288201367220 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1484091864604101661) ^ 296818372920820332 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1484091864604101661) ^ 60 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_1510897560083794661 : Nat.Prime 1510897560083794661 := by
  apply lucas_primality 1510897560083794661 (2 : ZMod 1510897560083794661)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (347, 1), (220189, 1), (988735051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (347, 1), (220189, 1), (988735051, 1)] : List FactorBlock).map factorBlockValue).prod) = 1510897560083794661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_347
      · exact prime_oneHundredSixtyNineFK_220189
      · exact prime_oneHundredSixtyNineFK_988735051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1510897560083794661) ^ 755448780041897330 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1510897560083794661) ^ 302179512016758932 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1510897560083794661) ^ 4354171642892780 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1510897560083794661) ^ 6861821253940 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1510897560083794661) ^ 1528111660 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_2713953990196456409 : Nat.Prime 2713953990196456409 := by
  apply lucas_primality 2713953990196456409 (3 : ZMod 2713953990196456409)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1142083, 1), (297039925097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1142083, 1), (297039925097, 1)] : List FactorBlock).map factorBlockValue).prod) = 2713953990196456409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_1142083
      · exact prime_oneHundredSixtyNineFK_297039925097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2713953990196456409) ^ 1356976995098228204 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2713953990196456409) ^ 2376319400776 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2713953990196456409) ^ 9136664 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_2719311851389386293 : Nat.Prime 2719311851389386293 := by
  apply lucas_primality 2719311851389386293 (2 : ZMod 2719311851389386293)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (19, 1), (367, 1), (646339, 1), (11603143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (19, 1), (367, 1), (646339, 1), (11603143, 1)] : List FactorBlock).map factorBlockValue).prod) = 2719311851389386293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_13
      · exact prime_oneHundredSixtyNineFK_19
      · exact prime_oneHundredSixtyNineFK_367
      · exact prime_oneHundredSixtyNineFK_646339
      · exact prime_oneHundredSixtyNineFK_11603143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2719311851389386293) ^ 1359655925694693146 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2719311851389386293) ^ 209177834722260484 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2719311851389386293) ^ 143121676388915068 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2719311851389386293) ^ 7409569077355276 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2719311851389386293) ^ 4207253239228 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2719311851389386293) ^ 234359936044 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_2898035704870355603 : Nat.Prime 2898035704870355603 := by
  apply lucas_primality 2898035704870355603 (5 : ZMod 2898035704870355603)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (6257, 1), (28627, 1), (1155669637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (6257, 1), (28627, 1), (1155669637, 1)] : List FactorBlock).map factorBlockValue).prod) = 2898035704870355603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_6257
      · exact prime_oneHundredSixtyNineFK_28627
      · exact prime_oneHundredSixtyNineFK_1155669637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2898035704870355603) ^ 1449017852435177801 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 2898035704870355603) ^ 414005100695765086 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 2898035704870355603) ^ 463166965777586 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 2898035704870355603) ^ 101234348861926 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 2898035704870355603) ^ 2507667946 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_2927544154246713619 : Nat.Prime 2927544154246713619 := by
  apply lucas_primality 2927544154246713619 (3 : ZMod 2927544154246713619)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (8560070626452379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (8560070626452379, 1)] : List FactorBlock).map factorBlockValue).prod) = 2927544154246713619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_19
      · exact prime_oneHundredSixtyNineFK_8560070626452379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2927544154246713619) ^ 1463772077123356809 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2927544154246713619) ^ 975848051415571206 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2927544154246713619) ^ 154081271276142822 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2927544154246713619) ^ 342 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_3014995691311940443 : Nat.Prime 3014995691311940443 := by
  apply lucas_primality 3014995691311940443 (2 : ZMod 3014995691311940443)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (321187, 1), (1564506913061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (321187, 1), (1564506913061, 1)] : List FactorBlock).map factorBlockValue).prod) = 3014995691311940443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_321187
      · exact prime_oneHundredSixtyNineFK_1564506913061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3014995691311940443) ^ 1507497845655970221 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3014995691311940443) ^ 1004998563770646814 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3014995691311940443) ^ 9387041478366 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3014995691311940443) ^ 1927122 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_3715491229476233549 : Nat.Prime 3715491229476233549 := by
  apply lucas_primality 3715491229476233549 (2 : ZMod 3715491229476233549)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (84442982488096217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (84442982488096217, 1)] : List FactorBlock).map factorBlockValue).prod) = 3715491229476233549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_11
      · exact prime_oneHundredSixtyNineFK_84442982488096217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3715491229476233549) ^ 1857745614738116774 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3715491229476233549) ^ 337771929952384868 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3715491229476233549) ^ 44 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_3982466814969929549 : Nat.Prime 3982466814969929549 := by
  apply lucas_primality 3982466814969929549 (2 : ZMod 3982466814969929549)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (167, 1), (1721, 1), (119452937729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (167, 1), (1721, 1), (119452937729, 1)] : List FactorBlock).map factorBlockValue).prod) = 3982466814969929549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_29
      · exact prime_oneHundredSixtyNineFK_167
      · exact prime_oneHundredSixtyNineFK_1721
      · exact prime_oneHundredSixtyNineFK_119452937729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3982466814969929549) ^ 1991233407484964774 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3982466814969929549) ^ 137326441895514812 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3982466814969929549) ^ 23847106676466644 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3982466814969929549) ^ 2314042309686188 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3982466814969929549) ^ 33339212 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_5070183952836401657 : Nat.Prime 5070183952836401657 := by
  apply lucas_primality 5070183952836401657 (3 : ZMod 5070183952836401657)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (112913, 1), (5612932028239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (112913, 1), (5612932028239, 1)] : List FactorBlock).map factorBlockValue).prod) = 5070183952836401657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_112913
      · exact prime_oneHundredSixtyNineFK_5612932028239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5070183952836401657) ^ 2535091976418200828 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5070183952836401657) ^ 44903456225912 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5070183952836401657) ^ 903304 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_5305305260013302659 : Nat.Prime 5305305260013302659 := by
  apply lucas_primality 5305305260013302659 (10 : ZMod 5305305260013302659)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (101, 1), (2347, 1), (90978926309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (101, 1), (2347, 1), (90978926309, 1)] : List FactorBlock).map factorBlockValue).prod) = 5305305260013302659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_41
      · exact prime_oneHundredSixtyNineFK_101
      · exact prime_oneHundredSixtyNineFK_2347
      · exact prime_oneHundredSixtyNineFK_90978926309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 5305305260013302659) ^ 2652652630006651329 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (10 : ZMod 5305305260013302659) ^ 1768435086671100886 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (10 : ZMod 5305305260013302659) ^ 129397689268617138 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (10 : ZMod 5305305260013302659) ^ 52527774851616858 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (10 : ZMod 5305305260013302659) ^ 2260462403073414 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (10 : ZMod 5305305260013302659) ^ 58313562 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_5605507952586782827 : Nat.Prime 5605507952586782827 := by
  apply lucas_primality 5605507952586782827 (3 : ZMod 5605507952586782827)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (521, 1), (105481689672703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (521, 1), (105481689672703, 1)] : List FactorBlock).map factorBlockValue).prod) = 5605507952586782827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_17
      · exact prime_oneHundredSixtyNineFK_521
      · exact prime_oneHundredSixtyNineFK_105481689672703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5605507952586782827) ^ 2802753976293391413 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5605507952586782827) ^ 1868502650862260942 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5605507952586782827) ^ 329735761916869578 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5605507952586782827) ^ 10759132346615706 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5605507952586782827) ^ 53142 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_5634850089567050837 : Nat.Prime 5634850089567050837 := by
  apply lucas_primality 5634850089567050837 (2 : ZMod 5634850089567050837)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (11119, 1), (64879, 1), (177525119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (11119, 1), (64879, 1), (177525119, 1)] : List FactorBlock).map factorBlockValue).prod) = 5634850089567050837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_11
      · exact prime_oneHundredSixtyNineFK_11119
      · exact prime_oneHundredSixtyNineFK_64879
      · exact prime_oneHundredSixtyNineFK_177525119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5634850089567050837) ^ 2817425044783525418 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5634850089567050837) ^ 512259099051550076 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5634850089567050837) ^ 506776696606444 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5634850089567050837) ^ 86851679119084 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5634850089567050837) ^ 31741142444 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_7614708867070260491 : Nat.Prime 7614708867070260491 := by
  apply lucas_primality 7614708867070260491 (2 : ZMod 7614708867070260491)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 2), (34022383, 1), (77444527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 2), (34022383, 1), (77444527, 1)] : List FactorBlock).map factorBlockValue).prod) = 7614708867070260491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_17
      · exact prime_oneHundredSixtyNineFK_34022383
      · exact prime_oneHundredSixtyNineFK_77444527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7614708867070260491) ^ 3807354433535130245 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 7614708867070260491) ^ 1522941773414052098 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 7614708867070260491) ^ 447924051004132970 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 7614708867070260491) ^ 223814683030 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 7614708867070260491) ^ 98324686870 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_8397225673051487929 : Nat.Prime 8397225673051487929 := by
  apply lucas_primality 8397225673051487929 (11 : ZMod 8397225673051487929)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (5737, 1), (14051, 1), (228443549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (5737, 1), (14051, 1), (228443549, 1)] : List FactorBlock).map factorBlockValue).prod) = 8397225673051487929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_19
      · exact prime_oneHundredSixtyNineFK_5737
      · exact prime_oneHundredSixtyNineFK_14051
      · exact prime_oneHundredSixtyNineFK_228443549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 8397225673051487929) ^ 4198612836525743964 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (11 : ZMod 8397225673051487929) ^ 2799075224350495976 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (11 : ZMod 8397225673051487929) ^ 441959245950078312 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (11 : ZMod 8397225673051487929) ^ 1463696299991544 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (11 : ZMod 8397225673051487929) ^ 597624772119528 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (11 : ZMod 8397225673051487929) ^ 36758427672 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_8882233993405823803 : Nat.Prime 8882233993405823803 := by
  apply lucas_primality 8882233993405823803 (2 : ZMod 8882233993405823803)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1480372332234303967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1480372332234303967, 1)] : List FactorBlock).map factorBlockValue).prod) = 8882233993405823803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_1480372332234303967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 8882233993405823803) ^ 4441116996702911901 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8882233993405823803) ^ 2960744664468607934 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8882233993405823803) ^ 6 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_11692542740429910109 : Nat.Prime 11692542740429910109 := by
  apply lucas_primality 11692542740429910109 (2 : ZMod 11692542740429910109)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (974378561702492509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (974378561702492509, 1)] : List FactorBlock).map factorBlockValue).prod) = 11692542740429910109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_974378561702492509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11692542740429910109) ^ 5846271370214955054 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 11692542740429910109) ^ 3897514246809970036 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 11692542740429910109) ^ 12 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_15229417734140520983 : Nat.Prime 15229417734140520983 := by
  apply lucas_primality 15229417734140520983 (5 : ZMod 15229417734140520983)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7614708867070260491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7614708867070260491, 1)] : List FactorBlock).map factorBlockValue).prod) = 15229417734140520983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_7614708867070260491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 15229417734140520983) ^ 7614708867070260491 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 15229417734140520983) ^ 2 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_28108957503210771101 : Nat.Prime 28108957503210771101 := by
  apply lucas_primality 28108957503210771101 (2 : ZMod 28108957503210771101)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (281089575032107711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (281089575032107711, 1)] : List FactorBlock).map factorBlockValue).prod) = 28108957503210771101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_281089575032107711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 28108957503210771101) ^ 14054478751605385550 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 28108957503210771101) ^ 5621791500642154220 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 28108957503210771101) ^ 100 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_31266642035869431949 : Nat.Prime 31266642035869431949 := by
  apply lucas_primality 31266642035869431949 (6 : ZMod 31266642035869431949)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (97, 1), (263, 1), (34044836906813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (97, 1), (263, 1), (34044836906813, 1)] : List FactorBlock).map factorBlockValue).prod) = 31266642035869431949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_97
      · exact prime_oneHundredSixtyNineFK_263
      · exact prime_oneHundredSixtyNineFK_34044836906813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 31266642035869431949) ^ 15633321017934715974 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 31266642035869431949) ^ 10422214011956477316 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 31266642035869431949) ^ 322336515833705484 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 31266642035869431949) ^ 118884570478590996 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 31266642035869431949) ^ 918396 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_48878814666647627771 : Nat.Prime 48878814666647627771 := by
  apply lucas_primality 48878814666647627771 (2 : ZMod 48878814666647627771)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (23, 1), (328271, 1), (38081267057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (23, 1), (328271, 1), (38081267057, 1)] : List FactorBlock).map factorBlockValue).prod) = 48878814666647627771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_17
      · exact prime_oneHundredSixtyNineFK_23
      · exact prime_oneHundredSixtyNineFK_328271
      · exact prime_oneHundredSixtyNineFK_38081267057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 48878814666647627771) ^ 24439407333323813885 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 48878814666647627771) ^ 9775762933329525554 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 48878814666647627771) ^ 2875224392155742810 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 48878814666647627771) ^ 2125165855071635990 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 48878814666647627771) ^ 148897754192870 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 48878814666647627771) ^ 1283539610 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_53053052600133026591 : Nat.Prime 53053052600133026591 := by
  apply lucas_primality 53053052600133026591 (13 : ZMod 53053052600133026591)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (5305305260013302659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (5305305260013302659, 1)] : List FactorBlock).map factorBlockValue).prod) = 53053052600133026591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_5305305260013302659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 53053052600133026591) ^ 26526526300066513295 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (13 : ZMod 53053052600133026591) ^ 10610610520026605318 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (13 : ZMod 53053052600133026591) ^ 10 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_83668240518057402979 : Nat.Prime 83668240518057402979 := by
  apply lucas_primality 83668240518057402979 (3 : ZMod 83668240518057402979)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1697, 1), (8217269742492379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1697, 1), (8217269742492379, 1)] : List FactorBlock).map factorBlockValue).prod) = 83668240518057402979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_1697
      · exact prime_oneHundredSixtyNineFK_8217269742492379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 83668240518057402979) ^ 41834120259028701489 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 83668240518057402979) ^ 27889413506019134326 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 83668240518057402979) ^ 49303618454954274 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 83668240518057402979) ^ 10182 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_105131039647847779157 : Nat.Prime 105131039647847779157 := by
  apply lucas_primality 105131039647847779157 (2 : ZMod 105131039647847779157)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (173, 1), (1831, 1), (2676546708113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (173, 1), (1831, 1), (2676546708113, 1)] : List FactorBlock).map factorBlockValue).prod) = 105131039647847779157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_31
      · exact prime_oneHundredSixtyNineFK_173
      · exact prime_oneHundredSixtyNineFK_1831
      · exact prime_oneHundredSixtyNineFK_2676546708113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 105131039647847779157) ^ 52565519823923889578 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 105131039647847779157) ^ 3391323859607992876 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 105131039647847779157) ^ 607693870796807972 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 105131039647847779157) ^ 57417279982440076 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 105131039647847779157) ^ 39278612 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_134445233374224880007 : Nat.Prime 134445233374224880007 := by
  apply lucas_primality 134445233374224880007 (5 : ZMod 134445233374224880007)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (127, 1), (151, 1), (467, 1), (7506160818217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (127, 1), (151, 1), (467, 1), (7506160818217, 1)] : List FactorBlock).map factorBlockValue).prod) = 134445233374224880007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_127
      · exact prime_oneHundredSixtyNineFK_151
      · exact prime_oneHundredSixtyNineFK_467
      · exact prime_oneHundredSixtyNineFK_7506160818217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 134445233374224880007) ^ 67222616687112440003 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 134445233374224880007) ^ 1058623884836416378 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 134445233374224880007) ^ 890365783935264106 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 134445233374224880007) ^ 287891292021894818 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 134445233374224880007) ^ 17911318 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_334672962072229611917 : Nat.Prime 334672962072229611917 := by
  apply lucas_primality 334672962072229611917 (2 : ZMod 334672962072229611917)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (83668240518057402979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (83668240518057402979, 1)] : List FactorBlock).map factorBlockValue).prod) = 334672962072229611917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_83668240518057402979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 334672962072229611917) ^ 167336481036114805958 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 334672962072229611917) ^ 4 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_379329305236451297653 : Nat.Prime 379329305236451297653 := by
  apply lucas_primality 379329305236451297653 (5 : ZMod 379329305236451297653)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5448323, 1), (5801927572277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5448323, 1), (5801927572277, 1)] : List FactorBlock).map factorBlockValue).prod) = 379329305236451297653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_5448323
      · exact prime_oneHundredSixtyNineFK_5801927572277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 379329305236451297653) ^ 189664652618225648826 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 379329305236451297653) ^ 126443101745483765884 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 379329305236451297653) ^ 69623130867324 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 379329305236451297653) ^ 65379876 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_472061411762961541247 : Nat.Prime 472061411762961541247 := by
  apply lucas_primality 472061411762961541247 (5 : ZMod 472061411762961541247)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (23, 1), (587, 1), (495799, 1), (3205562407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (23, 1), (587, 1), (495799, 1), (3205562407, 1)] : List FactorBlock).map factorBlockValue).prod) = 472061411762961541247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_11
      · exact prime_oneHundredSixtyNineFK_23
      · exact prime_oneHundredSixtyNineFK_587
      · exact prime_oneHundredSixtyNineFK_495799
      · exact prime_oneHundredSixtyNineFK_3205562407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 472061411762961541247) ^ 236030705881480770623 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 472061411762961541247) ^ 42914673796632867386 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 472061411762961541247) ^ 20524409207085284402 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 472061411762961541247) ^ 804193205729065658 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 472061411762961541247) ^ 952122557251954 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 472061411762961541247) ^ 147263210578 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_566666835265044922523 : Nat.Prime 566666835265044922523 := by
  apply lucas_primality 566666835265044922523 (2 : ZMod 566666835265044922523)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1217, 1), (12203, 1), (19078341164711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1217, 1), (12203, 1), (19078341164711, 1)] : List FactorBlock).map factorBlockValue).prod) = 566666835265044922523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_1217
      · exact prime_oneHundredSixtyNineFK_12203
      · exact prime_oneHundredSixtyNineFK_19078341164711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 566666835265044922523) ^ 283333417632522461261 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 566666835265044922523) ^ 465625994465936666 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 566666835265044922523) ^ 46436682394906574 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 566666835265044922523) ^ 29702102 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_654278044547262999497 : Nat.Prime 654278044547262999497 := by
  apply lucas_primality 654278044547262999497 (3 : ZMod 654278044547262999497)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (101, 1), (84127, 1), (9625329027931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (101, 1), (84127, 1), (9625329027931, 1)] : List FactorBlock).map factorBlockValue).prod) = 654278044547262999497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_101
      · exact prime_oneHundredSixtyNineFK_84127
      · exact prime_oneHundredSixtyNineFK_9625329027931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 654278044547262999497) ^ 327139022273631499748 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 654278044547262999497) ^ 6478000441062009896 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 654278044547262999497) ^ 7777265854568248 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 654278044547262999497) ^ 67974616 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_914889170606674696241 : Nat.Prime 914889170606674696241 := by
  apply lucas_primality 914889170606674696241 (3 : ZMod 914889170606674696241)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (29, 1), (394348780433911507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (29, 1), (394348780433911507, 1)] : List FactorBlock).map factorBlockValue).prod) = 914889170606674696241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_29
      · exact prime_oneHundredSixtyNineFK_394348780433911507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 914889170606674696241) ^ 457444585303337348120 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 914889170606674696241) ^ 182977834121334939248 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 914889170606674696241) ^ 31547902434712920560 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 914889170606674696241) ^ 2320 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_1229635431332928230239 : Nat.Prime 1229635431332928230239 := by
  apply lucas_primality 1229635431332928230239 (3 : ZMod 1229635431332928230239)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (191, 1), (4003, 1), (9927557170763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (191, 1), (4003, 1), (9927557170763, 1)] : List FactorBlock).map factorBlockValue).prod) = 1229635431332928230239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_191
      · exact prime_oneHundredSixtyNineFK_4003
      · exact prime_oneHundredSixtyNineFK_9927557170763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1229635431332928230239) ^ 614817715666464115119 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1229635431332928230239) ^ 409878477110976076746 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1229635431332928230239) ^ 6437881839439414818 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1229635431332928230239) ^ 307178473977748746 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1229635431332928230239) ^ 123860826 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_2074949581101156252881 : Nat.Prime 2074949581101156252881 := by
  apply lucas_primality 2074949581101156252881 (3 : ZMod 2074949581101156252881)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (43, 1), (113, 1), (19146287, 1), (278795717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (43, 1), (113, 1), (19146287, 1), (278795717, 1)] : List FactorBlock).map factorBlockValue).prod) = 2074949581101156252881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_43
      · exact prime_oneHundredSixtyNineFK_113
      · exact prime_oneHundredSixtyNineFK_19146287
      · exact prime_oneHundredSixtyNineFK_278795717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2074949581101156252881) ^ 1037474790550578126440 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2074949581101156252881) ^ 414989916220231250576 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2074949581101156252881) ^ 48254641420957122160 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2074949581101156252881) ^ 18362385673461559760 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2074949581101156252881) ^ 108373471112240 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2074949581101156252881) ^ 7442544682640 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_2832368470577769247483 : Nat.Prime 2832368470577769247483 := by
  apply lucas_primality 2832368470577769247483 (5 : ZMod 2832368470577769247483)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (472061411762961541247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (472061411762961541247, 1)] : List FactorBlock).map factorBlockValue).prod) = 2832368470577769247483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_472061411762961541247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2832368470577769247483) ^ 1416184235288884623741 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 2832368470577769247483) ^ 944122823525923082494 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 2832368470577769247483) ^ 6 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_5121942728684063900791 : Nat.Prime 5121942728684063900791 := by
  apply lucas_primality 5121942728684063900791 (6 : ZMod 5121942728684063900791)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (113, 1), (1510897560083794661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (113, 1), (1510897560083794661, 1)] : List FactorBlock).map factorBlockValue).prod) = 5121942728684063900791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_113
      · exact prime_oneHundredSixtyNineFK_1510897560083794661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 5121942728684063900791) ^ 2560971364342031950395 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 5121942728684063900791) ^ 1707314242894687966930 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 5121942728684063900791) ^ 1024388545736812780158 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 5121942728684063900791) ^ 45326926802513839830 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 5121942728684063900791) ^ 3390 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_6463569983665893301297 : Nat.Prime 6463569983665893301297 := by
  apply lucas_primality 6463569983665893301297 (5 : ZMod 6463569983665893301297)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (83, 1), (1662347, 1), (325319568059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (83, 1), (1662347, 1), (325319568059, 1)] : List FactorBlock).map factorBlockValue).prod) = 6463569983665893301297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_83
      · exact prime_oneHundredSixtyNineFK_1662347
      · exact prime_oneHundredSixtyNineFK_325319568059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6463569983665893301297) ^ 3231784991832946650648 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 6463569983665893301297) ^ 2154523327888631100432 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 6463569983665893301297) ^ 77874337152601124112 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 6463569983665893301297) ^ 3888219477441168 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 6463569983665893301297) ^ 19868371344 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_11101442910320680602859 : Nat.Prime 11101442910320680602859 := by
  apply lucas_primality 11101442910320680602859 (2 : ZMod 11101442910320680602859)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (227, 1), (12197, 1), (222755298876899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (227, 1), (12197, 1), (222755298876899, 1)] : List FactorBlock).map factorBlockValue).prod) = 11101442910320680602859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_227
      · exact prime_oneHundredSixtyNineFK_12197
      · exact prime_oneHundredSixtyNineFK_222755298876899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11101442910320680602859) ^ 5550721455160340301429 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 11101442910320680602859) ^ 3700480970106893534286 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 11101442910320680602859) ^ 48905034847227667854 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 11101442910320680602859) ^ 910178151211009314 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 11101442910320680602859) ^ 49836942 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_11144369743995659131789 : Nat.Prime 11144369743995659131789 := by
  apply lucas_primality 11144369743995659131789 (2 : ZMod 11144369743995659131789)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (48878814666647627771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (48878814666647627771, 1)] : List FactorBlock).map factorBlockValue).prod) = 11144369743995659131789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_19
      · exact prime_oneHundredSixtyNineFK_48878814666647627771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11144369743995659131789) ^ 5572184871997829565894 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 11144369743995659131789) ^ 3714789914665219710596 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 11144369743995659131789) ^ 586545775999771533252 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 11144369743995659131789) ^ 228 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_14174902484384579013313 : Nat.Prime 14174902484384579013313 := by
  apply lucas_primality 14174902484384579013313 (7 : ZMod 14174902484384579013313)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 5), (17, 1), (103, 1), (5477, 1), (7561, 1), (12569723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 5), (17, 1), (103, 1), (5477, 1), (7561, 1), (12569723, 1)] : List FactorBlock).map factorBlockValue).prod) = 14174902484384579013313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_17
      · exact prime_oneHundredSixtyNineFK_103
      · exact prime_oneHundredSixtyNineFK_5477
      · exact prime_oneHundredSixtyNineFK_7561
      · exact prime_oneHundredSixtyNineFK_12569723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 14174902484384579013313) ^ 7087451242192289506656 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 14174902484384579013313) ^ 4724967494794859671104 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 14174902484384579013313) ^ 833817793199092883136 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 14174902484384579013313) ^ 137620412469753194304 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 14174902484384579013313) ^ 2588077868246225856 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 14174902484384579013313) ^ 1874739119744025792 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 14174902484384579013313) ^ 1127702057108544 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_20106015158711479063193 : Nat.Prime 20106015158711479063193 := by
  apply lucas_primality 20106015158711479063193 (3 : ZMod 20106015158711479063193)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (719749531, 1), (498834621647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (719749531, 1), (498834621647, 1)] : List FactorBlock).map factorBlockValue).prod) = 20106015158711479063193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_719749531
      · exact prime_oneHundredSixtyNineFK_498834621647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 20106015158711479063193) ^ 10053007579355739531596 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 20106015158711479063193) ^ 2872287879815925580456 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 20106015158711479063193) ^ 27934738812232 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 20106015158711479063193) ^ 40305973736 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_49008898340585701262639 : Nat.Prime 49008898340585701262639 := by
  apply lucas_primality 49008898340585701262639 (11 : ZMod 49008898340585701262639)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (151, 1), (103787, 1), (1563597756299587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (151, 1), (103787, 1), (1563597756299587, 1)] : List FactorBlock).map factorBlockValue).prod) = 49008898340585701262639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_151
      · exact prime_oneHundredSixtyNineFK_103787
      · exact prime_oneHundredSixtyNineFK_1563597756299587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 49008898340585701262639) ^ 24504449170292850631319 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (11 : ZMod 49008898340585701262639) ^ 324562240666130471938 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (11 : ZMod 49008898340585701262639) ^ 472206522402475274 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (11 : ZMod 49008898340585701262639) ^ 31343674 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_52282660955972034247861 : Nat.Prime 52282660955972034247861 := by
  apply lucas_primality 52282660955972034247861 (2 : ZMod 52282660955972034247861)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (31, 1), (28108957503210771101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (31, 1), (28108957503210771101, 1)] : List FactorBlock).map factorBlockValue).prod) = 52282660955972034247861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_31
      · exact prime_oneHundredSixtyNineFK_28108957503210771101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 52282660955972034247861) ^ 26141330477986017123930 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 52282660955972034247861) ^ 17427553651990678082620 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 52282660955972034247861) ^ 10456532191194406849572 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 52282660955972034247861) ^ 1686537450192646266060 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 52282660955972034247861) ^ 1860 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_100329910258537320213361 : Nat.Prime 100329910258537320213361 := by
  apply lucas_primality 100329910258537320213361 (17 : ZMod 100329910258537320213361)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (109, 1), (673, 1), (5698723949233277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (109, 1), (673, 1), (5698723949233277, 1)] : List FactorBlock).map factorBlockValue).prod) = 100329910258537320213361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_109
      · exact prime_oneHundredSixtyNineFK_673
      · exact prime_oneHundredSixtyNineFK_5698723949233277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 100329910258537320213361) ^ 50164955129268660106680 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (17 : ZMod 100329910258537320213361) ^ 33443303419512440071120 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (17 : ZMod 100329910258537320213361) ^ 20065982051707464042672 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (17 : ZMod 100329910258537320213361) ^ 920457892280158901040 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (17 : ZMod 100329910258537320213361) ^ 149078618511942526320 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (17 : ZMod 100329910258537320213361) ^ 17605680 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_128625488317586069425411 : Nat.Prime 128625488317586069425411 := by
  apply lucas_primality 128625488317586069425411 (2 : ZMod 128625488317586069425411)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (31, 1), (63971657, 1), (2162003974441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (31, 1), (63971657, 1), (2162003974441, 1)] : List FactorBlock).map factorBlockValue).prod) = 128625488317586069425411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_31
      · exact prime_oneHundredSixtyNineFK_63971657
      · exact prime_oneHundredSixtyNineFK_2162003974441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 128625488317586069425411) ^ 64312744158793034712705 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 128625488317586069425411) ^ 42875162772528689808470 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 128625488317586069425411) ^ 25725097663517213885082 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 128625488317586069425411) ^ 4149209300567292562110 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 128625488317586069425411) ^ 2010663696230130 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 128625488317586069425411) ^ 59493641010 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_141479767159201912318901 : Nat.Prime 141479767159201912318901 := by
  apply lucas_primality 141479767159201912318901 (2 : ZMod 141479767159201912318901)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (11, 2), (11692542740429910109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (11, 2), (11692542740429910109, 1)] : List FactorBlock).map factorBlockValue).prod) = 141479767159201912318901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_11
      · exact prime_oneHundredSixtyNineFK_11692542740429910109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 141479767159201912318901) ^ 70739883579600956159450 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 141479767159201912318901) ^ 28295953431840382463780 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 141479767159201912318901) ^ 12861797014472901119900 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 141479767159201912318901) ^ 12100 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_1758489583121024011629967 : Nat.Prime 1758489583121024011629967 := by
  apply lucas_primality 1758489583121024011629967 (6 : ZMod 1758489583121024011629967)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (1690142863, 1), (8257447839607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (1690142863, 1), (8257447839607, 1)] : List FactorBlock).map factorBlockValue).prod) = 1758489583121024011629967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_1690142863
      · exact prime_oneHundredSixtyNineFK_8257447839607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1758489583121024011629967) ^ 879244791560512005814983 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1758489583121024011629967) ^ 586163194373674670543322 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1758489583121024011629967) ^ 251212797588717715947138 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1758489583121024011629967) ^ 1040438427790482 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1758489583121024011629967) ^ 212958000738 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_2287830526987244114474713 : Nat.Prime 2287830526987244114474713 := by
  apply lucas_primality 2287830526987244114474713 (5 : ZMod 2287830526987244114474713)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (6067, 1), (27779, 1), (188538805577147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (6067, 1), (27779, 1), (188538805577147, 1)] : List FactorBlock).map factorBlockValue).prod) = 2287830526987244114474713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_6067
      · exact prime_oneHundredSixtyNineFK_27779
      · exact prime_oneHundredSixtyNineFK_188538805577147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2287830526987244114474713) ^ 1143915263493622057237356 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 2287830526987244114474713) ^ 762610175662414704824904 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 2287830526987244114474713) ^ 377094202569184788936 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 2287830526987244114474713) ^ 82358275207431661128 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 2287830526987244114474713) ^ 12134533896 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_4384531564919398513263553 : Nat.Prime 4384531564919398513263553 := by
  apply lucas_primality 4384531564919398513263553 (5 : ZMod 4384531564919398513263553)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (7, 1), (13, 1), (1251818357, 1), (200465325763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (7, 1), (13, 1), (1251818357, 1), (200465325763, 1)] : List FactorBlock).map factorBlockValue).prod) = 4384531564919398513263553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_13
      · exact prime_oneHundredSixtyNineFK_1251818357
      · exact prime_oneHundredSixtyNineFK_200465325763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4384531564919398513263553) ^ 2192265782459699256631776 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 4384531564919398513263553) ^ 1461510521639799504421184 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 4384531564919398513263553) ^ 626361652131342644751936 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 4384531564919398513263553) ^ 337271658839953731789504 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 4384531564919398513263553) ^ 3502530171731136 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (5 : ZMod 4384531564919398513263553) ^ 21871770333504 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_6607026996904103377845313 : Nat.Prime 6607026996904103377845313 := by
  apply lucas_primality 6607026996904103377845313 (15 : ZMod 6607026996904103377845313)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (13441, 1), (853398778419484457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (13441, 1), (853398778419484457, 1)] : List FactorBlock).map factorBlockValue).prod) = 6607026996904103377845313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_13441
      · exact prime_oneHundredSixtyNineFK_853398778419484457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 6607026996904103377845313) ^ 3303513498452051688922656 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (15 : ZMod 6607026996904103377845313) ^ 2202342332301367792615104 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (15 : ZMod 6607026996904103377845313) ^ 491557696369623047232 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (15 : ZMod 6607026996904103377845313) ^ 7742016 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_8403562559445532900799971 : Nat.Prime 8403562559445532900799971 := by
  apply lucas_primality 8403562559445532900799971 (10 : ZMod 8403562559445532900799971)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (2659, 1), (235117, 1), (448063754576233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (2659, 1), (235117, 1), (448063754576233, 1)] : List FactorBlock).map factorBlockValue).prod) = 8403562559445532900799971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_2659
      · exact prime_oneHundredSixtyNineFK_235117
      · exact prime_oneHundredSixtyNineFK_448063754576233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 8403562559445532900799971) ^ 4201781279722766450399985 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (10 : ZMod 8403562559445532900799971) ^ 2801187519815177633599990 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (10 : ZMod 8403562559445532900799971) ^ 1680712511889106580159994 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (10 : ZMod 8403562559445532900799971) ^ 3160422173541005227830 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (10 : ZMod 8403562559445532900799971) ^ 35742045702546106410 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (10 : ZMod 8403562559445532900799971) ^ 18755283090 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_430610136666760754847888169 : Nat.Prime 430610136666760754847888169 := by
  apply lucas_primality 430610136666760754847888169 (7 : ZMod 430610136666760754847888169)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (8647, 1), (2074949581101156252881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (8647, 1), (2074949581101156252881, 1)] : List FactorBlock).map factorBlockValue).prod) = 430610136666760754847888169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_8647
      · exact prime_oneHundredSixtyNineFK_2074949581101156252881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 430610136666760754847888169) ^ 215305068333380377423944084 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 430610136666760754847888169) ^ 143536712222253584949296056 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 430610136666760754847888169) ^ 49798789946427750069144 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 430610136666760754847888169) ^ 207528 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_920751628633073687785346131 : Nat.Prime 920751628633073687785346131 := by
  apply lucas_primality 920751628633073687785346131 (2 : ZMod 920751628633073687785346131)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (4384531564919398513263553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (4384531564919398513263553, 1)] : List FactorBlock).map factorBlockValue).prod) = 920751628633073687785346131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_4384531564919398513263553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 920751628633073687785346131) ^ 460375814316536843892673065 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 920751628633073687785346131) ^ 306917209544357895928448710 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 920751628633073687785346131) ^ 184150325726614737557069226 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 920751628633073687785346131) ^ 131535946947581955397906590 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 920751628633073687785346131) ^ 210 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_955995710111851627987656031 : Nat.Prime 955995710111851627987656031 := by
  apply lucas_primality 955995710111851627987656031 (6 : ZMod 955995710111851627987656031)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (11, 1), (13, 1), (3391, 1), (820351907, 1), (26702345737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (11, 1), (13, 1), (3391, 1), (820351907, 1), (26702345737, 1)] : List FactorBlock).map factorBlockValue).prod) = 955995710111851627987656031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_11
      · exact prime_oneHundredSixtyNineFK_13
      · exact prime_oneHundredSixtyNineFK_3391
      · exact prime_oneHundredSixtyNineFK_820351907
      · exact prime_oneHundredSixtyNineFK_26702345737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 955995710111851627987656031) ^ 477997855055925813993828015 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 955995710111851627987656031) ^ 318665236703950542662552010 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 955995710111851627987656031) ^ 191199142022370325597531206 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 955995710111851627987656031) ^ 86908700919259238907968730 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 955995710111851627987656031) ^ 73538131547065509845204310 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 955995710111851627987656031) ^ 281921471575302750807330 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 955995710111851627987656031) ^ 1165348312052929290 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (6 : ZMod 955995710111851627987656031) ^ 35801937385118190 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_3386493278192830343210510347 : Nat.Prime 3386493278192830343210510347 := by
  apply lucas_primality 3386493278192830343210510347 (2 : ZMod 3386493278192830343210510347)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (2069, 1), (106541, 1), (714677, 1), (398079114803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (2069, 1), (106541, 1), (714677, 1), (398079114803, 1)] : List FactorBlock).map factorBlockValue).prod) = 3386493278192830343210510347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_2069
      · exact prime_oneHundredSixtyNineFK_106541
      · exact prime_oneHundredSixtyNineFK_714677
      · exact prime_oneHundredSixtyNineFK_398079114803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3386493278192830343210510347) ^ 1693246639096415171605255173 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3386493278192830343210510347) ^ 1128831092730943447736836782 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3386493278192830343210510347) ^ 1636777804829787502760034 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3386493278192830343210510347) ^ 31785822154783889237106 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3386493278192830343210510347) ^ 4738494841995517336098 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3386493278192830343210510347) ^ 8507086034565582 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_22200344823708554472157790053 : Nat.Prime 22200344823708554472157790053 := by
  apply lucas_primality 22200344823708554472157790053 (2 : ZMod 22200344823708554472157790053)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (23, 2), (6125023, 1), (45432131, 1), (380836031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (23, 2), (6125023, 1), (45432131, 1), (380836031, 1)] : List FactorBlock).map factorBlockValue).prod) = 22200344823708554472157790053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_11
      · exact prime_oneHundredSixtyNineFK_23
      · exact prime_oneHundredSixtyNineFK_6125023
      · exact prime_oneHundredSixtyNineFK_45432131
      · exact prime_oneHundredSixtyNineFK_380836031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22200344823708554472157790053) ^ 11100172411854277236078895026 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 22200344823708554472157790053) ^ 7400114941236184824052596684 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 22200344823708554472157790053) ^ 2018213165791686770196162732 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 22200344823708554472157790053) ^ 965232383639502368354686524 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 22200344823708554472157790053) ^ 3624532483177378186524 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 22200344823708554472157790053) ^ 488648547516042214092 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (2 : ZMod 22200344823708554472157790053) ^ 58293709146728699292 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_28543300487625284321345730067 : Nat.Prime 28543300487625284321345730067 := by
  apply lucas_primality 28543300487625284321345730067 (3 : ZMod 28543300487625284321345730067)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3779, 1), (2224961, 1), (345695209, 1), (1636666841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3779, 1), (2224961, 1), (345695209, 1), (1636666841, 1)] : List FactorBlock).map factorBlockValue).prod) = 28543300487625284321345730067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_3779
      · exact prime_oneHundredSixtyNineFK_2224961
      · exact prime_oneHundredSixtyNineFK_345695209
      · exact prime_oneHundredSixtyNineFK_1636666841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 28543300487625284321345730067) ^ 14271650243812642160672865033 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 28543300487625284321345730067) ^ 9514433495875094773781910022 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 28543300487625284321345730067) ^ 7553135879233999555794054 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 28543300487625284321345730067) ^ 12828674519519795772306 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 28543300487625284321345730067) ^ 82567822013481489474 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 28543300487625284321345730067) ^ 17439896607293264226 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_49950775853344247562355027609 : Nat.Prime 49950775853344247562355027609 := by
  apply lucas_primality 49950775853344247562355027609 (23 : ZMod 49950775853344247562355027609)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (17, 1), (661, 1), (1193, 1), (81359, 1), (636082306604681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (17, 1), (661, 1), (1193, 1), (81359, 1), (636082306604681, 1)] : List FactorBlock).map factorBlockValue).prod) = 49950775853344247562355027609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_17
      · exact prime_oneHundredSixtyNineFK_661
      · exact prime_oneHundredSixtyNineFK_1193
      · exact prime_oneHundredSixtyNineFK_81359
      · exact prime_oneHundredSixtyNineFK_636082306604681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 49950775853344247562355027609) ^ 24975387926672123781177513804 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (23 : ZMod 49950775853344247562355027609) ^ 16650258617781415854118342536 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (23 : ZMod 49950775853344247562355027609) ^ 2938280932549661621315001624 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (23 : ZMod 49950775853344247562355027609) ^ 75568495995982220215363128 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (23 : ZMod 49950775853344247562355027609) ^ 41869887555192160571965656 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (23 : ZMod 49950775853344247562355027609) ^ 613955135305795886900712 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (23 : ZMod 49950775853344247562355027609) ^ 78528793105368 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_66601034471125663416473370151 : Nat.Prime 66601034471125663416473370151 := by
  apply lucas_primality 66601034471125663416473370151 (3 : ZMod 66601034471125663416473370151)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (72949, 1), (333439, 1), (18253829013077291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (72949, 1), (333439, 1), (18253829013077291, 1)] : List FactorBlock).map factorBlockValue).prod) = 66601034471125663416473370151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_72949
      · exact prime_oneHundredSixtyNineFK_333439
      · exact prime_oneHundredSixtyNineFK_18253829013077291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 66601034471125663416473370151) ^ 33300517235562831708236685075 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 66601034471125663416473370151) ^ 22200344823708554472157790050 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 66601034471125663416473370151) ^ 13320206894225132683294674030 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 66601034471125663416473370151) ^ 912980773843721825062350 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 66601034471125663416473370151) ^ 199739785901246295173850 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 66601034471125663416473370151) ^ 3648606241650 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_99901551706688495124710055209 : Nat.Prime 99901551706688495124710055209 := by
  apply lucas_primality 99901551706688495124710055209 (3 : ZMod 99901551706688495124710055209)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (430610136666760754847888169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (430610136666760754847888169, 1)] : List FactorBlock).map factorBlockValue).prod) = 99901551706688495124710055209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_29
      · exact prime_oneHundredSixtyNineFK_430610136666760754847888169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 99901551706688495124710055209) ^ 49950775853344247562355027604 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 99901551706688495124710055209) ^ 3444881093334086038783105352 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 99901551706688495124710055209) ^ 232 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_99901551706688495124710055241 : Nat.Prime 99901551706688495124710055241 := by
  apply lucas_primality 99901551706688495124710055241 (7 : ZMod 99901551706688495124710055241)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (131, 1), (52931733677, 1), (120061447069121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (131, 1), (52931733677, 1), (120061447069121, 1)] : List FactorBlock).map factorBlockValue).prod) = 99901551706688495124710055241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_131
      · exact prime_oneHundredSixtyNineFK_52931733677
      · exact prime_oneHundredSixtyNineFK_120061447069121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 99901551706688495124710055241) ^ 49950775853344247562355027620 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 99901551706688495124710055241) ^ 33300517235562831708236685080 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 99901551706688495124710055241) ^ 19980310341337699024942011048 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 99901551706688495124710055241) ^ 762607264936553397898550040 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 99901551706688495124710055241) ^ 1887365947926582120 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (7 : ZMod 99901551706688495124710055241) ^ 832086853402440 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_199803103413376990249420110401 : Nat.Prime 199803103413376990249420110401 := by
  apply lucas_primality 199803103413376990249420110401 (3 : ZMod 199803103413376990249420110401)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 2), (13, 2), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 2), (13, 2), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_5
      · exact prime_oneHundredSixtyNineFK_13
      · exact prime_oneHundredSixtyNineFK_171401
      · exact prime_oneHundredSixtyNineFK_714027719
      · exact prime_oneHundredSixtyNineFK_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 199803103413376990249420110401) ^ 99901551706688495124710055200 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 199803103413376990249420110401) ^ 39960620682675398049884022080 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 199803103413376990249420110401) ^ 15369469493336691557647700800 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 199803103413376990249420110401) ^ 1165705587560031681550400 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 199803103413376990249420110401) ^ 279825415872093041600 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 199803103413376990249420110401) ^ 33092921593391857600 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyNineFK_199803103413376990249420110463 : Nat.Prime 199803103413376990249420110463 := by
  apply lucas_primality 199803103413376990249420110463 (3 : ZMod 199803103413376990249420110463)
  · rw [← oneHundredSixtyNineFKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (3779, 1), (2224961, 1), (345695209, 1), (1636666841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (3779, 1), (2224961, 1), (345695209, 1), (1636666841, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyNineFK_2
      · exact prime_oneHundredSixtyNineFK_3
      · exact prime_oneHundredSixtyNineFK_7
      · exact prime_oneHundredSixtyNineFK_3779
      · exact prime_oneHundredSixtyNineFK_2224961
      · exact prime_oneHundredSixtyNineFK_345695209
      · exact prime_oneHundredSixtyNineFK_1636666841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 199803103413376990249420110463) ^ 99901551706688495124710055231 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 199803103413376990249420110463) ^ 66601034471125663416473370154 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 199803103413376990249420110463) ^ 28543300487625284321345730066 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 199803103413376990249420110463) ^ 52871951154637996890558378 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 199803103413376990249420110463) ^ 89800721636638570406142 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 199803103413376990249420110463) ^ 577974754094370426318 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide
    · change (3 : ZMod 199803103413376990249420110463) ^ 122079276251052849582 ≠ 1
      rw [← oneHundredSixtyNineFKFastPow_eq_pow]
      decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110400 : Nat.totient 199803103413376990249420110400 = 73773023038106923735087104000 := by
  rw [← show ((([(2, 6), (5, 2), (13, 2), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110400 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_5, prime_oneHundredSixtyNineFK_13, prime_oneHundredSixtyNineFK_171401, prime_oneHundredSixtyNineFK_714027719, prime_oneHundredSixtyNineFK_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110401 : Nat.totient 199803103413376990249420110401 = 199803103413376990249420110400 := by
  rw [← show ((([(199803103413376990249420110401, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110401 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_199803103413376990249420110401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110402 : Nat.totient 199803103413376990249420110402 = 59058313710939910001063116800 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (41, 1), (5209, 1), (14174902484384579013313, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110402 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_3, prime_oneHundredSixtyNineFK_11, prime_oneHundredSixtyNineFK_41, prime_oneHundredSixtyNineFK_5209, prime_oneHundredSixtyNineFK_14174902484384579013313]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110403 : Nat.totient 199803103413376990249420110403 = 189286852304787222276710221824 := by
  rw [← show ((([(19, 1), (634573, 1), (29392746433, 1), (563802335893, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110403 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_19, prime_oneHundredSixtyNineFK_634573, prime_oneHundredSixtyNineFK_29392746433, prime_oneHundredSixtyNineFK_563802335893]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110404 : Nat.totient 199803103413376990249420110404 = 99333446541613203090954852000 := by
  rw [← show ((([(2, 2), (271, 1), (499, 1), (133432513219, 1), (2768284592951, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110404 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_271, prime_oneHundredSixtyNineFK_499, prime_oneHundredSixtyNineFK_133432513219, prime_oneHundredSixtyNineFK_2768284592951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110405 : Nat.totient 199803103413376990249420110405 = 106561625211226777945606871040 := by
  rw [← show ((([(3, 2), (5, 1), (3578573, 1), (646518413, 1), (1919105882641, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110405 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_3, prime_oneHundredSixtyNineFK_5, prime_oneHundredSixtyNineFK_3578573, prime_oneHundredSixtyNineFK_646518413, prime_oneHundredSixtyNineFK_1919105882641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110406 : Nat.totient 199803103413376990249420110406 = 85586929156186809265137936384 := by
  rw [← show ((([(2, 1), (7, 2), (1993, 1), (18134537, 1), (38926313, 1), (1449169259, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110406 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_7, prime_oneHundredSixtyNineFK_1993, prime_oneHundredSixtyNineFK_18134537, prime_oneHundredSixtyNineFK_38926313, prime_oneHundredSixtyNineFK_1449169259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110407 : Nat.totient 199803103413376990249420110407 = 191942221479407442088501847040 := by
  rw [← show ((([(37, 1), (79, 1), (560792161, 1), (121890955072991669, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110407 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_37, prime_oneHundredSixtyNineFK_79, prime_oneHundredSixtyNineFK_560792161, prime_oneHundredSixtyNineFK_121890955072991669]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110408 : Nat.totient 199803103413376990249420110408 = 66490697525035297267172192256 := by
  rw [← show ((([(2, 3), (3, 1), (619, 1), (24247, 1), (1439833793, 1), (385238749183, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110408 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_3, prime_oneHundredSixtyNineFK_619, prime_oneHundredSixtyNineFK_24247, prime_oneHundredSixtyNineFK_1439833793, prime_oneHundredSixtyNineFK_385238749183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110409 : Nat.totient 199803103413376990249420110409 = 199050790462911517569822238464 := by
  rw [← show ((([(269, 1), (26597, 1), (99149, 1), (3399503, 1), (82854009379, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110409 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_269, prime_oneHundredSixtyNineFK_26597, prime_oneHundredSixtyNineFK_99149, prime_oneHundredSixtyNineFK_3399503, prime_oneHundredSixtyNineFK_82854009379]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110410 : Nat.totient 199803103413376990249420110410 = 79011795576804273411554168832 := by
  rw [← show ((([(2, 1), (5, 1), (89, 1), (6899, 1), (10464804083, 1), (3109531609057, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110410 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_5, prime_oneHundredSixtyNineFK_89, prime_oneHundredSixtyNineFK_6899, prime_oneHundredSixtyNineFK_10464804083, prime_oneHundredSixtyNineFK_3109531609057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110411 : Nat.totient 199803103413376990249420110411 = 133202068942244949439176995232 := by
  rw [← show ((([(3, 1), (21025232975533, 1), (3167671651896989, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110411 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_3, prime_oneHundredSixtyNineFK_21025232975533, prime_oneHundredSixtyNineFK_3167671651896989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110412 : Nat.totient 199803103413376990249420110412 = 99871617836536046659973122560 := by
  rw [← show ((([(2, 2), (3361, 1), (475327, 1), (31266642035869431949, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110412 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_3361, prime_oneHundredSixtyNineFK_475327, prime_oneHundredSixtyNineFK_31266642035869431949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110413 : Nat.totient 199803103413376990249420110413 = 143246421475541300710992107520 := by
  rw [← show ((([(7, 1), (11, 1), (13, 1), (317, 1), (9719, 1), (6998309863, 1), (9257508937, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110413 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_7, prime_oneHundredSixtyNineFK_11, prime_oneHundredSixtyNineFK_13, prime_oneHundredSixtyNineFK_317, prime_oneHundredSixtyNineFK_9719, prime_oneHundredSixtyNineFK_6998309863, prime_oneHundredSixtyNineFK_9257508937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110414 : Nat.totient 199803103413376990249420110414 = 65439853212694896386686287360 := by
  rw [← show ((([(2, 1), (3, 3), (59, 1), (2069, 1), (106541, 1), (714677, 1), (398079114803, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110414 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_3, prime_oneHundredSixtyNineFK_59, prime_oneHundredSixtyNineFK_2069, prime_oneHundredSixtyNineFK_106541, prime_oneHundredSixtyNineFK_714677, prime_oneHundredSixtyNineFK_398079114803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110415 : Nat.totient 199803103413376990249420110415 = 150439962327473102388183407104 := by
  rw [← show ((([(5, 1), (17, 1), (7023647, 1), (334672962072229611917, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110415 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_5, prime_oneHundredSixtyNineFK_17, prime_oneHundredSixtyNineFK_7023647, prime_oneHundredSixtyNineFK_334672962072229611917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110416 : Nat.totient 199803103413376990249420110416 = 96456670613354409085926949632 := by
  rw [← show ((([(2, 4), (29, 1), (430610136666760754847888169, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110416 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_29, prime_oneHundredSixtyNineFK_430610136666760754847888169]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110417 : Nat.totient 199803103413376990249420110417 = 133187998796476395178332706560 := by
  rw [← show ((([(3, 1), (9467, 1), (1501079606857, 1), (4686675374681, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110417 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_3, prime_oneHundredSixtyNineFK_9467, prime_oneHundredSixtyNineFK_1501079606857, prime_oneHundredSixtyNineFK_4686675374681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110418 : Nat.totient 199803103413376990249420110418 = 99901551706688495124710055208 := by
  rw [← show ((([(2, 1), (99901551706688495124710055209, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110418 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_99901551706688495124710055209]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110419 : Nat.totient 199803103413376990249420110419 = 199756124073344887877925232416 := by
  rw [← show ((([(4253, 1), (28563801229, 1), (1644715724703787, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110419 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_4253, prime_oneHundredSixtyNineFK_28563801229, prime_oneHundredSixtyNineFK_1644715724703787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110420 : Nat.totient 199803103413376990249420110420 = 45669258302324605075669893120 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (7, 1), (2039417, 1), (540669361, 1), (431434771973, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110420 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_3, prime_oneHundredSixtyNineFK_5, prime_oneHundredSixtyNineFK_7, prime_oneHundredSixtyNineFK_2039417, prime_oneHundredSixtyNineFK_540669361, prime_oneHundredSixtyNineFK_431434771973]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110421 : Nat.totient 199803103413376990249420110421 = 199803003083466731712097905600 := by
  rw [← show ((([(1991461, 1), (100329910258537320213361, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110421 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_1991461, prime_oneHundredSixtyNineFK_100329910258537320213361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110422 : Nat.totient 199803103413376990249420110422 = 90526608955184347447943474880 := by
  rw [← show ((([(2, 1), (19, 1), (23, 1), (44633, 1), (5121942728684063900791, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110422 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_19, prime_oneHundredSixtyNineFK_23, prime_oneHundredSixtyNineFK_44633, prime_oneHundredSixtyNineFK_5121942728684063900791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110423 : Nat.totient 199803103413376990249420110423 = 133190244011208288012675384960 := by
  rw [← show ((([(3, 2), (12659, 1), (106441, 1), (2596739, 1), (6344875045567, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110423 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_3, prime_oneHundredSixtyNineFK_12659, prime_oneHundredSixtyNineFK_106441, prime_oneHundredSixtyNineFK_2596739, prime_oneHundredSixtyNineFK_6344875045567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110424 : Nat.totient 199803103413376990249420110424 = 90090886652388146597179968000 := by
  rw [← show ((([(2, 3), (11, 1), (149, 1), (757, 1), (8589331, 1), (2343570757683731, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110424 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_11, prime_oneHundredSixtyNineFK_149, prime_oneHundredSixtyNineFK_757, prime_oneHundredSixtyNineFK_8589331, prime_oneHundredSixtyNineFK_2343570757683731]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110425 : Nat.totient 199803103413376990249420110425 = 156595706249603022541000800000 := by
  rw [← show ((([(5, 2), (61, 1), (251, 1), (6267139, 1), (83289324010206373, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110425 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_5, prime_oneHundredSixtyNineFK_61, prime_oneHundredSixtyNineFK_251, prime_oneHundredSixtyNineFK_6267139, prime_oneHundredSixtyNineFK_83289324010206373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110426 : Nat.totient 199803103413376990249420110426 = 61035590494854777143133512640 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (139, 1), (104050223, 1), (177112743868002511, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110426 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_3, prime_oneHundredSixtyNineFK_13, prime_oneHundredSixtyNineFK_139, prime_oneHundredSixtyNineFK_104050223, prime_oneHundredSixtyNineFK_177112743868002511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110427 : Nat.totient 199803103413376990249420110427 = 165735293153953263801362303400 := by
  rw [← show ((([(7, 1), (31, 1), (920751628633073687785346131, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110427 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_7, prime_oneHundredSixtyNineFK_31, prime_oneHundredSixtyNineFK_920751628633073687785346131]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110428 : Nat.totient 199803103413376990249420110428 = 98574805921102882087501267968 := by
  rw [← show ((([(2, 2), (83, 1), (809, 1), (88589, 1), (8397225673051487929, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110428 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_83, prime_oneHundredSixtyNineFK_809, prime_oneHundredSixtyNineFK_88589, prime_oneHundredSixtyNineFK_8397225673051487929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110429 : Nat.totient 199803103413376990249420110429 = 129912168644443669796332046208 := by
  rw [← show ((([(3, 1), (43, 1), (677, 1), (2287830526987244114474713, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110429 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_3, prime_oneHundredSixtyNineFK_43, prime_oneHundredSixtyNineFK_677, prime_oneHundredSixtyNineFK_2287830526987244114474713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110430 : Nat.totient 199803103413376990249420110430 = 79921215511070861436182474112 := by
  rw [← show ((([(2, 1), (5, 1), (3091219, 1), (6463569983665893301297, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110430 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_5, prime_oneHundredSixtyNineFK_3091219, prime_oneHundredSixtyNineFK_6463569983665893301297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110431 : Nat.totient 199803103413376990249420110431 = 199767569936651127063469704600 := by
  rw [← show ((([(5623, 1), (686518747, 1), (51758507535017051, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110431 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_5623, prime_oneHundredSixtyNineFK_686518747, prime_oneHundredSixtyNineFK_51758507535017051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110432 : Nat.totient 199803103413376990249420110432 = 62535263749756369821322444800 := by
  rw [← show ((([(2, 5), (3, 2), (17, 1), (661, 1), (1193, 1), (81359, 1), (636082306604681, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110432 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_3, prime_oneHundredSixtyNineFK_17, prime_oneHundredSixtyNineFK_661, prime_oneHundredSixtyNineFK_1193, prime_oneHundredSixtyNineFK_81359, prime_oneHundredSixtyNineFK_636082306604681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110433 : Nat.totient 199803103413376990249420110433 = 199796496386380086146042234880 := by
  rw [← show ((([(30241, 1), (6607026996904103377845313, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110433 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_30241, prime_oneHundredSixtyNineFK_6607026996904103377845313]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110434 : Nat.totient 199803103413376990249420110434 = 85629587766910117131830065200 := by
  rw [← show ((([(2, 1), (7, 1), (272971, 1), (52282660955972034247861, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110434 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_7, prime_oneHundredSixtyNineFK_272971, prime_oneHundredSixtyNineFK_52282660955972034247861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110435 : Nat.totient 199803103413376990249420110435 = 95062173504501425598880358400 := by
  rw [← show ((([(3, 1), (5, 1), (11, 1), (73, 1), (197, 1), (30913481, 1), (2723838083453899, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110435 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_3, prime_oneHundredSixtyNineFK_5, prime_oneHundredSixtyNineFK_11, prime_oneHundredSixtyNineFK_73, prime_oneHundredSixtyNineFK_197, prime_oneHundredSixtyNineFK_30913481, prime_oneHundredSixtyNineFK_2723838083453899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110436 : Nat.totient 199803103413376990249420110436 = 99901551706688495124710055216 := by
  rw [← show ((([(2, 2), (49950775853344247562355027609, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110436 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_49950775853344247562355027609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110437 : Nat.totient 199803103413376990249420110437 = 199803103413030922675234077036 := by
  rw [← show ((([(577353822359, 1), (346066996832211043, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110437 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_577353822359, prime_oneHundredSixtyNineFK_346066996832211043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110438 : Nat.totient 199803103413376990249420110438 = 65329697283433075032375264000 := by
  rw [← show ((([(2, 1), (3, 1), (53, 1), (4441, 1), (141479767159201912318901, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110438 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_3, prime_oneHundredSixtyNineFK_53, prime_oneHundredSixtyNineFK_4441, prime_oneHundredSixtyNineFK_141479767159201912318901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110439 : Nat.totient 199803103413376990249420110439 = 180508363501863077559281981952 := by
  rw [← show ((([(13, 1), (47, 1), (160183, 1), (7631857, 1), (267494201311979, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110439 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_13, prime_oneHundredSixtyNineFK_47, prime_oneHundredSixtyNineFK_160183, prime_oneHundredSixtyNineFK_7631857, prime_oneHundredSixtyNineFK_267494201311979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110440 : Nat.totient 199803103413376990249420110440 = 79921064108626651186892386560 := by
  rw [← show ((([(2, 3), (5, 1), (450943, 1), (3153829117, 1), (3512225810531, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110440 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_5, prime_oneHundredSixtyNineFK_450943, prime_oneHundredSixtyNineFK_3153829117, prime_oneHundredSixtyNineFK_3512225810531]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110441 : Nat.totient 199803103413376990249420110441 = 106541352369105203830211712000 := by
  rw [← show ((([(3, 3), (7, 1), (19, 1), (67, 1), (12781, 1), (13702301, 1), (4741914110413, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110441 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_3, prime_oneHundredSixtyNineFK_7, prime_oneHundredSixtyNineFK_19, prime_oneHundredSixtyNineFK_67, prime_oneHundredSixtyNineFK_12781, prime_oneHundredSixtyNineFK_13702301, prime_oneHundredSixtyNineFK_4741914110413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110442 : Nat.totient 199803103413376990249420110442 = 98234230912823309327583436800 := by
  rw [← show ((([(2, 1), (107, 1), (227, 1), (331, 1), (2470527071, 1), (5029733657089, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110442 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_107, prime_oneHundredSixtyNineFK_227, prime_oneHundredSixtyNineFK_331, prime_oneHundredSixtyNineFK_2470527071, prime_oneHundredSixtyNineFK_5029733657089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110443 : Nat.totient 199803103413376990249420110443 = 194929844294078248148220541440 := by
  rw [← show ((([(41, 1), (15780377, 1), (570725087, 1), (541095641077, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110443 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_41, prime_oneHundredSixtyNineFK_15780377, prime_oneHundredSixtyNineFK_570725087, prime_oneHundredSixtyNineFK_541095641077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110444 : Nat.totient 199803103413376990249420110444 = 64801006298737362885589977600 := by
  rw [← show ((([(2, 2), (3, 1), (37, 1), (303220441, 1), (1484091864604101661, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110444 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_3, prime_oneHundredSixtyNineFK_37, prime_oneHundredSixtyNineFK_303220441, prime_oneHundredSixtyNineFK_1484091864604101661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110445 : Nat.totient 199803103413376990249420110445 = 147620643721180412335549624320 := by
  rw [← show ((([(5, 1), (23, 1), (29, 1), (1187823636907, 1), (50437601740481, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110445 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_5, prime_oneHundredSixtyNineFK_23, prime_oneHundredSixtyNineFK_29, prime_oneHundredSixtyNineFK_1187823636907, prime_oneHundredSixtyNineFK_50437601740481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110446 : Nat.totient 199803103413376990249420110446 = 90819481016928464702227855680 := by
  rw [← show ((([(2, 1), (11, 1), (814937, 1), (11144369743995659131789, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110446 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_11, prime_oneHundredSixtyNineFK_814937, prime_oneHundredSixtyNineFK_11144369743995659131789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110447 : Nat.totient 199803103413376990249420110447 = 132816636631658827779298724672 := by
  rw [← show ((([(3, 1), (359, 1), (9227, 1), (20106015158711479063193, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110447 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_3, prime_oneHundredSixtyNineFK_359, prime_oneHundredSixtyNineFK_9227, prime_oneHundredSixtyNineFK_20106015158711479063193]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110448 : Nat.totient 199803103413376990249420110448 = 85629901332348884065857100032 := by
  rw [← show ((([(2, 4), (7, 1), (656032253, 1), (2719311851389386293, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110448 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_7, prime_oneHundredSixtyNineFK_656032253, prime_oneHundredSixtyNineFK_2719311851389386293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110449 : Nat.totient 199803103413376990249420110449 = 188049623100258483458386821120 := by
  rw [← show ((([(17, 1), (553873, 1), (11019809, 1), (1925613163622321, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110449 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_17, prime_oneHundredSixtyNineFK_553873, prime_oneHundredSixtyNineFK_11019809, prime_oneHundredSixtyNineFK_1925613163622321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110450 : Nat.totient 199803103413376990249420110450 = 53279937402643191321415555200 := by
  rw [← show ((([(2, 1), (3, 2), (5, 2), (72949, 1), (333439, 1), (18253829013077291, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110450 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_3, prime_oneHundredSixtyNineFK_5, prime_oneHundredSixtyNineFK_72949, prime_oneHundredSixtyNineFK_333439, prime_oneHundredSixtyNineFK_18253829013077291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110451 : Nat.totient 199803103413376990249420110451 = 197418460354674160536002995200 := by
  rw [← show ((([(101, 1), (593, 1), (2713, 1), (1229635431332928230239, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110451 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_101, prime_oneHundredSixtyNineFK_593, prime_oneHundredSixtyNineFK_2713, prime_oneHundredSixtyNineFK_1229635431332928230239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110452 : Nat.totient 199803103413376990249420110452 = 92216816960016581621490659328 := by
  rw [← show ((([(2, 2), (13, 1), (33312673606897, 1), (115342509540833, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110452 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_13, prime_oneHundredSixtyNineFK_33312673606897, prime_oneHundredSixtyNineFK_115342509540833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110453 : Nat.totient 199803103413376990249420110453 = 133202068942251326832946740300 := by
  rw [← show ((([(3, 1), (66601034471125663416473370151, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110453 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_3, prime_oneHundredSixtyNineFK_66601034471125663416473370151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110454 : Nat.totient 199803103413376990249420110454 = 99820785626957176715870508384 := by
  rw [← show ((([(2, 1), (1237, 1), (20279179, 1), (3982466814969929549, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110454 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_1237, prime_oneHundredSixtyNineFK_20279179, prime_oneHundredSixtyNineFK_3982466814969929549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110455 : Nat.totient 199803103413376990249420110455 = 136844833410725385540327888960 := by
  rw [← show ((([(5, 1), (7, 2), (971, 1), (6247, 1), (134445233374224880007, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110455 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_5, prime_oneHundredSixtyNineFK_7, prime_oneHundredSixtyNineFK_971, prime_oneHundredSixtyNineFK_6247, prime_oneHundredSixtyNineFK_134445233374224880007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110456 : Nat.totient 199803103413376990249420110456 = 66405263010383495005443237888 := by
  rw [← show ((([(2, 3), (3, 1), (503, 1), (1049, 1), (1798922659, 1), (8770715472553, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110456 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_3, prime_oneHundredSixtyNineFK_503, prime_oneHundredSixtyNineFK_1049, prime_oneHundredSixtyNineFK_1798922659, prime_oneHundredSixtyNineFK_8770715472553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110457 : Nat.totient 199803103413376990249420110457 = 181639184884096896974005319760 := by
  rw [← show ((([(11, 1), (4888699063, 1), (3715491229476233549, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110457 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_11, prime_oneHundredSixtyNineFK_4888699063, prime_oneHundredSixtyNineFK_3715491229476233549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110458 : Nat.totient 199803103413376990249420110458 = 96630745120998134418183456000 := by
  rw [← show ((([(2, 1), (31, 1), (2161, 1), (28109, 1), (53053052600133026591, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110458 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_31, prime_oneHundredSixtyNineFK_2161, prime_oneHundredSixtyNineFK_28109, prime_oneHundredSixtyNineFK_53053052600133026591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110459 : Nat.totient 199803103413376990249420110459 = 133145200418589970712954798400 := by
  rw [← show ((([(3, 2), (4451, 1), (4943, 1), (208981189, 1), (4828411988963, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110459 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_3, prime_oneHundredSixtyNineFK_4451, prime_oneHundredSixtyNineFK_4943, prime_oneHundredSixtyNineFK_208981189, prime_oneHundredSixtyNineFK_4828411988963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110460 : Nat.totient 199803103413376990249420110460 = 75713261633079562758608725824 := by
  rw [← show ((([(2, 2), (5, 1), (19, 1), (47363, 1), (11101442910320680602859, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110460 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_5, prime_oneHundredSixtyNineFK_19, prime_oneHundredSixtyNineFK_47363, prime_oneHundredSixtyNineFK_11101442910320680602859]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110461 : Nat.totient 199803103413376990249420110461 = 198479819052998210490679684800 := by
  rw [← show ((([(151, 1), (2335057, 1), (566666835265044922523, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110461 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_151, prime_oneHundredSixtyNineFK_2335057, prime_oneHundredSixtyNineFK_566666835265044922523]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110462 : Nat.totient 199803103413376990249420110462 = 57071468852970097102619443200 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (3779, 1), (2224961, 1), (345695209, 1), (1636666841, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110462 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_3, prime_oneHundredSixtyNineFK_7, prime_oneHundredSixtyNineFK_3779, prime_oneHundredSixtyNineFK_2224961, prime_oneHundredSixtyNineFK_345695209, prime_oneHundredSixtyNineFK_1636666841]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110463 : Nat.totient 199803103413376990249420110463 = 199803103413376990249420110462 := by
  rw [← show ((([(199803103413376990249420110463, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110463 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_199803103413376990249420110463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110464 : Nat.totient 199803103413376990249420110464 = 98494487576621467294685030400 := by
  rw [← show ((([(2, 7), (71, 1), (4576435033, 1), (4804039943204891, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110464 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_71, prime_oneHundredSixtyNineFK_4576435033, prime_oneHundredSixtyNineFK_4804039943204891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110465 : Nat.totient 199803103413376990249420110465 = 98364604476310587127661078016 := by
  rw [← show ((([(3, 1), (5, 1), (13, 1), (349996873, 1), (2927544154246713619, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110465 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_3, prime_oneHundredSixtyNineFK_5, prime_oneHundredSixtyNineFK_13, prime_oneHundredSixtyNineFK_349996873, prime_oneHundredSixtyNineFK_2927544154246713619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110466 : Nat.totient 199803103413376990249420110466 = 94022501950332651012961459200 := by
  rw [← show ((([(2, 1), (17, 1), (37951, 1), (9080177, 1), (17053195632415487, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110466 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_17, prime_oneHundredSixtyNineFK_37951, prime_oneHundredSixtyNineFK_9080177, prime_oneHundredSixtyNineFK_17053195632415487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110467 : Nat.totient 199803103413376990249420110467 = 198279626611336699943890107072 := by
  rw [← show ((([(199, 1), (383, 1), (517043, 1), (5070183952836401657, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110467 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_199, prime_oneHundredSixtyNineFK_383, prime_oneHundredSixtyNineFK_517043, prime_oneHundredSixtyNineFK_5070183952836401657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110468 : Nat.totient 199803103413376990249420110468 = 57913932136262361421206384000 := by
  rw [← show ((([(2, 2), (3, 4), (11, 1), (23, 2), (6125023, 1), (45432131, 1), (380836031, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110468 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_3, prime_oneHundredSixtyNineFK_11, prime_oneHundredSixtyNineFK_23, prime_oneHundredSixtyNineFK_6125023, prime_oneHundredSixtyNineFK_45432131, prime_oneHundredSixtyNineFK_380836031]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110469 : Nat.totient 199803103413376990249420110469 = 171259802925751705928074380396 := by
  rw [← show ((([(7, 1), (28543300487625284321345730067, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110469 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_7, prime_oneHundredSixtyNineFK_28543300487625284321345730067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110470 : Nat.totient 199803103413376990249420110470 = 79921241365329214473551840064 := by
  rw [← show ((([(2, 1), (5, 1), (3705752800063, 1), (5391700801250969, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110470 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_5, prime_oneHundredSixtyNineFK_3705752800063, prime_oneHundredSixtyNineFK_5391700801250969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110471 : Nat.totient 199803103413376990249420110471 = 132353529770219868048118137984 := by
  rw [← show ((([(3, 1), (157, 1), (1118317, 1), (379329305236451297653, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110471 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_3, prime_oneHundredSixtyNineFK_157, prime_oneHundredSixtyNineFK_1118317, prime_oneHundredSixtyNineFK_379329305236451297653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110472 : Nat.totient 199803103413376990249420110472 = 97574195001660946698066719040 := by
  rw [← show ((([(2, 3), (43, 1), (24007, 1), (425074411, 1), (56916859996319, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110472 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_43, prime_oneHundredSixtyNineFK_24007, prime_oneHundredSixtyNineFK_425074411, prime_oneHundredSixtyNineFK_56916859996319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110473 : Nat.totient 199803103413376990249420110473 = 196416610135184159906209600068 := by
  rw [← show ((([(59, 1), (3386493278192830343210510347, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110473 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_59, prime_oneHundredSixtyNineFK_3386493278192830343210510347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110474 : Nat.totient 199803103413376990249420110474 = 64205971658914828712633318592 := by
  rw [← show ((([(2, 1), (3, 1), (29, 1), (653, 1), (1758489583121024011629967, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110474 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_3, prime_oneHundredSixtyNineFK_29, prime_oneHundredSixtyNineFK_653, prime_oneHundredSixtyNineFK_1758489583121024011629967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110475 : Nat.totient 199803103413376990249420110475 = 158427934928959339507857208320 := by
  rw [← show ((([(5, 2), (113, 1), (12617369, 1), (5605507952586782827, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110475 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_5, prime_oneHundredSixtyNineFK_113, prime_oneHundredSixtyNineFK_12617369, prime_oneHundredSixtyNineFK_5605507952586782827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110476 : Nat.totient 199803103413376990249420110476 = 85629901456541117366055380880 := by
  rw [← show ((([(2, 2), (7, 1), (13517518187, 1), (527894619647632591, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110476 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_7, prime_oneHundredSixtyNineFK_13517518187, prime_oneHundredSixtyNineFK_527894619647632591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110477 : Nat.totient 199803103413376990249420110477 = 133202068942251326832946740312 := by
  rw [← show ((([(3, 2), (22200344823708554472157790053, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110477 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_3, prime_oneHundredSixtyNineFK_22200344823708554472157790053]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110478 : Nat.totient 199803103413376990249420110478 = 91916425377685546878717063648 := by
  rw [← show ((([(2, 1), (13, 1), (307, 1), (8302403, 1), (3014995691311940443, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110478 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_13, prime_oneHundredSixtyNineFK_307, prime_oneHundredSixtyNineFK_8302403, prime_oneHundredSixtyNineFK_3014995691311940443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110479 : Nat.totient 199803103413376990249420110479 = 172079227820133293037778085400 := by
  rw [← show ((([(11, 1), (19, 1), (955995710111851627987656031, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110479 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_11, prime_oneHundredSixtyNineFK_19, prime_oneHundredSixtyNineFK_955995710111851627987656031]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110480 : Nat.totient 199803103413376990249420110480 = 52874103701268350622660198400 := by
  rw [← show ((([(2, 4), (3, 1), (5, 1), (131, 1), (52931733677, 1), (120061447069121, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110480 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_3, prime_oneHundredSixtyNineFK_5, prime_oneHundredSixtyNineFK_131, prime_oneHundredSixtyNineFK_52931733677, prime_oneHundredSixtyNineFK_120061447069121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110481 : Nat.totient 199803103413376990249420110481 = 194398389019760341198232254320 := by
  rw [← show ((([(37, 1), (41983, 1), (128625488317586069425411, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110481 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_37, prime_oneHundredSixtyNineFK_41983, prime_oneHundredSixtyNineFK_128625488317586069425411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110482 : Nat.totient 199803103413376990249420110482 = 99901551706688495124710055240 := by
  rw [← show ((([(2, 1), (99901551706688495124710055241, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110482 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_99901551706688495124710055241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110483 : Nat.totient 199803103413376990249420110483 = 106830133604426724189015214080 := by
  rw [← show ((([(3, 1), (7, 1), (17, 1), (173, 1), (18367, 1), (2579191, 1), (68291425731899, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110483 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_3, prime_oneHundredSixtyNineFK_7, prime_oneHundredSixtyNineFK_17, prime_oneHundredSixtyNineFK_173, prime_oneHundredSixtyNineFK_18367, prime_oneHundredSixtyNineFK_2579191, prime_oneHundredSixtyNineFK_68291425731899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110484 : Nat.totient 199803103413376990249420110484 = 97464835773146933757454440960 := by
  rw [← show ((([(2, 2), (41, 1), (1053083, 1), (576225343, 1), (2007721290649, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110484 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_41, prime_oneHundredSixtyNineFK_1053083, prime_oneHundredSixtyNineFK_576225343, prime_oneHundredSixtyNineFK_2007721290649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110485 : Nat.totient 199803103413376990249420110485 = 159601299230338052864360795136 := by
  rw [← show ((([(5, 1), (1039, 1), (2953, 1), (4799, 1), (2713953990196456409, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110485 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_5, prime_oneHundredSixtyNineFK_1039, prime_oneHundredSixtyNineFK_2953, prime_oneHundredSixtyNineFK_4799, prime_oneHundredSixtyNineFK_2713953990196456409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110486 : Nat.totient 199803103413376990249420110486 = 63303813808567738606924251840 := by
  rw [← show ((([(2, 1), (3, 2), (47, 1), (61, 1), (79, 1), (49008898340585701262639, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110486 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_3, prime_oneHundredSixtyNineFK_47, prime_oneHundredSixtyNineFK_61, prime_oneHundredSixtyNineFK_79, prime_oneHundredSixtyNineFK_49008898340585701262639]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110487 : Nat.totient 199803103413376990249420110487 = 199789504384502680974382116192 := by
  rw [← show ((([(14783, 1), (2398597, 1), (5634850089567050837, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110487 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_14783, prime_oneHundredSixtyNineFK_2398597, prime_oneHundredSixtyNineFK_5634850089567050837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110488 : Nat.totient 199803103413376990249420110488 = 99875574157847320392766275840 := by
  rw [← show ((([(2, 3), (3881, 1), (422557, 1), (15229417734140520983, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110488 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_3881, prime_oneHundredSixtyNineFK_422557, prime_oneHundredSixtyNineFK_15229417734140520983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110489 : Nat.totient 199803103413376990249420110489 = 128846563162484709094737733440 := by
  rw [← show ((([(3, 1), (31, 1), (2243, 1), (107837, 1), (8882233993405823803, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110489 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_3, prime_oneHundredSixtyNineFK_31, prime_oneHundredSixtyNineFK_2243, prime_oneHundredSixtyNineFK_107837, prime_oneHundredSixtyNineFK_8882233993405823803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110490 : Nat.totient 199803103413376990249420110490 = 62276291277472051147107109440 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (11, 1), (89538079, 1), (2898035704870355603, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110490 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_5, prime_oneHundredSixtyNineFK_7, prime_oneHundredSixtyNineFK_11, prime_oneHundredSixtyNineFK_89538079, prime_oneHundredSixtyNineFK_2898035704870355603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110491 : Nat.totient 199803103413376990249420110491 = 173084756272593950359945903104 := by
  rw [← show ((([(13, 1), (23, 1), (53, 1), (119929, 1), (105131039647847779157, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110491 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_13, prime_oneHundredSixtyNineFK_23, prime_oneHundredSixtyNineFK_53, prime_oneHundredSixtyNineFK_119929, prime_oneHundredSixtyNineFK_105131039647847779157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110492 : Nat.totient 199803103413376990249420110492 = 66601034471124327333354070128 := by
  rw [← show ((([(2, 2), (3, 1), (60981093390527, 1), (273039686434483, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110492 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_3, prime_oneHundredSixtyNineFK_60981093390527, prime_oneHundredSixtyNineFK_273039686434483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110493 : Nat.totient 199803103413376990249420110493 = 199803103413375902417037995740 := by
  rw [← show ((([(234010206150683, 1), (853822175964071, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110493 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_234010206150683, prime_oneHundredSixtyNineFK_853822175964071]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110494 : Nat.totient 199803103413376990249420110494 = 99853235235932813393833584384 := by
  rw [← show ((([(2, 1), (2129, 1), (71719, 1), (654278044547262999497, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110494 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_2129, prime_oneHundredSixtyNineFK_71719, prime_oneHundredSixtyNineFK_654278044547262999497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110495 : Nat.totient 199803103413376990249420110495 = 105443504058460252033875815424 := by
  rw [← show ((([(3, 3), (5, 1), (97, 1), (5387, 1), (2832368470577769247483, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110495 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_3, prime_oneHundredSixtyNineFK_5, prime_oneHundredSixtyNineFK_97, prime_oneHundredSixtyNineFK_5387, prime_oneHundredSixtyNineFK_2832368470577769247483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110496 : Nat.totient 199803103413376990249420110496 = 99767094705737366598297243840 := by
  rw [← show ((([(2, 5), (743, 1), (8403562559445532900799971, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110496 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_743, prime_oneHundredSixtyNineFK_8403562559445532900799971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110497 : Nat.totient 199803103413376990249420110497 = 171259802924391816351585761664 := by
  rw [← show ((([(7, 1), (125936620919, 1), (226648136811482209, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110497 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_7, prime_oneHundredSixtyNineFK_125936620919, prime_oneHundredSixtyNineFK_226648136811482209]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110498 : Nat.totient 199803103413376990249420110498 = 63095706993194472598203916224 := by
  rw [← show ((([(2, 1), (3, 1), (19, 1), (6395327, 1), (10966543499, 1), (24989919509, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110498 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_3, prime_oneHundredSixtyNineFK_19, prime_oneHundredSixtyNineFK_6395327, prime_oneHundredSixtyNineFK_10966543499, prime_oneHundredSixtyNineFK_24989919509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110499 : Nat.totient 199803103413376990249420110499 = 195742427511581984964698127360 := by
  rw [← show ((([(89, 1), (109, 1), (84221, 1), (238079, 1), (2161199, 1), (475279939, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110499 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_89, prime_oneHundredSixtyNineFK_109, prime_oneHundredSixtyNineFK_84221, prime_oneHundredSixtyNineFK_238079, prime_oneHundredSixtyNineFK_2161199, prime_oneHundredSixtyNineFK_475279939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110500 : Nat.totient 199803103413376990249420110500 = 75217064227925396146553856000 := by
  rw [← show ((([(2, 2), (5, 3), (17, 1), (25693, 1), (914889170606674696241, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110500 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_2, prime_oneHundredSixtyNineFK_5, prime_oneHundredSixtyNineFK_17, prime_oneHundredSixtyNineFK_25693, prime_oneHundredSixtyNineFK_914889170606674696241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyNineFK_199803103413376990249420110501 : Nat.totient 199803103413376990249420110501 = 119914566318286105244238432000 := by
  rw [← show ((([(3, 1), (11, 1), (103, 1), (50741, 1), (593179, 1), (1953018132419141, 1)] : List FactorBlock).map factorBlockValue).prod) = 199803103413376990249420110501 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyNineFK_3, prime_oneHundredSixtyNineFK_11, prime_oneHundredSixtyNineFK_103, prime_oneHundredSixtyNineFK_50741, prime_oneHundredSixtyNineFK_593179, prime_oneHundredSixtyNineFK_1953018132419141]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredSixtyNineFK : certifiedKill 1 199803103413376990249420110399 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredSixtyNineFK_199803103413376990249420110400, phi_oneHundredSixtyNineFK_199803103413376990249420110401, phi_oneHundredSixtyNineFK_199803103413376990249420110402,
    phi_oneHundredSixtyNineFK_199803103413376990249420110403, phi_oneHundredSixtyNineFK_199803103413376990249420110404, phi_oneHundredSixtyNineFK_199803103413376990249420110405,
    phi_oneHundredSixtyNineFK_199803103413376990249420110406, phi_oneHundredSixtyNineFK_199803103413376990249420110407, phi_oneHundredSixtyNineFK_199803103413376990249420110408,
    phi_oneHundredSixtyNineFK_199803103413376990249420110409, phi_oneHundredSixtyNineFK_199803103413376990249420110410, phi_oneHundredSixtyNineFK_199803103413376990249420110411,
    phi_oneHundredSixtyNineFK_199803103413376990249420110412, phi_oneHundredSixtyNineFK_199803103413376990249420110413, phi_oneHundredSixtyNineFK_199803103413376990249420110414,
    phi_oneHundredSixtyNineFK_199803103413376990249420110415, phi_oneHundredSixtyNineFK_199803103413376990249420110416, phi_oneHundredSixtyNineFK_199803103413376990249420110417,
    phi_oneHundredSixtyNineFK_199803103413376990249420110418, phi_oneHundredSixtyNineFK_199803103413376990249420110419, phi_oneHundredSixtyNineFK_199803103413376990249420110420,
    phi_oneHundredSixtyNineFK_199803103413376990249420110421, phi_oneHundredSixtyNineFK_199803103413376990249420110422, phi_oneHundredSixtyNineFK_199803103413376990249420110423,
    phi_oneHundredSixtyNineFK_199803103413376990249420110424, phi_oneHundredSixtyNineFK_199803103413376990249420110425, phi_oneHundredSixtyNineFK_199803103413376990249420110426,
    phi_oneHundredSixtyNineFK_199803103413376990249420110427, phi_oneHundredSixtyNineFK_199803103413376990249420110428, phi_oneHundredSixtyNineFK_199803103413376990249420110429,
    phi_oneHundredSixtyNineFK_199803103413376990249420110430, phi_oneHundredSixtyNineFK_199803103413376990249420110431, phi_oneHundredSixtyNineFK_199803103413376990249420110432,
    phi_oneHundredSixtyNineFK_199803103413376990249420110433, phi_oneHundredSixtyNineFK_199803103413376990249420110434, phi_oneHundredSixtyNineFK_199803103413376990249420110435,
    phi_oneHundredSixtyNineFK_199803103413376990249420110436, phi_oneHundredSixtyNineFK_199803103413376990249420110437, phi_oneHundredSixtyNineFK_199803103413376990249420110438,
    phi_oneHundredSixtyNineFK_199803103413376990249420110439, phi_oneHundredSixtyNineFK_199803103413376990249420110440, phi_oneHundredSixtyNineFK_199803103413376990249420110441,
    phi_oneHundredSixtyNineFK_199803103413376990249420110442, phi_oneHundredSixtyNineFK_199803103413376990249420110443, phi_oneHundredSixtyNineFK_199803103413376990249420110444,
    phi_oneHundredSixtyNineFK_199803103413376990249420110445, phi_oneHundredSixtyNineFK_199803103413376990249420110446, phi_oneHundredSixtyNineFK_199803103413376990249420110447,
    phi_oneHundredSixtyNineFK_199803103413376990249420110448, phi_oneHundredSixtyNineFK_199803103413376990249420110449, phi_oneHundredSixtyNineFK_199803103413376990249420110450,
    phi_oneHundredSixtyNineFK_199803103413376990249420110451, phi_oneHundredSixtyNineFK_199803103413376990249420110452, phi_oneHundredSixtyNineFK_199803103413376990249420110453,
    phi_oneHundredSixtyNineFK_199803103413376990249420110454, phi_oneHundredSixtyNineFK_199803103413376990249420110455, phi_oneHundredSixtyNineFK_199803103413376990249420110456,
    phi_oneHundredSixtyNineFK_199803103413376990249420110457, phi_oneHundredSixtyNineFK_199803103413376990249420110458, phi_oneHundredSixtyNineFK_199803103413376990249420110459,
    phi_oneHundredSixtyNineFK_199803103413376990249420110460, phi_oneHundredSixtyNineFK_199803103413376990249420110461, phi_oneHundredSixtyNineFK_199803103413376990249420110462,
    phi_oneHundredSixtyNineFK_199803103413376990249420110463, phi_oneHundredSixtyNineFK_199803103413376990249420110464, phi_oneHundredSixtyNineFK_199803103413376990249420110465,
    phi_oneHundredSixtyNineFK_199803103413376990249420110466, phi_oneHundredSixtyNineFK_199803103413376990249420110467, phi_oneHundredSixtyNineFK_199803103413376990249420110468,
    phi_oneHundredSixtyNineFK_199803103413376990249420110469, phi_oneHundredSixtyNineFK_199803103413376990249420110470, phi_oneHundredSixtyNineFK_199803103413376990249420110471,
    phi_oneHundredSixtyNineFK_199803103413376990249420110472, phi_oneHundredSixtyNineFK_199803103413376990249420110473, phi_oneHundredSixtyNineFK_199803103413376990249420110474,
    phi_oneHundredSixtyNineFK_199803103413376990249420110475, phi_oneHundredSixtyNineFK_199803103413376990249420110476, phi_oneHundredSixtyNineFK_199803103413376990249420110477,
    phi_oneHundredSixtyNineFK_199803103413376990249420110478, phi_oneHundredSixtyNineFK_199803103413376990249420110479, phi_oneHundredSixtyNineFK_199803103413376990249420110480,
    phi_oneHundredSixtyNineFK_199803103413376990249420110481, phi_oneHundredSixtyNineFK_199803103413376990249420110482, phi_oneHundredSixtyNineFK_199803103413376990249420110483,
    phi_oneHundredSixtyNineFK_199803103413376990249420110484, phi_oneHundredSixtyNineFK_199803103413376990249420110485, phi_oneHundredSixtyNineFK_199803103413376990249420110486,
    phi_oneHundredSixtyNineFK_199803103413376990249420110487, phi_oneHundredSixtyNineFK_199803103413376990249420110488, phi_oneHundredSixtyNineFK_199803103413376990249420110489,
    phi_oneHundredSixtyNineFK_199803103413376990249420110490, phi_oneHundredSixtyNineFK_199803103413376990249420110491, phi_oneHundredSixtyNineFK_199803103413376990249420110492,
    phi_oneHundredSixtyNineFK_199803103413376990249420110493, phi_oneHundredSixtyNineFK_199803103413376990249420110494, phi_oneHundredSixtyNineFK_199803103413376990249420110495,
    phi_oneHundredSixtyNineFK_199803103413376990249420110496, phi_oneHundredSixtyNineFK_199803103413376990249420110497, phi_oneHundredSixtyNineFK_199803103413376990249420110498,
    phi_oneHundredSixtyNineFK_199803103413376990249420110499, phi_oneHundredSixtyNineFK_199803103413376990249420110500, phi_oneHundredSixtyNineFK_199803103413376990249420110501
    ]

end TotientTailPeriodKiller
end Erdos249257
