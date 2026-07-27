import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredFiftyNineFAFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredFiftyNineFAFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredFiftyNineFAFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredFiftyNineFAFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredFiftyNineFAFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredFiftyNineFAFastPow a n * oneHundredFiftyNineFAFastPow a n * a else oneHundredFiftyNineFAFastPow a n * oneHundredFiftyNineFAFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredFiftyNineFA_2 : Nat.Prime 2 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_3 : Nat.Prime 3 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_5 : Nat.Prime 5 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_7 : Nat.Prime 7 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_11 : Nat.Prime 11 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_13 : Nat.Prime 13 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_17 : Nat.Prime 17 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_19 : Nat.Prime 19 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_23 : Nat.Prime 23 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_29 : Nat.Prime 29 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_31 : Nat.Prime 31 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_37 : Nat.Prime 37 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_41 : Nat.Prime 41 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_43 : Nat.Prime 43 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_47 : Nat.Prime 47 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_53 : Nat.Prime 53 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_59 : Nat.Prime 59 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_61 : Nat.Prime 61 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_67 : Nat.Prime 67 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_71 : Nat.Prime 71 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_73 : Nat.Prime 73 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_79 : Nat.Prime 79 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_83 : Nat.Prime 83 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_89 : Nat.Prime 89 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_97 : Nat.Prime 97 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_101 : Nat.Prime 101 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_103 : Nat.Prime 103 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_107 : Nat.Prime 107 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_109 : Nat.Prime 109 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_113 : Nat.Prime 113 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_127 : Nat.Prime 127 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_131 : Nat.Prime 131 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_137 : Nat.Prime 137 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_149 : Nat.Prime 149 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_151 : Nat.Prime 151 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_157 : Nat.Prime 157 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_163 : Nat.Prime 163 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_167 : Nat.Prime 167 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_173 : Nat.Prime 173 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_179 : Nat.Prime 179 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_181 : Nat.Prime 181 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_191 : Nat.Prime 191 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_193 : Nat.Prime 193 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_197 : Nat.Prime 197 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_199 : Nat.Prime 199 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_211 : Nat.Prime 211 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_223 : Nat.Prime 223 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_227 : Nat.Prime 227 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_229 : Nat.Prime 229 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_239 : Nat.Prime 239 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_241 : Nat.Prime 241 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_257 : Nat.Prime 257 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_263 : Nat.Prime 263 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_269 : Nat.Prime 269 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_271 : Nat.Prime 271 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_277 : Nat.Prime 277 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_281 : Nat.Prime 281 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_283 : Nat.Prime 283 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_293 : Nat.Prime 293 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_307 : Nat.Prime 307 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_317 : Nat.Prime 317 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_337 : Nat.Prime 337 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_347 : Nat.Prime 347 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_349 : Nat.Prime 349 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_353 : Nat.Prime 353 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_359 : Nat.Prime 359 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_367 : Nat.Prime 367 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_389 : Nat.Prime 389 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_401 : Nat.Prime 401 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_419 : Nat.Prime 419 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_421 : Nat.Prime 421 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_431 : Nat.Prime 431 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_433 : Nat.Prime 433 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_439 : Nat.Prime 439 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_443 : Nat.Prime 443 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_449 : Nat.Prime 449 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_457 : Nat.Prime 457 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_461 : Nat.Prime 461 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_463 : Nat.Prime 463 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_479 : Nat.Prime 479 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_487 : Nat.Prime 487 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_499 : Nat.Prime 499 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_503 : Nat.Prime 503 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_521 : Nat.Prime 521 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_547 : Nat.Prime 547 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_557 : Nat.Prime 557 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_563 : Nat.Prime 563 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_569 : Nat.Prime 569 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_577 : Nat.Prime 577 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_593 : Nat.Prime 593 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_599 : Nat.Prime 599 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_601 : Nat.Prime 601 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_613 : Nat.Prime 613 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_617 : Nat.Prime 617 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_619 : Nat.Prime 619 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_641 : Nat.Prime 641 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_643 : Nat.Prime 643 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_659 : Nat.Prime 659 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_677 : Nat.Prime 677 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_683 : Nat.Prime 683 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_701 : Nat.Prime 701 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_727 : Nat.Prime 727 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_733 : Nat.Prime 733 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_743 : Nat.Prime 743 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_769 : Nat.Prime 769 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_787 : Nat.Prime 787 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_797 : Nat.Prime 797 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_809 : Nat.Prime 809 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_811 : Nat.Prime 811 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_823 : Nat.Prime 823 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_829 : Nat.Prime 829 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_839 : Nat.Prime 839 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_853 : Nat.Prime 853 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_881 : Nat.Prime 881 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_887 : Nat.Prime 887 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_953 : Nat.Prime 953 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_971 : Nat.Prime 971 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1039 : Nat.Prime 1039 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1087 : Nat.Prime 1087 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1097 : Nat.Prime 1097 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1103 : Nat.Prime 1103 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1171 : Nat.Prime 1171 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1237 : Nat.Prime 1237 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1279 : Nat.Prime 1279 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1301 : Nat.Prime 1301 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1453 : Nat.Prime 1453 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1471 : Nat.Prime 1471 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1549 : Nat.Prime 1549 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1579 : Nat.Prime 1579 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1601 : Nat.Prime 1601 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1607 : Nat.Prime 1607 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1609 : Nat.Prime 1609 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1621 : Nat.Prime 1621 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1783 : Nat.Prime 1783 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1789 : Nat.Prime 1789 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1847 : Nat.Prime 1847 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1871 : Nat.Prime 1871 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1873 : Nat.Prime 1873 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1931 : Nat.Prime 1931 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1933 : Nat.Prime 1933 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1997 : Nat.Prime 1997 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_2069 : Nat.Prime 2069 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_2083 : Nat.Prime 2083 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_2143 : Nat.Prime 2143 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_2153 : Nat.Prime 2153 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_2213 : Nat.Prime 2213 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_2281 : Nat.Prime 2281 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_2309 : Nat.Prime 2309 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_2311 : Nat.Prime 2311 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_2417 : Nat.Prime 2417 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_2579 : Nat.Prime 2579 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_2687 : Nat.Prime 2687 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_2731 : Nat.Prime 2731 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_2861 : Nat.Prime 2861 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_2953 : Nat.Prime 2953 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_3001 : Nat.Prime 3001 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_3217 : Nat.Prime 3217 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_3457 : Nat.Prime 3457 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_3461 : Nat.Prime 3461 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_3499 : Nat.Prime 3499 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_3547 : Nat.Prime 3547 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_3613 : Nat.Prime 3613 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_3637 : Nat.Prime 3637 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_3673 : Nat.Prime 3673 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_3701 : Nat.Prime 3701 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_3803 : Nat.Prime 3803 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_3821 : Nat.Prime 3821 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_3833 : Nat.Prime 3833 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_3853 : Nat.Prime 3853 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_4007 : Nat.Prime 4007 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_4057 : Nat.Prime 4057 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_4349 : Nat.Prime 4349 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_4423 : Nat.Prime 4423 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_4663 : Nat.Prime 4663 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_4919 : Nat.Prime 4919 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_5179 : Nat.Prime 5179 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_5419 : Nat.Prime 5419 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_5743 : Nat.Prime 5743 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_5779 : Nat.Prime 5779 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_6311 : Nat.Prime 6311 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_6373 : Nat.Prime 6373 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_6737 : Nat.Prime 6737 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_6791 : Nat.Prime 6791 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_6827 : Nat.Prime 6827 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_6829 : Nat.Prime 6829 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_6863 : Nat.Prime 6863 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_6907 : Nat.Prime 6907 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_6967 : Nat.Prime 6967 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_7043 : Nat.Prime 7043 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_7103 : Nat.Prime 7103 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_7177 : Nat.Prime 7177 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_7207 : Nat.Prime 7207 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_7283 : Nat.Prime 7283 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_7321 : Nat.Prime 7321 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_7537 : Nat.Prime 7537 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_7669 : Nat.Prime 7669 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_8011 : Nat.Prime 8011 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_8513 : Nat.Prime 8513 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_8647 : Nat.Prime 8647 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_8681 : Nat.Prime 8681 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_8837 : Nat.Prime 8837 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_9137 : Nat.Prime 9137 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_9199 : Nat.Prime 9199 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_9281 : Nat.Prime 9281 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_10331 : Nat.Prime 10331 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_10433 : Nat.Prime 10433 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_10529 : Nat.Prime 10529 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_10601 : Nat.Prime 10601 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_10949 : Nat.Prime 10949 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_11321 : Nat.Prime 11321 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_11483 : Nat.Prime 11483 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_11731 : Nat.Prime 11731 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_12007 : Nat.Prime 12007 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_12413 : Nat.Prime 12413 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_12941 : Nat.Prime 12941 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_12973 : Nat.Prime 12973 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_13043 : Nat.Prime 13043 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_14407 : Nat.Prime 14407 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_15541 : Nat.Prime 15541 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_16229 : Nat.Prime 16229 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_16427 : Nat.Prime 16427 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_16573 : Nat.Prime 16573 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_16843 : Nat.Prime 16843 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_17203 : Nat.Prime 17203 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_18251 : Nat.Prime 18251 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_18401 : Nat.Prime 18401 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_18719 : Nat.Prime 18719 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_18743 : Nat.Prime 18743 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_19267 : Nat.Prime 19267 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_19301 : Nat.Prime 19301 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_19597 : Nat.Prime 19597 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_19793 : Nat.Prime 19793 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_19997 : Nat.Prime 19997 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_20327 : Nat.Prime 20327 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_20747 : Nat.Prime 20747 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_20753 : Nat.Prime 20753 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_21487 : Nat.Prime 21487 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_25111 : Nat.Prime 25111 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_25117 : Nat.Prime 25117 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_25793 : Nat.Prime 25793 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_26729 : Nat.Prime 26729 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_26759 : Nat.Prime 26759 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_27541 : Nat.Prime 27541 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_28403 : Nat.Prime 28403 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_28687 : Nat.Prime 28687 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_30253 : Nat.Prime 30253 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_30949 : Nat.Prime 30949 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_31177 : Nat.Prime 31177 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_31321 : Nat.Prime 31321 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_31727 : Nat.Prime 31727 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_32063 : Nat.Prime 32063 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_33851 : Nat.Prime 33851 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_33941 : Nat.Prime 33941 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_34129 : Nat.Prime 34129 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_34589 : Nat.Prime 34589 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_35831 : Nat.Prime 35831 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_36319 : Nat.Prime 36319 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_39521 : Nat.Prime 39521 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_40483 : Nat.Prime 40483 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_40841 : Nat.Prime 40841 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_42643 : Nat.Prime 42643 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_43319 : Nat.Prime 43319 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_44699 : Nat.Prime 44699 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_47527 : Nat.Prime 47527 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_47533 : Nat.Prime 47533 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_47969 : Nat.Prime 47969 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_53791 : Nat.Prime 53791 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_54799 : Nat.Prime 54799 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_67129 : Nat.Prime 67129 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_69389 : Nat.Prime 69389 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_70139 : Nat.Prime 70139 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_77731 : Nat.Prime 77731 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_77983 : Nat.Prime 77983 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_79259 : Nat.Prime 79259 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_79357 : Nat.Prime 79357 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_80233 : Nat.Prime 80233 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_80929 : Nat.Prime 80929 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_82237 : Nat.Prime 82237 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_83203 : Nat.Prime 83203 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_87313 : Nat.Prime 87313 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_88547 : Nat.Prime 88547 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_92821 : Nat.Prime 92821 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_119797 : Nat.Prime 119797 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_120691 : Nat.Prime 120691 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_126047 : Nat.Prime 126047 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_127363 : Nat.Prime 127363 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_129959 : Nat.Prime 129959 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_132001 : Nat.Prime 132001 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_136309 : Nat.Prime 136309 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_138401 : Nat.Prime 138401 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_139759 : Nat.Prime 139759 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_140407 : Nat.Prime 140407 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_145517 : Nat.Prime 145517 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_145543 : Nat.Prime 145543 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_163027 : Nat.Prime 163027 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_171401 : Nat.Prime 171401 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_172751 : Nat.Prime 172751 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_172853 : Nat.Prime 172853 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_173659 : Nat.Prime 173659 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_176903 : Nat.Prime 176903 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_182179 : Nat.Prime 182179 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_192581 : Nat.Prime 192581 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_195281 : Nat.Prime 195281 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_197273 : Nat.Prime 197273 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_203393 : Nat.Prime 203393 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_209371 : Nat.Prime 209371 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_211213 : Nat.Prime 211213 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_212987 : Nat.Prime 212987 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_218143 : Nat.Prime 218143 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_229601 : Nat.Prime 229601 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_230761 : Nat.Prime 230761 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_236653 : Nat.Prime 236653 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_237977 : Nat.Prime 237977 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_243809 : Nat.Prime 243809 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_255961 : Nat.Prime 255961 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_263537 : Nat.Prime 263537 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_296279 : Nat.Prime 296279 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_307423 : Nat.Prime 307423 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_312047 : Nat.Prime 312047 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_314851 : Nat.Prime 314851 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_348463 : Nat.Prime 348463 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_369917 : Nat.Prime 369917 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_374909 : Nat.Prime 374909 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_377393 : Nat.Prime 377393 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_381223 : Nat.Prime 381223 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_403889 : Nat.Prime 403889 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_424037 : Nat.Prime 424037 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_456647 : Nat.Prime 456647 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_514841 : Nat.Prime 514841 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_524149 : Nat.Prime 524149 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_542461 : Nat.Prime 542461 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_559841 : Nat.Prime 559841 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_575087 : Nat.Prime 575087 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_585799 : Nat.Prime 585799 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_604907 : Nat.Prime 604907 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_631003 : Nat.Prime 631003 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_678499 : Nat.Prime 678499 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_725111 : Nat.Prime 725111 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_737293 : Nat.Prime 737293 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_753937 : Nat.Prime 753937 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_756739 : Nat.Prime 756739 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_789977 : Nat.Prime 789977 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_811607 : Nat.Prime 811607 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_839117 : Nat.Prime 839117 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_883973 : Nat.Prime 883973 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_911969 : Nat.Prime 911969 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_989323 : Nat.Prime 989323 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1108747 : Nat.Prime 1108747 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1112977 : Nat.Prime 1112977 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1177717 : Nat.Prime 1177717 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1260167 : Nat.Prime 1260167 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1289839 : Nat.Prime 1289839 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1369793 : Nat.Prime 1369793 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1444903 : Nat.Prime 1444903 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1493719 : Nat.Prime 1493719 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1638011 : Nat.Prime 1638011 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1712219 : Nat.Prime 1712219 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1723957 : Nat.Prime 1723957 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1818233 : Nat.Prime 1818233 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1861583 : Nat.Prime 1861583 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1873783 : Nat.Prime 1873783 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1911961 : Nat.Prime 1911961 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1955687 : Nat.Prime 1955687 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1977743 : Nat.Prime 1977743 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_1982587 : Nat.Prime 1982587 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_2156117 : Nat.Prime 2156117 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_2330143 : Nat.Prime 2330143 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_2446693 : Nat.Prime 2446693 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_2459291 : Nat.Prime 2459291 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_2595331 : Nat.Prime 2595331 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_2636243 : Nat.Prime 2636243 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_2741797 : Nat.Prime 2741797 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_2904257 : Nat.Prime 2904257 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_3008207 : Nat.Prime 3008207 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_3150913 : Nat.Prime 3150913 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_3279737 : Nat.Prime 3279737 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_3653579 : Nat.Prime 3653579 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_4065767 : Nat.Prime 4065767 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_4255697 : Nat.Prime 4255697 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_4291759 : Nat.Prime 4291759 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_4554743 : Nat.Prime 4554743 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_4603253 : Nat.Prime 4603253 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_5328119 : Nat.Prime 5328119 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_5460491 : Nat.Prime 5460491 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_5796377 : Nat.Prime 5796377 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_6130979 : Nat.Prime 6130979 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_6930643 : Nat.Prime 6930643 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_6975581 : Nat.Prime 6975581 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_6981943 : Nat.Prime 6981943 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_7052371 : Nat.Prime 7052371 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_7461073 : Nat.Prime 7461073 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_8408053 : Nat.Prime 8408053 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_8501447 : Nat.Prime 8501447 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_9015649 : Nat.Prime 9015649 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_9860681 : Nat.Prime 9860681 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_10237013 : Nat.Prime 10237013 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_10766669 : Nat.Prime 10766669 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_10820141 : Nat.Prime 10820141 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_11088971 : Nat.Prime 11088971 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_11090077 : Nat.Prime 11090077 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_11292637 : Nat.Prime 11292637 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_11913173 : Nat.Prime 11913173 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_12244711 : Nat.Prime 12244711 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_12722849 : Nat.Prime 12722849 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_12737171 : Nat.Prime 12737171 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_13185883 : Nat.Prime 13185883 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_13224683 : Nat.Prime 13224683 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_13435817 : Nat.Prime 13435817 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_13436279 : Nat.Prime 13436279 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_15047689 : Nat.Prime 15047689 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_15581651 : Nat.Prime 15581651 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_15626833 : Nat.Prime 15626833 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_16062367 : Nat.Prime 16062367 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_16185991 : Nat.Prime 16185991 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_17236273 : Nat.Prime 17236273 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_17725927 : Nat.Prime 17725927 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_17783561 : Nat.Prime 17783561 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_18017891 : Nat.Prime 18017891 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_18065417 : Nat.Prime 18065417 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_21696511 : Nat.Prime 21696511 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_21836813 : Nat.Prime 21836813 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_22175303 : Nat.Prime 22175303 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_22841963 : Nat.Prime 22841963 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_25402583 : Nat.Prime 25402583 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_25669421 : Nat.Prime 25669421 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_25969873 : Nat.Prime 25969873 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_29222153 : Nat.Prime 29222153 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_29778929 : Nat.Prime 29778929 := by
  norm_num

private theorem prime_oneHundredFiftyNineFA_34252279 : Nat.Prime 34252279 := by
  apply lucas_primality 34252279 (3 : ZMod 34252279)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (199, 1), (28687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (199, 1), (28687, 1)] : List FactorBlock).map factorBlockValue).prod) = 34252279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_199
      · exact prime_oneHundredFiftyNineFA_28687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 34252279) ^ 17126139 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 34252279) ^ 11417426 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 34252279) ^ 172122 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 34252279) ^ 1194 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_34428517 : Nat.Prime 34428517 := by
  apply lucas_primality 34428517 (2 : ZMod 34428517)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (79, 1), (1579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (79, 1), (1579, 1)] : List FactorBlock).map factorBlockValue).prod) = 34428517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_23
      · exact prime_oneHundredFiftyNineFA_79
      · exact prime_oneHundredFiftyNineFA_1579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 34428517) ^ 17214258 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 34428517) ^ 11476172 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 34428517) ^ 1496892 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 34428517) ^ 435804 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 34428517) ^ 21804 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_35454739 : Nat.Prime 35454739 := by
  apply lucas_primality 35454739 (10 : ZMod 35454739)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (269, 1), (1997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (269, 1), (1997, 1)] : List FactorBlock).map factorBlockValue).prod) = 35454739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_11
      · exact prime_oneHundredFiftyNineFA_269
      · exact prime_oneHundredFiftyNineFA_1997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 35454739) ^ 17727369 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (10 : ZMod 35454739) ^ 11818246 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (10 : ZMod 35454739) ^ 3223158 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (10 : ZMod 35454739) ^ 131802 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (10 : ZMod 35454739) ^ 17754 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_35567123 : Nat.Prime 35567123 := by
  apply lucas_primality 35567123 (2 : ZMod 35567123)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17783561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17783561, 1)] : List FactorBlock).map factorBlockValue).prod) = 35567123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_17783561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 35567123) ^ 17783561 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 35567123) ^ 2 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_39070043 : Nat.Prime 39070043 := by
  apply lucas_primality 39070043 (2 : ZMod 39070043)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (151, 1), (619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (151, 1), (619, 1)] : List FactorBlock).map factorBlockValue).prod) = 39070043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_11
      · exact prime_oneHundredFiftyNineFA_19
      · exact prime_oneHundredFiftyNineFA_151
      · exact prime_oneHundredFiftyNineFA_619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 39070043) ^ 19535021 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 39070043) ^ 3551822 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 39070043) ^ 2056318 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 39070043) ^ 258742 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 39070043) ^ 63118 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_39853391 : Nat.Prime 39853391 := by
  apply lucas_primality 39853391 (13 : ZMod 39853391)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (577, 1), (6907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (577, 1), (6907, 1)] : List FactorBlock).map factorBlockValue).prod) = 39853391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_577
      · exact prime_oneHundredFiftyNineFA_6907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 39853391) ^ 19926695 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (13 : ZMod 39853391) ^ 7970678 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (13 : ZMod 39853391) ^ 69070 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (13 : ZMod 39853391) ^ 5770 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_49926029 : Nat.Prime 49926029 := by
  apply lucas_primality 49926029 (2 : ZMod 49926029)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41, 1), (293, 1), (1039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41, 1), (293, 1), (1039, 1)] : List FactorBlock).map factorBlockValue).prod) = 49926029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_41
      · exact prime_oneHundredFiftyNineFA_293
      · exact prime_oneHundredFiftyNineFA_1039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 49926029) ^ 24963014 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 49926029) ^ 1217708 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 49926029) ^ 170396 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 49926029) ^ 48052 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_50052643 : Nat.Prime 50052643 := by
  apply lucas_primality 50052643 (2 : ZMod 50052643)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1789, 1), (4663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1789, 1), (4663, 1)] : List FactorBlock).map factorBlockValue).prod) = 50052643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_1789
      · exact prime_oneHundredFiftyNineFA_4663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 50052643) ^ 25026321 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 50052643) ^ 16684214 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 50052643) ^ 27978 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 50052643) ^ 10734 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_51415129 : Nat.Prime 51415129 := by
  apply lucas_primality 51415129 (7 : ZMod 51415129)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (103, 1), (2311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (103, 1), (2311, 1)] : List FactorBlock).map factorBlockValue).prod) = 51415129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_103
      · exact prime_oneHundredFiftyNineFA_2311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 51415129) ^ 25707564 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 51415129) ^ 17138376 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 51415129) ^ 499176 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 51415129) ^ 22248 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_53379463 : Nat.Prime 53379463 := by
  apply lucas_primality 53379463 (3 : ZMod 53379463)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2309, 1), (3853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2309, 1), (3853, 1)] : List FactorBlock).map factorBlockValue).prod) = 53379463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_2309
      · exact prime_oneHundredFiftyNineFA_3853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 53379463) ^ 26689731 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 53379463) ^ 17793154 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 53379463) ^ 23118 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 53379463) ^ 13854 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_58002107 : Nat.Prime 58002107 := by
  apply lucas_primality 58002107 (2 : ZMod 58002107)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (167, 1), (173659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (167, 1), (173659, 1)] : List FactorBlock).map factorBlockValue).prod) = 58002107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_167
      · exact prime_oneHundredFiftyNineFA_173659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 58002107) ^ 29001053 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 58002107) ^ 347318 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 58002107) ^ 334 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_60510379 : Nat.Prime 60510379 := by
  apply lucas_primality 60510379 (13 : ZMod 60510379)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (23, 1), (25793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (23, 1), (25793, 1)] : List FactorBlock).map factorBlockValue).prod) = 60510379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_17
      · exact prime_oneHundredFiftyNineFA_23
      · exact prime_oneHundredFiftyNineFA_25793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 60510379) ^ 30255189 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (13 : ZMod 60510379) ^ 20170126 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (13 : ZMod 60510379) ^ 3559434 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (13 : ZMod 60510379) ^ 2630886 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (13 : ZMod 60510379) ^ 2346 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_62542367 : Nat.Prime 62542367 := by
  apply lucas_primality 62542367 (5 : ZMod 62542367)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (401, 1), (77983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (401, 1), (77983, 1)] : List FactorBlock).map factorBlockValue).prod) = 62542367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_401
      · exact prime_oneHundredFiftyNineFA_77983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 62542367) ^ 31271183 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 62542367) ^ 155966 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 62542367) ^ 802 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_64357477 : Nat.Prime 64357477 := by
  apply lucas_primality 64357477 (5 : ZMod 64357477)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (47, 1), (53, 1), (2153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (47, 1), (53, 1), (2153, 1)] : List FactorBlock).map factorBlockValue).prod) = 64357477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_47
      · exact prime_oneHundredFiftyNineFA_53
      · exact prime_oneHundredFiftyNineFA_2153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 64357477) ^ 32178738 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 64357477) ^ 21452492 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 64357477) ^ 1369308 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 64357477) ^ 1214292 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 64357477) ^ 29892 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_69702169 : Nat.Prime 69702169 := by
  apply lucas_primality 69702169 (17 : ZMod 69702169)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2904257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2904257, 1)] : List FactorBlock).map factorBlockValue).prod) = 69702169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_2904257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 69702169) ^ 34851084 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (17 : ZMod 69702169) ^ 23234056 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (17 : ZMod 69702169) ^ 24 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_79913401 : Nat.Prime 79913401 := by
  apply lucas_primality 79913401 (11 : ZMod 79913401)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (7, 1), (53, 1), (359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (7, 1), (53, 1), (359, 1)] : List FactorBlock).map factorBlockValue).prod) = 79913401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_53
      · exact prime_oneHundredFiftyNineFA_359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 79913401) ^ 39956700 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (11 : ZMod 79913401) ^ 26637800 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (11 : ZMod 79913401) ^ 15982680 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (11 : ZMod 79913401) ^ 11416200 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (11 : ZMod 79913401) ^ 1507800 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (11 : ZMod 79913401) ^ 222600 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_81611039 : Nat.Prime 81611039 := by
  apply lucas_primality 81611039 (11 : ZMod 81611039)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (307, 1), (5779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (307, 1), (5779, 1)] : List FactorBlock).map factorBlockValue).prod) = 81611039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_23
      · exact prime_oneHundredFiftyNineFA_307
      · exact prime_oneHundredFiftyNineFA_5779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 81611039) ^ 40805519 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (11 : ZMod 81611039) ^ 3548306 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (11 : ZMod 81611039) ^ 265834 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (11 : ZMod 81611039) ^ 14122 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_84080531 : Nat.Prime 84080531 := by
  apply lucas_primality 84080531 (2 : ZMod 84080531)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (8408053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (8408053, 1)] : List FactorBlock).map factorBlockValue).prod) = 84080531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_8408053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 84080531) ^ 42040265 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 84080531) ^ 16816106 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 84080531) ^ 10 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_86812207 : Nat.Prime 86812207 := by
  apply lucas_primality 86812207 (3 : ZMod 86812207)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (1112977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (1112977, 1)] : List FactorBlock).map factorBlockValue).prod) = 86812207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_13
      · exact prime_oneHundredFiftyNineFA_1112977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 86812207) ^ 43406103 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 86812207) ^ 28937402 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 86812207) ^ 6677862 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 86812207) ^ 78 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_89663359 : Nat.Prime 89663359 := by
  apply lucas_primality 89663359 (3 : ZMod 89663359)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (403889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (403889, 1)] : List FactorBlock).map factorBlockValue).prod) = 89663359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_37
      · exact prime_oneHundredFiftyNineFA_403889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 89663359) ^ 44831679 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 89663359) ^ 29887786 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 89663359) ^ 2423334 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 89663359) ^ 222 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_93770503 : Nat.Prime 93770503 := by
  apply lucas_primality 93770503 (3 : ZMod 93770503)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (317, 1), (7043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (317, 1), (7043, 1)] : List FactorBlock).map factorBlockValue).prod) = 93770503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_317
      · exact prime_oneHundredFiftyNineFA_7043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 93770503) ^ 46885251 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 93770503) ^ 31256834 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 93770503) ^ 13395786 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 93770503) ^ 295806 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 93770503) ^ 13314 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_95737399 : Nat.Prime 95737399 := by
  apply lucas_primality 95737399 (3 : ZMod 95737399)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (53, 1), (163, 1), (1847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (53, 1), (163, 1), (1847, 1)] : List FactorBlock).map factorBlockValue).prod) = 95737399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_53
      · exact prime_oneHundredFiftyNineFA_163
      · exact prime_oneHundredFiftyNineFA_1847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 95737399) ^ 47868699 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 95737399) ^ 31912466 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 95737399) ^ 1806366 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 95737399) ^ 587346 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 95737399) ^ 51834 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_100446427 : Nat.Prime 100446427 := by
  apply lucas_primality 100446427 (2 : ZMod 100446427)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (19, 1), (47, 1), (2083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (19, 1), (47, 1), (2083, 1)] : List FactorBlock).map factorBlockValue).prod) = 100446427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_19
      · exact prime_oneHundredFiftyNineFA_47
      · exact prime_oneHundredFiftyNineFA_2083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 100446427) ^ 50223213 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 100446427) ^ 33482142 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 100446427) ^ 5286654 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 100446427) ^ 2137158 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 100446427) ^ 48222 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_101772589 : Nat.Prime 101772589 := by
  apply lucas_primality 101772589 (2 : ZMod 101772589)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (349, 1), (1279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (349, 1), (1279, 1)] : List FactorBlock).map factorBlockValue).prod) = 101772589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_19
      · exact prime_oneHundredFiftyNineFA_349
      · exact prime_oneHundredFiftyNineFA_1279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 101772589) ^ 50886294 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 101772589) ^ 33924196 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 101772589) ^ 5356452 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 101772589) ^ 291612 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 101772589) ^ 79572 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_104710223 : Nat.Prime 104710223 := by
  apply lucas_primality 104710223 (5 : ZMod 104710223)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (163, 1), (8681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (163, 1), (8681, 1)] : List FactorBlock).map factorBlockValue).prod) = 104710223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_37
      · exact prime_oneHundredFiftyNineFA_163
      · exact prime_oneHundredFiftyNineFA_8681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 104710223) ^ 52355111 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 104710223) ^ 2830006 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 104710223) ^ 642394 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 104710223) ^ 12062 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_106355563 : Nat.Prime 106355563 := by
  apply lucas_primality 106355563 (3 : ZMod 106355563)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17725927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17725927, 1)] : List FactorBlock).map factorBlockValue).prod) = 106355563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_17725927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 106355563) ^ 53177781 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 106355563) ^ 35451854 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 106355563) ^ 6 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_116206091 : Nat.Prime 116206091 := by
  apply lucas_primality 116206091 (6 : ZMod 116206091)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (11, 1), (13, 2), (19, 1), (47, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (11, 1), (13, 2), (19, 1), (47, 1)] : List FactorBlock).map factorBlockValue).prod) = 116206091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_11
      · exact prime_oneHundredFiftyNineFA_13
      · exact prime_oneHundredFiftyNineFA_19
      · exact prime_oneHundredFiftyNineFA_47
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 116206091) ^ 58103045 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (6 : ZMod 116206091) ^ 23241218 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (6 : ZMod 116206091) ^ 16600870 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (6 : ZMod 116206091) ^ 10564190 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (6 : ZMod 116206091) ^ 8938930 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (6 : ZMod 116206091) ^ 6116110 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (6 : ZMod 116206091) ^ 2472470 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_119270369 : Nat.Prime 119270369 := by
  apply lucas_primality 119270369 (3 : ZMod 119270369)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (17, 1), (31321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (17, 1), (31321, 1)] : List FactorBlock).map factorBlockValue).prod) = 119270369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_17
      · exact prime_oneHundredFiftyNineFA_31321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 119270369) ^ 59635184 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 119270369) ^ 17038624 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 119270369) ^ 7015904 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 119270369) ^ 3808 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_207769307 : Nat.Prime 207769307 := by
  apply lucas_primality 207769307 (2 : ZMod 207769307)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (601, 1), (172853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (601, 1), (172853, 1)] : List FactorBlock).map factorBlockValue).prod) = 207769307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_601
      · exact prime_oneHundredFiftyNineFA_172853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 207769307) ^ 103884653 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 207769307) ^ 345706 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 207769307) ^ 1202 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_209420447 : Nat.Prime 209420447 := by
  apply lucas_primality 209420447 (5 : ZMod 209420447)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (104710223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (104710223, 1)] : List FactorBlock).map factorBlockValue).prod) = 209420447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_104710223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 209420447) ^ 104710223 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 209420447) ^ 2 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_221249411 : Nat.Prime 221249411 := by
  apply lucas_primality 221249411 (2 : ZMod 221249411)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (59, 1), (67, 1), (193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (59, 1), (67, 1), (193, 1)] : List FactorBlock).map factorBlockValue).prod) = 221249411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_29
      · exact prime_oneHundredFiftyNineFA_59
      · exact prime_oneHundredFiftyNineFA_67
      · exact prime_oneHundredFiftyNineFA_193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 221249411) ^ 110624705 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 221249411) ^ 44249882 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 221249411) ^ 7629290 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 221249411) ^ 3749990 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 221249411) ^ 3302230 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 221249411) ^ 1146370 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_223022117 : Nat.Prime 223022117 := by
  apply lucas_primality 223022117 (2 : ZMod 223022117)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (3279737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (3279737, 1)] : List FactorBlock).map factorBlockValue).prod) = 223022117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_17
      · exact prime_oneHundredFiftyNineFA_3279737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 223022117) ^ 111511058 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 223022117) ^ 13118948 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 223022117) ^ 68 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_231754987 : Nat.Prime 231754987 := by
  apply lucas_primality 231754987 (3 : ZMod 231754987)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (4291759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (4291759, 1)] : List FactorBlock).map factorBlockValue).prod) = 231754987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_4291759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 231754987) ^ 115877493 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 231754987) ^ 77251662 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 231754987) ^ 54 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_242258123 : Nat.Prime 242258123 := by
  apply lucas_primality 242258123 (2 : ZMod 242258123)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (743, 1), (163027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (743, 1), (163027, 1)] : List FactorBlock).map factorBlockValue).prod) = 242258123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_743
      · exact prime_oneHundredFiftyNineFA_163027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 242258123) ^ 121129061 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 242258123) ^ 326054 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 242258123) ^ 1486 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_254743421 : Nat.Prime 254743421 := by
  apply lucas_primality 254743421 (2 : ZMod 254743421)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (12737171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (12737171, 1)] : List FactorBlock).map factorBlockValue).prod) = 254743421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_12737171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 254743421) ^ 127371710 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 254743421) ^ 50948684 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 254743421) ^ 20 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_267741883 : Nat.Prime 267741883 := by
  apply lucas_primality 267741883 (2 : ZMod 267741883)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (19, 1), (59, 1), (4423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (19, 1), (59, 1), (4423, 1)] : List FactorBlock).map factorBlockValue).prod) = 267741883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_19
      · exact prime_oneHundredFiftyNineFA_59
      · exact prime_oneHundredFiftyNineFA_4423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 267741883) ^ 133870941 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 267741883) ^ 89247294 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 267741883) ^ 14091678 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 267741883) ^ 4537998 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 267741883) ^ 60534 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_280223327 : Nat.Prime 280223327 := by
  apply lucas_primality 280223327 (5 : ZMod 280223327)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3461, 1), (40483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3461, 1), (40483, 1)] : List FactorBlock).map factorBlockValue).prod) = 280223327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3461
      · exact prime_oneHundredFiftyNineFA_40483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 280223327) ^ 140111663 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 280223327) ^ 80966 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 280223327) ^ 6922 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_284243513 : Nat.Prime 284243513 := by
  apply lucas_primality 284243513 (3 : ZMod 284243513)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (725111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (725111, 1)] : List FactorBlock).map factorBlockValue).prod) = 284243513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_725111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 284243513) ^ 142121756 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 284243513) ^ 40606216 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 284243513) ^ 392 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_338107303 : Nat.Prime 338107303 := by
  apply lucas_primality 338107303 (7 : ZMod 338107303)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (1444903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (1444903, 1)] : List FactorBlock).map factorBlockValue).prod) = 338107303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_13
      · exact prime_oneHundredFiftyNineFA_1444903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 338107303) ^ 169053651 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 338107303) ^ 112702434 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 338107303) ^ 26008254 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 338107303) ^ 234 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_344726491 : Nat.Prime 344726491 := by
  apply lucas_primality 344726491 (7 : ZMod 344726491)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (881, 1), (13043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (881, 1), (13043, 1)] : List FactorBlock).map factorBlockValue).prod) = 344726491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_881
      · exact prime_oneHundredFiftyNineFA_13043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 344726491) ^ 172363245 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 344726491) ^ 114908830 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 344726491) ^ 68945298 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 344726491) ^ 391290 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 344726491) ^ 26430 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_417250243 : Nat.Prime 417250243 := by
  apply lucas_primality 417250243 (2 : ZMod 417250243)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (43, 1), (59, 1), (9137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (43, 1), (59, 1), (9137, 1)] : List FactorBlock).map factorBlockValue).prod) = 417250243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_43
      · exact prime_oneHundredFiftyNineFA_59
      · exact prime_oneHundredFiftyNineFA_9137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 417250243) ^ 208625121 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 417250243) ^ 139083414 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 417250243) ^ 9703494 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 417250243) ^ 7072038 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 417250243) ^ 45666 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_425422253 : Nat.Prime 425422253 := by
  apply lucas_primality 425422253 (2 : ZMod 425422253)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (106355563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (106355563, 1)] : List FactorBlock).map factorBlockValue).prod) = 425422253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_106355563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 425422253) ^ 212711126 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 425422253) ^ 4 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_525020833 : Nat.Prime 525020833 := by
  apply lucas_primality 525020833 (11 : ZMod 525020833)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (7, 1), (47, 1), (1847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (7, 1), (47, 1), (1847, 1)] : List FactorBlock).map factorBlockValue).prod) = 525020833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_47
      · exact prime_oneHundredFiftyNineFA_1847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 525020833) ^ 262510416 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (11 : ZMod 525020833) ^ 175006944 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (11 : ZMod 525020833) ^ 75002976 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (11 : ZMod 525020833) ^ 11170656 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (11 : ZMod 525020833) ^ 284256 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_533815433 : Nat.Prime 533815433 := by
  apply lucas_primality 533815433 (3 : ZMod 533815433)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (557, 1), (119797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (557, 1), (119797, 1)] : List FactorBlock).map factorBlockValue).prod) = 533815433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_557
      · exact prime_oneHundredFiftyNineFA_119797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 533815433) ^ 266907716 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 533815433) ^ 958376 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 533815433) ^ 4456 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_545962603 : Nat.Prime 545962603 := by
  apply lucas_primality 545962603 (2 : ZMod 545962603)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (2459291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (2459291, 1)] : List FactorBlock).map factorBlockValue).prod) = 545962603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_37
      · exact prime_oneHundredFiftyNineFA_2459291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 545962603) ^ 272981301 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 545962603) ^ 181987534 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 545962603) ^ 14755746 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 545962603) ^ 222 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_546673783 : Nat.Prime 546673783 := by
  apply lucas_primality 546673783 (3 : ZMod 546673783)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (239, 1), (381223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (239, 1), (381223, 1)] : List FactorBlock).map factorBlockValue).prod) = 546673783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_239
      · exact prime_oneHundredFiftyNineFA_381223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 546673783) ^ 273336891 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 546673783) ^ 182224594 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 546673783) ^ 2287338 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 546673783) ^ 1434 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_591872399 : Nat.Prime 591872399 := by
  apply lucas_primality 591872399 (19 : ZMod 591872399)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (31, 1), (109, 1), (6737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (31, 1), (109, 1), (6737, 1)] : List FactorBlock).map factorBlockValue).prod) = 591872399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_13
      · exact prime_oneHundredFiftyNineFA_31
      · exact prime_oneHundredFiftyNineFA_109
      · exact prime_oneHundredFiftyNineFA_6737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 591872399) ^ 295936199 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (19 : ZMod 591872399) ^ 45528646 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (19 : ZMod 591872399) ^ 19092658 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (19 : ZMod 591872399) ^ 5430022 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (19 : ZMod 591872399) ^ 87854 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_640202239 : Nat.Prime 640202239 := by
  apply lucas_primality 640202239 (3 : ZMod 640202239)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (13, 1), (911969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (13, 1), (911969, 1)] : List FactorBlock).map factorBlockValue).prod) = 640202239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_13
      · exact prime_oneHundredFiftyNineFA_911969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 640202239) ^ 320101119 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 640202239) ^ 213400746 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 640202239) ^ 49246326 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 640202239) ^ 702 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_640433267 : Nat.Prime 640433267 := by
  apply lucas_primality 640433267 (2 : ZMod 640433267)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) = 640433267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_11
      · exact prime_oneHundredFiftyNineFA_19
      · exact prime_oneHundredFiftyNineFA_61
      · exact prime_oneHundredFiftyNineFA_25117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 640433267) ^ 320216633 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 58221206 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 33707014 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 10498906 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 25498 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_641467753 : Nat.Prime 641467753 := by
  apply lucas_primality 641467753 (5 : ZMod 641467753)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (617, 1), (43319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (617, 1), (43319, 1)] : List FactorBlock).map factorBlockValue).prod) = 641467753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_617
      · exact prime_oneHundredFiftyNineFA_43319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 641467753) ^ 320733876 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 641467753) ^ 213822584 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 641467753) ^ 1039656 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 641467753) ^ 14808 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_17203
      · exact prime_oneHundredFiftyNineFA_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_762426647 : Nat.Prime 762426647 := by
  apply lucas_primality 762426647 (5 : ZMod 762426647)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (137, 1), (229, 1), (419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (137, 1), (229, 1), (419, 1)] : List FactorBlock).map factorBlockValue).prod) = 762426647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_29
      · exact prime_oneHundredFiftyNineFA_137
      · exact prime_oneHundredFiftyNineFA_229
      · exact prime_oneHundredFiftyNineFA_419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 762426647) ^ 381213323 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 762426647) ^ 26290574 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 762426647) ^ 5565158 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 762426647) ^ 3329374 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 762426647) ^ 1819634 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_780004259 : Nat.Prime 780004259 := by
  apply lucas_primality 780004259 (2 : ZMod 780004259)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (35454739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (35454739, 1)] : List FactorBlock).map factorBlockValue).prod) = 780004259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_11
      · exact prime_oneHundredFiftyNineFA_35454739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 780004259) ^ 390002129 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 780004259) ^ 70909478 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 780004259) ^ 22 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_872765963 : Nat.Prime 872765963 := by
  apply lucas_primality 872765963 (5 : ZMod 872765963)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (15047689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (15047689, 1)] : List FactorBlock).map factorBlockValue).prod) = 872765963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_29
      · exact prime_oneHundredFiftyNineFA_15047689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 872765963) ^ 436382981 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 872765963) ^ 30095378 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 872765963) ^ 58 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_937705031 : Nat.Prime 937705031 := by
  apply lucas_primality 937705031 (7 : ZMod 937705031)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (93770503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (93770503, 1)] : List FactorBlock).map factorBlockValue).prod) = 937705031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_93770503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 937705031) ^ 468852515 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 937705031) ^ 187541006 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 937705031) ^ 10 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_940924489 : Nat.Prime 940924489 := by
  apply lucas_primality 940924489 (22 : ZMod 940924489)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (29, 1), (151, 1), (1279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (29, 1), (151, 1), (1279, 1)] : List FactorBlock).map factorBlockValue).prod) = 940924489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_29
      · exact prime_oneHundredFiftyNineFA_151
      · exact prime_oneHundredFiftyNineFA_1279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 940924489) ^ 470462244 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (22 : ZMod 940924489) ^ 313641496 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (22 : ZMod 940924489) ^ 134417784 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (22 : ZMod 940924489) ^ 32445672 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (22 : ZMod 940924489) ^ 6231288 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (22 : ZMod 940924489) ^ 735672 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_1221271069 : Nat.Prime 1221271069 := by
  apply lucas_primality 1221271069 (6 : ZMod 1221271069)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (101772589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (101772589, 1)] : List FactorBlock).map factorBlockValue).prod) = 1221271069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_101772589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 1221271069) ^ 610635534 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (6 : ZMod 1221271069) ^ 407090356 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (6 : ZMod 1221271069) ^ 12 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_1272258079 : Nat.Prime 1272258079 := by
  apply lucas_primality 1272258079 (3 : ZMod 1272258079)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (2330143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (2330143, 1)] : List FactorBlock).map factorBlockValue).prod) = 1272258079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_13
      · exact prime_oneHundredFiftyNineFA_2330143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1272258079) ^ 636129039 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1272258079) ^ 424086026 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1272258079) ^ 181751154 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1272258079) ^ 97866006 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1272258079) ^ 546 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_1352429213 : Nat.Prime 1352429213 := by
  apply lucas_primality 1352429213 (2 : ZMod 1352429213)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (338107303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (338107303, 1)] : List FactorBlock).map factorBlockValue).prod) = 1352429213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_338107303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1352429213) ^ 676214606 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1352429213) ^ 4 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_1371739483 : Nat.Prime 1371739483 := by
  apply lucas_primality 1371739483 (2 : ZMod 1371739483)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (25402583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (25402583, 1)] : List FactorBlock).map factorBlockValue).prod) = 1371739483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_25402583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1371739483) ^ 685869741 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1371739483) ^ 457246494 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1371739483) ^ 54 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_1417011571 : Nat.Prime 1417011571 := by
  apply lucas_primality 1417011571 (2 : ZMod 1417011571)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (13, 1), (37, 1), (3637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (13, 1), (37, 1), (3637, 1)] : List FactorBlock).map factorBlockValue).prod) = 1417011571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_13
      · exact prime_oneHundredFiftyNineFA_37
      · exact prime_oneHundredFiftyNineFA_3637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1417011571) ^ 708505785 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1417011571) ^ 472337190 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1417011571) ^ 283402314 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1417011571) ^ 109000890 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1417011571) ^ 38297610 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1417011571) ^ 389610 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_1438441219 : Nat.Prime 1438441219 := by
  apply lucas_primality 1438441219 (3 : ZMod 1438441219)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (79913401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (79913401, 1)] : List FactorBlock).map factorBlockValue).prod) = 1438441219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_79913401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1438441219) ^ 719220609 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1438441219) ^ 479480406 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1438441219) ^ 18 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_1472279759 : Nat.Prime 1472279759 := by
  apply lucas_primality 1472279759 (11 : ZMod 1472279759)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (127, 1), (5796377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (127, 1), (5796377, 1)] : List FactorBlock).map factorBlockValue).prod) = 1472279759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_127
      · exact prime_oneHundredFiftyNineFA_5796377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 1472279759) ^ 736139879 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (11 : ZMod 1472279759) ^ 11592754 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (11 : ZMod 1472279759) ^ 254 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_1948405247 : Nat.Prime 1948405247 := by
  apply lucas_primality 1948405247 (5 : ZMod 1948405247)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83, 1), (151, 1), (77731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83, 1), (151, 1), (77731, 1)] : List FactorBlock).map factorBlockValue).prod) = 1948405247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_83
      · exact prime_oneHundredFiftyNineFA_151
      · exact prime_oneHundredFiftyNineFA_77731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1948405247) ^ 974202623 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1948405247) ^ 23474762 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1948405247) ^ 12903346 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1948405247) ^ 25066 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_2083492969 : Nat.Prime 2083492969 := by
  apply lucas_primality 2083492969 (7 : ZMod 2083492969)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (86812207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (86812207, 1)] : List FactorBlock).map factorBlockValue).prod) = 2083492969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_86812207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 2083492969) ^ 1041746484 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 2083492969) ^ 694497656 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 2083492969) ^ 24 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_2143619521 : Nat.Prime 2143619521 := by
  apply lucas_primality 2143619521 (22 : ZMod 2143619521)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (7, 1), (19, 1), (103, 1), (163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (7, 1), (19, 1), (103, 1), (163, 1)] : List FactorBlock).map factorBlockValue).prod) = 2143619521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_19
      · exact prime_oneHundredFiftyNineFA_103
      · exact prime_oneHundredFiftyNineFA_163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 2143619521) ^ 1071809760 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (22 : ZMod 2143619521) ^ 714539840 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (22 : ZMod 2143619521) ^ 428723904 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (22 : ZMod 2143619521) ^ 306231360 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (22 : ZMod 2143619521) ^ 112822080 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (22 : ZMod 2143619521) ^ 20811840 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (22 : ZMod 2143619521) ^ 13151040 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_2312752087 : Nat.Prime 2312752087 := by
  apply lucas_primality 2312752087 (3 : ZMod 2312752087)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (31, 1), (218143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (31, 1), (218143, 1)] : List FactorBlock).map factorBlockValue).prod) = 2312752087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_19
      · exact prime_oneHundredFiftyNineFA_31
      · exact prime_oneHundredFiftyNineFA_218143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2312752087) ^ 1156376043 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2312752087) ^ 770917362 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2312752087) ^ 121723794 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2312752087) ^ 74604906 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2312752087) ^ 10602 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_2704858427 : Nat.Prime 2704858427 := by
  apply lucas_primality 2704858427 (2 : ZMod 2704858427)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1352429213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1352429213, 1)] : List FactorBlock).map factorBlockValue).prod) = 2704858427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_1352429213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 2704858427) ^ 1352429213 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2704858427) ^ 2 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_3809923631 : Nat.Prime 3809923631 := by
  apply lucas_primality 3809923631 (13 : ZMod 3809923631)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (431, 1), (883973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (431, 1), (883973, 1)] : List FactorBlock).map factorBlockValue).prod) = 3809923631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_431
      · exact prime_oneHundredFiftyNineFA_883973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 3809923631) ^ 1904961815 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (13 : ZMod 3809923631) ^ 761984726 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (13 : ZMod 3809923631) ^ 8839730 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (13 : ZMod 3809923631) ^ 4310 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_4806132109 : Nat.Prime 4806132109 := by
  apply lucas_primality 4806132109 (2 : ZMod 4806132109)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (12941, 1), (30949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (12941, 1), (30949, 1)] : List FactorBlock).map factorBlockValue).prod) = 4806132109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_12941
      · exact prime_oneHundredFiftyNineFA_30949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4806132109) ^ 2403066054 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4806132109) ^ 1602044036 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4806132109) ^ 371388 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4806132109) ^ 155292 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_5547333761 : Nat.Prime 5547333761 := by
  apply lucas_primality 5547333761 (3 : ZMod 5547333761)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 1), (839, 1), (10331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 1), (839, 1), (10331, 1)] : List FactorBlock).map factorBlockValue).prod) = 5547333761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_839
      · exact prime_oneHundredFiftyNineFA_10331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5547333761) ^ 2773666880 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5547333761) ^ 1109466752 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5547333761) ^ 6611840 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5547333761) ^ 536960 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_5628813031 : Nat.Prime 5628813031 := by
  apply lucas_primality 5628813031 (6 : ZMod 5628813031)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (62542367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (62542367, 1)] : List FactorBlock).map factorBlockValue).prod) = 5628813031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_62542367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 5628813031) ^ 2814406515 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (6 : ZMod 5628813031) ^ 1876271010 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (6 : ZMod 5628813031) ^ 1125762606 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (6 : ZMod 5628813031) ^ 90 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_31
      · exact prime_oneHundredFiftyNineFA_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_6504558913 : Nat.Prime 6504558913 := by
  apply lucas_primality 6504558913 (7 : ZMod 6504558913)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (11292637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (11292637, 1)] : List FactorBlock).map factorBlockValue).prod) = 6504558913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_11292637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 6504558913) ^ 3252279456 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 6504558913) ^ 2168186304 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 6504558913) ^ 576 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_6946781833 : Nat.Prime 6946781833 := by
  apply lucas_primality 6946781833 (5 : ZMod 6946781833)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (167, 1), (192581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (167, 1), (192581, 1)] : List FactorBlock).map factorBlockValue).prod) = 6946781833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_167
      · exact prime_oneHundredFiftyNineFA_192581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6946781833) ^ 3473390916 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 6946781833) ^ 2315593944 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 6946781833) ^ 41597496 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 6946781833) ^ 36072 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_7995888361 : Nat.Prime 7995888361 := by
  apply lucas_primality 7995888361 (11 : ZMod 7995888361)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (23, 1), (241, 1), (4007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (23, 1), (241, 1), (4007, 1)] : List FactorBlock).map factorBlockValue).prod) = 7995888361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_23
      · exact prime_oneHundredFiftyNineFA_241
      · exact prime_oneHundredFiftyNineFA_4007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 7995888361) ^ 3997944180 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (11 : ZMod 7995888361) ^ 2665296120 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (11 : ZMod 7995888361) ^ 1599177672 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (11 : ZMod 7995888361) ^ 347647320 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (11 : ZMod 7995888361) ^ 33177960 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (11 : ZMod 7995888361) ^ 1995480 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_8293563323 : Nat.Prime 8293563323 := by
  apply lucas_primality 8293563323 (2 : ZMod 8293563323)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (17, 1), (22175303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (17, 1), (22175303, 1)] : List FactorBlock).map factorBlockValue).prod) = 8293563323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_11
      · exact prime_oneHundredFiftyNineFA_17
      · exact prime_oneHundredFiftyNineFA_22175303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8293563323) ^ 4146781661 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8293563323) ^ 753960302 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8293563323) ^ 487856666 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8293563323) ^ 374 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_8900480053 : Nat.Prime 8900480053 := by
  apply lucas_primality 8900480053 (2 : ZMod 8900480053)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (47, 1), (191, 1), (27541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (47, 1), (191, 1), (27541, 1)] : List FactorBlock).map factorBlockValue).prod) = 8900480053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_47
      · exact prime_oneHundredFiftyNineFA_191
      · exact prime_oneHundredFiftyNineFA_27541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8900480053) ^ 4450240026 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8900480053) ^ 2966826684 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8900480053) ^ 189371916 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8900480053) ^ 46599372 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8900480053) ^ 323172 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_9871326761 : Nat.Prime 9871326761 := by
  apply lucas_primality 9871326761 (15 : ZMod 9871326761)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (17, 2), (23, 1), (137, 1), (271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (17, 2), (23, 1), (137, 1), (271, 1)] : List FactorBlock).map factorBlockValue).prod) = 9871326761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_17
      · exact prime_oneHundredFiftyNineFA_23
      · exact prime_oneHundredFiftyNineFA_137
      · exact prime_oneHundredFiftyNineFA_271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 9871326761) ^ 4935663380 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (15 : ZMod 9871326761) ^ 1974265352 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (15 : ZMod 9871326761) ^ 580666280 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (15 : ZMod 9871326761) ^ 429188120 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (15 : ZMod 9871326761) ^ 72053480 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (15 : ZMod 9871326761) ^ 36425560 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_11313494663 : Nat.Prime 11313494663 := by
  apply lucas_primality 11313494663 (5 : ZMod 11313494663)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (37, 1), (103, 1), (87313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (37, 1), (103, 1), (87313, 1)] : List FactorBlock).map factorBlockValue).prod) = 11313494663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_17
      · exact prime_oneHundredFiftyNineFA_37
      · exact prime_oneHundredFiftyNineFA_103
      · exact prime_oneHundredFiftyNineFA_87313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 11313494663) ^ 5656747331 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 11313494663) ^ 665499686 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 11313494663) ^ 305770126 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 11313494663) ^ 109839754 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 11313494663) ^ 129574 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_11609959469 : Nat.Prime 11609959469 := by
  apply lucas_primality 11609959469 (2 : ZMod 11609959469)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1549, 1), (1873783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1549, 1), (1873783, 1)] : List FactorBlock).map factorBlockValue).prod) = 11609959469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_1549
      · exact prime_oneHundredFiftyNineFA_1873783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11609959469) ^ 5804979734 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 11609959469) ^ 7495132 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 11609959469) ^ 6196 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_12297957071 : Nat.Prime 12297957071 := by
  apply lucas_primality 12297957071 (11 : ZMod 12297957071)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (137, 1), (797, 1), (1609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (137, 1), (797, 1), (1609, 1)] : List FactorBlock).map factorBlockValue).prod) = 12297957071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_137
      · exact prime_oneHundredFiftyNineFA_797
      · exact prime_oneHundredFiftyNineFA_1609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 12297957071) ^ 6148978535 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (11 : ZMod 12297957071) ^ 2459591414 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (11 : ZMod 12297957071) ^ 1756851010 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (11 : ZMod 12297957071) ^ 89766110 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (11 : ZMod 12297957071) ^ 15430310 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (11 : ZMod 12297957071) ^ 7643230 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_13552314197 : Nat.Prime 13552314197 := by
  apply lucas_primality 13552314197 (2 : ZMod 13552314197)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (619, 1), (237977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (619, 1), (237977, 1)] : List FactorBlock).map factorBlockValue).prod) = 13552314197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_23
      · exact prime_oneHundredFiftyNineFA_619
      · exact prime_oneHundredFiftyNineFA_237977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13552314197) ^ 6776157098 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 13552314197) ^ 589231052 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 13552314197) ^ 21893884 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 13552314197) ^ 56948 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_14689556407 : Nat.Prime 14689556407 := by
  apply lucas_primality 14689556407 (3 : ZMod 14689556407)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (37, 1), (3150913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (37, 1), (3150913, 1)] : List FactorBlock).map factorBlockValue).prod) = 14689556407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_37
      · exact prime_oneHundredFiftyNineFA_3150913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 14689556407) ^ 7344778203 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 14689556407) ^ 4896518802 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 14689556407) ^ 2098508058 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 14689556407) ^ 397015038 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 14689556407) ^ 4662 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_16092631393 : Nat.Prime 16092631393 := by
  apply lucas_primality 16092631393 (5 : ZMod 16092631393)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (17, 1), (9860681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (17, 1), (9860681, 1)] : List FactorBlock).map factorBlockValue).prod) = 16092631393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_17
      · exact prime_oneHundredFiftyNineFA_9860681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 16092631393) ^ 8046315696 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 16092631393) ^ 5364210464 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 16092631393) ^ 946625376 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 16092631393) ^ 1632 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_16503636659 : Nat.Prime 16503636659 := by
  apply lucas_primality 16503636659 (2 : ZMod 16503636659)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (223022117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (223022117, 1)] : List FactorBlock).map factorBlockValue).prod) = 16503636659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_37
      · exact prime_oneHundredFiftyNineFA_223022117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 16503636659) ^ 8251818329 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 16503636659) ^ 446044234 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 16503636659) ^ 74 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_22138347709 : Nat.Prime 22138347709 := by
  apply lucas_primality 22138347709 (2 : ZMod 22138347709)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7669, 1), (26729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7669, 1), (26729, 1)] : List FactorBlock).map factorBlockValue).prod) = 22138347709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_7669
      · exact prime_oneHundredFiftyNineFA_26729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 22138347709) ^ 11069173854 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 22138347709) ^ 7379449236 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 22138347709) ^ 2886732 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 22138347709) ^ 828252 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_26767755673 : Nat.Prime 26767755673 := by
  apply lucas_primality 26767755673 (5 : ZMod 26767755673)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 3), (23, 1), (37, 1), (3821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 3), (23, 1), (37, 1), (3821, 1)] : List FactorBlock).map factorBlockValue).prod) = 26767755673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_23
      · exact prime_oneHundredFiftyNineFA_37
      · exact prime_oneHundredFiftyNineFA_3821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 26767755673) ^ 13383877836 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 26767755673) ^ 8922585224 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 26767755673) ^ 3823965096 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 26767755673) ^ 1163815464 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 26767755673) ^ 723452856 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 26767755673) ^ 7005432 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_26992428143 : Nat.Prime 26992428143 := by
  apply lucas_primality 26992428143 (5 : ZMod 26992428143)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (221249411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (221249411, 1)] : List FactorBlock).map factorBlockValue).prod) = 26992428143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_61
      · exact prime_oneHundredFiftyNineFA_221249411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 26992428143) ^ 13496214071 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 26992428143) ^ 442498822 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 26992428143) ^ 122 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_27197869187 : Nat.Prime 27197869187 := by
  apply lucas_primality 27197869187 (2 : ZMod 27197869187)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 2), (193, 1), (243809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 2), (193, 1), (243809, 1)] : List FactorBlock).map factorBlockValue).prod) = 27197869187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_17
      · exact prime_oneHundredFiftyNineFA_193
      · exact prime_oneHundredFiftyNineFA_243809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 27197869187) ^ 13598934593 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 27197869187) ^ 1599874658 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 27197869187) ^ 140921602 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 27197869187) ^ 111554 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_31701130841 : Nat.Prime 31701130841 := by
  apply lucas_primality 31701130841 (6 : ZMod 31701130841)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (37, 1), (853, 1), (25111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (37, 1), (853, 1), (25111, 1)] : List FactorBlock).map factorBlockValue).prod) = 31701130841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_37
      · exact prime_oneHundredFiftyNineFA_853
      · exact prime_oneHundredFiftyNineFA_25111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 31701130841) ^ 15850565420 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (6 : ZMod 31701130841) ^ 6340226168 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (6 : ZMod 31701130841) ^ 856787320 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (6 : ZMod 31701130841) ^ 37164280 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (6 : ZMod 31701130841) ^ 1262440 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_33769121923 : Nat.Prime 33769121923 := by
  apply lucas_primality 33769121923 (3 : ZMod 33769121923)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (109, 1), (3499, 1), (4919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (109, 1), (3499, 1), (4919, 1)] : List FactorBlock).map factorBlockValue).prod) = 33769121923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_109
      · exact prime_oneHundredFiftyNineFA_3499
      · exact prime_oneHundredFiftyNineFA_4919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 33769121923) ^ 16884560961 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 33769121923) ^ 11256373974 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 33769121923) ^ 309808458 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 33769121923) ^ 9651078 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 33769121923) ^ 6865038 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_34543175743 : Nat.Prime 34543175743 := by
  apply lucas_primality 34543175743 (3 : ZMod 34543175743)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (47, 1), (71, 1), (575087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (47, 1), (71, 1), (575087, 1)] : List FactorBlock).map factorBlockValue).prod) = 34543175743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_47
      · exact prime_oneHundredFiftyNineFA_71
      · exact prime_oneHundredFiftyNineFA_575087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 34543175743) ^ 17271587871 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 34543175743) ^ 11514391914 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 34543175743) ^ 734961186 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 34543175743) ^ 486523602 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 34543175743) ^ 60066 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_35601920213 : Nat.Prime 35601920213 := by
  apply lucas_primality 35601920213 (2 : ZMod 35601920213)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (8900480053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (8900480053, 1)] : List FactorBlock).map factorBlockValue).prod) = 35601920213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_8900480053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 35601920213) ^ 17800960106 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 35601920213) ^ 4 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_54667378301 : Nat.Prime 54667378301 := by
  apply lucas_primality 54667378301 (2 : ZMod 54667378301)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (546673783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (546673783, 1)] : List FactorBlock).map factorBlockValue).prod) = 54667378301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_546673783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 54667378301) ^ 27333689150 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 54667378301) ^ 10933475660 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 54667378301) ^ 100 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_65593250837 : Nat.Prime 65593250837 := by
  apply lucas_primality 65593250837 (2 : ZMod 65593250837)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (271, 1), (60510379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (271, 1), (60510379, 1)] : List FactorBlock).map factorBlockValue).prod) = 65593250837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_271
      · exact prime_oneHundredFiftyNineFA_60510379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 65593250837) ^ 32796625418 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 65593250837) ^ 242041516 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 65593250837) ^ 1084 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_77914288607 : Nat.Prime 77914288607 := by
  apply lucas_primality 77914288607 (5 : ZMod 77914288607)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (73, 1), (6930643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (73, 1), (6930643, 1)] : List FactorBlock).map factorBlockValue).prod) = 77914288607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_11
      · exact prime_oneHundredFiftyNineFA_73
      · exact prime_oneHundredFiftyNineFA_6930643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 77914288607) ^ 38957144303 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 77914288607) ^ 11130612658 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 77914288607) ^ 7083117146 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 77914288607) ^ 1067319022 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 77914288607) ^ 11242 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_78632141981 : Nat.Prime 78632141981 := by
  apply lucas_primality 78632141981 (2 : ZMod 78632141981)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (211, 1), (887, 1), (3001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (211, 1), (887, 1), (3001, 1)] : List FactorBlock).map factorBlockValue).prod) = 78632141981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_211
      · exact prime_oneHundredFiftyNineFA_887
      · exact prime_oneHundredFiftyNineFA_3001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 78632141981) ^ 39316070990 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 78632141981) ^ 15726428396 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 78632141981) ^ 11233163140 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 78632141981) ^ 372664180 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 78632141981) ^ 88649540 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 78632141981) ^ 26201980 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_85485900683 : Nat.Prime 85485900683 := by
  apply lucas_primality 85485900683 (2 : ZMod 85485900683)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (13, 1), (89, 1), (753937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (13, 1), (89, 1), (753937, 1)] : List FactorBlock).map factorBlockValue).prod) = 85485900683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_13
      · exact prime_oneHundredFiftyNineFA_89
      · exact prime_oneHundredFiftyNineFA_753937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 85485900683) ^ 42742950341 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 85485900683) ^ 12212271526 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 85485900683) ^ 6575838514 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 85485900683) ^ 960515738 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 85485900683) ^ 113386 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_96753101927 : Nat.Prime 96753101927 := by
  apply lucas_primality 96753101927 (5 : ZMod 96753101927)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (2953, 1), (1260167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (2953, 1), (1260167, 1)] : List FactorBlock).map factorBlockValue).prod) = 96753101927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_13
      · exact prime_oneHundredFiftyNineFA_2953
      · exact prime_oneHundredFiftyNineFA_1260167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 96753101927) ^ 48376550963 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 96753101927) ^ 7442546302 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 96753101927) ^ 32764342 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 96753101927) ^ 76778 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_115436188111 : Nat.Prime 115436188111 := by
  apply lucas_primality 115436188111 (6 : ZMod 115436188111)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (347, 1), (11088971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (347, 1), (11088971, 1)] : List FactorBlock).map factorBlockValue).prod) = 115436188111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_347
      · exact prime_oneHundredFiftyNineFA_11088971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 115436188111) ^ 57718094055 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (6 : ZMod 115436188111) ^ 38478729370 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (6 : ZMod 115436188111) ^ 23087237622 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (6 : ZMod 115436188111) ^ 332669130 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (6 : ZMod 115436188111) ^ 10410 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_158348909629 : Nat.Prime 158348909629 := by
  apply lucas_primality 158348909629 (2 : ZMod 158348909629)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (13, 1), (53, 1), (701, 1), (1301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (13, 1), (53, 1), (701, 1), (1301, 1)] : List FactorBlock).map factorBlockValue).prod) = 158348909629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_13
      · exact prime_oneHundredFiftyNineFA_53
      · exact prime_oneHundredFiftyNineFA_701
      · exact prime_oneHundredFiftyNineFA_1301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 158348909629) ^ 79174454814 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 158348909629) ^ 52782969876 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 158348909629) ^ 22621272804 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 158348909629) ^ 12180685356 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 158348909629) ^ 2987715276 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 158348909629) ^ 225890028 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 158348909629) ^ 121713228 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_219079342061 : Nat.Prime 219079342061 := by
  apply lucas_primality 219079342061 (2 : ZMod 219079342061)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (43, 1), (254743421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (43, 1), (254743421, 1)] : List FactorBlock).map factorBlockValue).prod) = 219079342061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_43
      · exact prime_oneHundredFiftyNineFA_254743421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 219079342061) ^ 109539671030 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 219079342061) ^ 43815868412 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 219079342061) ^ 5094868420 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 219079342061) ^ 860 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_243364641461 : Nat.Prime 243364641461 := by
  apply lucas_primality 243364641461 (2 : ZMod 243364641461)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) = 243364641461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_19
      · exact prime_oneHundredFiftyNineFA_640433267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 243364641461) ^ 121682320730 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 48672928292 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 12808665340 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 380 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_261456974479 : Nat.Prime 261456974479 := by
  apply lucas_primality 261456974479 (7 : ZMod 261456974479)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 2), (2281, 1), (129959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 2), (2281, 1), (129959, 1)] : List FactorBlock).map factorBlockValue).prod) = 261456974479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_2281
      · exact prime_oneHundredFiftyNineFA_129959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 261456974479) ^ 130728487239 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 261456974479) ^ 87152324826 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 261456974479) ^ 37350996354 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 261456974479) ^ 114623838 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 261456974479) ^ 2011842 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_263430948743 : Nat.Prime 263430948743 := by
  apply lucas_primality 263430948743 (5 : ZMod 263430948743)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (113, 1), (89663359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (113, 1), (89663359, 1)] : List FactorBlock).map factorBlockValue).prod) = 263430948743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_13
      · exact prime_oneHundredFiftyNineFA_113
      · exact prime_oneHundredFiftyNineFA_89663359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 263430948743) ^ 131715474371 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 263430948743) ^ 20263919134 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 263430948743) ^ 2331247334 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 263430948743) ^ 2938 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_273233758573 : Nat.Prime 273233758573 := by
  apply lucas_primality 273233758573 (2 : ZMod 273233758573)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (31, 1), (81611039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (31, 1), (81611039, 1)] : List FactorBlock).map factorBlockValue).prod) = 273233758573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_31
      · exact prime_oneHundredFiftyNineFA_81611039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 273233758573) ^ 136616879286 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 273233758573) ^ 91077919524 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 273233758573) ^ 8813992212 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 273233758573) ^ 3348 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_276188646443 : Nat.Prime 276188646443 := by
  apply lucas_primality 276188646443 (2 : ZMod 276188646443)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (8837, 1), (15626833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (8837, 1), (15626833, 1)] : List FactorBlock).map factorBlockValue).prod) = 276188646443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_8837
      · exact prime_oneHundredFiftyNineFA_15626833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 276188646443) ^ 138094323221 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 276188646443) ^ 31253666 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 276188646443) ^ 17674 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_278318393651 : Nat.Prime 278318393651 := by
  apply lucas_primality 278318393651 (2 : ZMod 278318393651)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (11, 1), (47, 1), (10766669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (11, 1), (47, 1), (10766669, 1)] : List FactorBlock).map factorBlockValue).prod) = 278318393651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_11
      · exact prime_oneHundredFiftyNineFA_47
      · exact prime_oneHundredFiftyNineFA_10766669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 278318393651) ^ 139159196825 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 278318393651) ^ 55663678730 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 278318393651) ^ 25301672150 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 278318393651) ^ 5921667950 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 278318393651) ^ 25850 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_289921734953 : Nat.Prime 289921734953 := by
  apply lucas_primality 289921734953 (3 : ZMod 289921734953)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (257, 1), (6130979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (257, 1), (6130979, 1)] : List FactorBlock).map factorBlockValue).prod) = 289921734953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_23
      · exact prime_oneHundredFiftyNineFA_257
      · exact prime_oneHundredFiftyNineFA_6130979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 289921734953) ^ 144960867476 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 289921734953) ^ 12605292824 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 289921734953) ^ 1128100136 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 289921734953) ^ 47288 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_366848151979 : Nat.Prime 366848151979 := by
  apply lucas_primality 366848151979 (2 : ZMod 366848151979)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (11321, 1), (70139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (11321, 1), (70139, 1)] : List FactorBlock).map factorBlockValue).prod) = 366848151979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_11
      · exact prime_oneHundredFiftyNineFA_11321
      · exact prime_oneHundredFiftyNineFA_70139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 366848151979) ^ 183424075989 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 366848151979) ^ 122282717326 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 366848151979) ^ 52406878854 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 366848151979) ^ 33349831998 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 366848151979) ^ 32404218 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 366848151979) ^ 5230302 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_387407651717 : Nat.Prime 387407651717 := by
  apply lucas_primality 387407651717 (2 : ZMod 387407651717)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (82237, 1), (1177717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (82237, 1), (1177717, 1)] : List FactorBlock).map factorBlockValue).prod) = 387407651717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_82237
      · exact prime_oneHundredFiftyNineFA_1177717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 387407651717) ^ 193703825858 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 387407651717) ^ 4710868 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 387407651717) ^ 328948 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_436944396181 : Nat.Prime 436944396181 := by
  apply lucas_primality 436944396181 (2 : ZMod 436944396181)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (17, 1), (433, 1), (989323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (17, 1), (433, 1), (989323, 1)] : List FactorBlock).map factorBlockValue).prod) = 436944396181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_17
      · exact prime_oneHundredFiftyNineFA_433
      · exact prime_oneHundredFiftyNineFA_989323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 436944396181) ^ 218472198090 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 436944396181) ^ 145648132060 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 436944396181) ^ 87388879236 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 436944396181) ^ 25702611540 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 436944396181) ^ 1009109460 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 436944396181) ^ 441660 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_449087020637 : Nat.Prime 449087020637 := by
  apply lucas_primality 449087020637 (2 : ZMod 449087020637)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (53, 1), (173, 1), (12244711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (53, 1), (173, 1), (12244711, 1)] : List FactorBlock).map factorBlockValue).prod) = 449087020637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_53
      · exact prime_oneHundredFiftyNineFA_173
      · exact prime_oneHundredFiftyNineFA_12244711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 449087020637) ^ 224543510318 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 449087020637) ^ 8473340012 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 449087020637) ^ 2595878732 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 449087020637) ^ 36676 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_648470840627 : Nat.Prime 648470840627 := by
  apply lucas_primality 648470840627 (2 : ZMod 648470840627)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (173, 1), (267741883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (173, 1), (267741883, 1)] : List FactorBlock).map factorBlockValue).prod) = 648470840627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_173
      · exact prime_oneHundredFiftyNineFA_267741883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 648470840627) ^ 324235420313 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 648470840627) ^ 92638691518 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 648470840627) ^ 3748386362 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 648470840627) ^ 2422 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_697714190897 : Nat.Prime 697714190897 := by
  apply lucas_primality 697714190897 (3 : ZMod 697714190897)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (101, 1), (1871, 1), (230761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (101, 1), (1871, 1), (230761, 1)] : List FactorBlock).map factorBlockValue).prod) = 697714190897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_101
      · exact prime_oneHundredFiftyNineFA_1871
      · exact prime_oneHundredFiftyNineFA_230761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 697714190897) ^ 348857095448 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 697714190897) ^ 6908061296 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 697714190897) ^ 372909776 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 697714190897) ^ 3023536 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_886166400859 : Nat.Prime 886166400859 := by
  apply lucas_primality 886166400859 (2 : ZMod 886166400859)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (293, 1), (1601, 1), (314851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (293, 1), (1601, 1), (314851, 1)] : List FactorBlock).map factorBlockValue).prod) = 886166400859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_293
      · exact prime_oneHundredFiftyNineFA_1601
      · exact prime_oneHundredFiftyNineFA_314851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 886166400859) ^ 443083200429 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 886166400859) ^ 295388800286 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 886166400859) ^ 3024458706 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 886166400859) ^ 553508058 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 886166400859) ^ 2814558 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_920427376933 : Nat.Prime 920427376933 := by
  apply lucas_primality 920427376933 (14 : ZMod 920427376933)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (277, 1), (13185883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (277, 1), (13185883, 1)] : List FactorBlock).map factorBlockValue).prod) = 920427376933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_277
      · exact prime_oneHundredFiftyNineFA_13185883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 920427376933) ^ 460213688466 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (14 : ZMod 920427376933) ^ 306809125644 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (14 : ZMod 920427376933) ^ 131489625276 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (14 : ZMod 920427376933) ^ 3322842516 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (14 : ZMod 920427376933) ^ 69804 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_1007290806703 : Nat.Prime 1007290806703 := by
  apply lucas_primality 1007290806703 (3 : ZMod 1007290806703)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (487, 1), (344726491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (487, 1), (344726491, 1)] : List FactorBlock).map factorBlockValue).prod) = 1007290806703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_487
      · exact prime_oneHundredFiftyNineFA_344726491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1007290806703) ^ 503645403351 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1007290806703) ^ 335763602234 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1007290806703) ^ 2068358946 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1007290806703) ^ 2922 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_1198484838211 : Nat.Prime 1198484838211 := by
  apply lucas_primality 1198484838211 (2 : ZMod 1198484838211)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (17, 1), (6311, 1), (33851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (17, 1), (6311, 1), (33851, 1)] : List FactorBlock).map factorBlockValue).prod) = 1198484838211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_11
      · exact prime_oneHundredFiftyNineFA_17
      · exact prime_oneHundredFiftyNineFA_6311
      · exact prime_oneHundredFiftyNineFA_33851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1198484838211) ^ 599242419105 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1198484838211) ^ 399494946070 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1198484838211) ^ 239696967642 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1198484838211) ^ 108953167110 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1198484838211) ^ 70499108130 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1198484838211) ^ 189904110 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1198484838211) ^ 35404710 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_1566517818589 : Nat.Prime 1566517818589 := by
  apply lucas_primality 1566517818589 (2 : ZMod 1566517818589)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (67, 1), (1948405247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (67, 1), (1948405247, 1)] : List FactorBlock).map factorBlockValue).prod) = 1566517818589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_67
      · exact prime_oneHundredFiftyNineFA_1948405247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1566517818589) ^ 783258909294 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1566517818589) ^ 522172606196 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1566517818589) ^ 23380862964 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1566517818589) ^ 804 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_1654807199021 : Nat.Prime 1654807199021 := by
  apply lucas_primality 1654807199021 (3 : ZMod 1654807199021)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (53, 1), (293, 1), (5328119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (53, 1), (293, 1), (5328119, 1)] : List FactorBlock).map factorBlockValue).prod) = 1654807199021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_53
      · exact prime_oneHundredFiftyNineFA_293
      · exact prime_oneHundredFiftyNineFA_5328119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1654807199021) ^ 827403599510 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1654807199021) ^ 330961439804 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1654807199021) ^ 31222777340 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1654807199021) ^ 5647806140 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1654807199021) ^ 310580 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_1843578322123 : Nat.Prime 1843578322123 := by
  apply lucas_primality 1843578322123 (14 : ZMod 1843578322123)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (479, 1), (641467753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (479, 1), (641467753, 1)] : List FactorBlock).map factorBlockValue).prod) = 1843578322123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_479
      · exact prime_oneHundredFiftyNineFA_641467753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 1843578322123) ^ 921789161061 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (14 : ZMod 1843578322123) ^ 614526107374 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (14 : ZMod 1843578322123) ^ 3848806518 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (14 : ZMod 1843578322123) ^ 2874 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_1852985661431 : Nat.Prime 1852985661431 := by
  apply lucas_primality 1852985661431 (7 : ZMod 1852985661431)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (41, 1), (1237, 1), (3653579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (41, 1), (1237, 1), (3653579, 1)] : List FactorBlock).map factorBlockValue).prod) = 1852985661431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_41
      · exact prime_oneHundredFiftyNineFA_1237
      · exact prime_oneHundredFiftyNineFA_3653579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1852985661431) ^ 926492830715 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 1852985661431) ^ 370597132286 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 1852985661431) ^ 45194772230 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 1852985661431) ^ 1497967390 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 1852985661431) ^ 507170 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_2042200077481 : Nat.Prime 2042200077481 := by
  apply lucas_primality 2042200077481 (26 : ZMod 2042200077481)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (2069, 1), (2741797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (2069, 1), (2741797, 1)] : List FactorBlock).map factorBlockValue).prod) = 2042200077481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_2069
      · exact prime_oneHundredFiftyNineFA_2741797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 2042200077481) ^ 1021100038740 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (26 : ZMod 2042200077481) ^ 680733359160 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (26 : ZMod 2042200077481) ^ 408440015496 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (26 : ZMod 2042200077481) ^ 987046920 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (26 : ZMod 2042200077481) ^ 744840 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_2174508912049 : Nat.Prime 2174508912049 := by
  apply lucas_primality 2174508912049 (7 : ZMod 2174508912049)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (11, 1), (17, 1), (242258123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (11, 1), (17, 1), (242258123, 1)] : List FactorBlock).map factorBlockValue).prod) = 2174508912049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_11
      · exact prime_oneHundredFiftyNineFA_17
      · exact prime_oneHundredFiftyNineFA_242258123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2174508912049) ^ 1087254456024 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 2174508912049) ^ 724836304016 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 2174508912049) ^ 197682628368 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 2174508912049) ^ 127912288944 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 2174508912049) ^ 8976 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_2788305715133 : Nat.Prime 2788305715133 := by
  apply lucas_primality 2788305715133 (2 : ZMod 2788305715133)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (347, 1), (463, 1), (88547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (347, 1), (463, 1), (88547, 1)] : List FactorBlock).map factorBlockValue).prod) = 2788305715133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_347
      · exact prime_oneHundredFiftyNineFA_463
      · exact prime_oneHundredFiftyNineFA_88547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2788305715133) ^ 1394152857566 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2788305715133) ^ 398329387876 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2788305715133) ^ 8035463156 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2788305715133) ^ 6022258564 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2788305715133) ^ 31489556 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_2809610191499 : Nat.Prime 2809610191499 := by
  apply lucas_primality 2809610191499 (2 : ZMod 2809610191499)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 2), (11609959469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 2), (11609959469, 1)] : List FactorBlock).map factorBlockValue).prod) = 2809610191499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_11
      · exact prime_oneHundredFiftyNineFA_11609959469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2809610191499) ^ 1404805095749 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2809610191499) ^ 255419108318 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2809610191499) ^ 242 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_3094799945617 : Nat.Prime 3094799945617 := by
  apply lucas_primality 3094799945617 (5 : ZMod 3094799945617)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (19, 1), (29, 1), (1171, 1), (3701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (19, 1), (29, 1), (1171, 1), (3701, 1)] : List FactorBlock).map factorBlockValue).prod) = 3094799945617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_19
      · exact prime_oneHundredFiftyNineFA_29
      · exact prime_oneHundredFiftyNineFA_1171
      · exact prime_oneHundredFiftyNineFA_3701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3094799945617) ^ 1547399972808 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 3094799945617) ^ 1031599981872 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 3094799945617) ^ 162884207664 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 3094799945617) ^ 106717239504 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 3094799945617) ^ 2642869296 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 3094799945617) ^ 836206416 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_3231185881793 : Nat.Prime 3231185881793 := by
  apply lucas_primality 3231185881793 (3 : ZMod 3231185881793)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (11, 2), (417250243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (11, 2), (417250243, 1)] : List FactorBlock).map factorBlockValue).prod) = 3231185881793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_11
      · exact prime_oneHundredFiftyNineFA_417250243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3231185881793) ^ 1615592940896 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 3231185881793) ^ 293744171072 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 3231185881793) ^ 7744 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_3800606335681 : Nat.Prime 3800606335681 := by
  apply lucas_primality 3800606335681 (37 : ZMod 3800606335681)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (7, 1), (11, 1), (51415129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (7, 1), (11, 1), (51415129, 1)] : List FactorBlock).map factorBlockValue).prod) = 3800606335681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_11
      · exact prime_oneHundredFiftyNineFA_51415129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (37 : ZMod 3800606335681) ^ 1900303167840 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (37 : ZMod 3800606335681) ^ 1266868778560 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (37 : ZMod 3800606335681) ^ 760121267136 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (37 : ZMod 3800606335681) ^ 542943762240 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (37 : ZMod 3800606335681) ^ 345509666880 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (37 : ZMod 3800606335681) ^ 73920 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_4595440430387 : Nat.Prime 4595440430387 := by
  apply lucas_primality 4595440430387 (2 : ZMod 4595440430387)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (59, 2), (127, 1), (173, 1), (2311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (59, 2), (127, 1), (173, 1), (2311, 1)] : List FactorBlock).map factorBlockValue).prod) = 4595440430387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_13
      · exact prime_oneHundredFiftyNineFA_59
      · exact prime_oneHundredFiftyNineFA_127
      · exact prime_oneHundredFiftyNineFA_173
      · exact prime_oneHundredFiftyNineFA_2311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4595440430387) ^ 2297720215193 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4595440430387) ^ 353495417722 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4595440430387) ^ 77888820854 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4595440430387) ^ 36184570318 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4595440430387) ^ 26563239482 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4595440430387) ^ 1988507326 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_5542245236371 : Nat.Prime 5542245236371 := by
  apply lucas_primality 5542245236371 (2 : ZMod 5542245236371)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (23, 1), (33941, 1), (236653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (23, 1), (33941, 1), (236653, 1)] : List FactorBlock).map factorBlockValue).prod) = 5542245236371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_23
      · exact prime_oneHundredFiftyNineFA_33941
      · exact prime_oneHundredFiftyNineFA_236653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5542245236371) ^ 2771122618185 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5542245236371) ^ 1847415078790 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5542245236371) ^ 1108449047274 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5542245236371) ^ 240967184190 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5542245236371) ^ 163290570 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5542245236371) ^ 23419290 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_6914126395331 : Nat.Prime 6914126395331 := by
  apply lucas_primality 6914126395331 (2 : ZMod 6914126395331)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (11, 1), (73, 1), (6373, 1), (19301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (11, 1), (73, 1), (6373, 1), (19301, 1)] : List FactorBlock).map factorBlockValue).prod) = 6914126395331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_11
      · exact prime_oneHundredFiftyNineFA_73
      · exact prime_oneHundredFiftyNineFA_6373
      · exact prime_oneHundredFiftyNineFA_19301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6914126395331) ^ 3457063197665 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 6914126395331) ^ 1382825279066 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 6914126395331) ^ 987732342190 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 6914126395331) ^ 628556945030 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 6914126395331) ^ 94714060210 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 6914126395331) ^ 1084909210 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 6914126395331) ^ 358226330 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_7020206314049 : Nat.Prime 7020206314049 := by
  apply lucas_primality 7020206314049 (3 : ZMod 7020206314049)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (521, 1), (12973, 1), (16229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (521, 1), (12973, 1), (16229, 1)] : List FactorBlock).map factorBlockValue).prod) = 7020206314049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_521
      · exact prime_oneHundredFiftyNineFA_12973
      · exact prime_oneHundredFiftyNineFA_16229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7020206314049) ^ 3510103157024 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 7020206314049) ^ 13474484288 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 7020206314049) ^ 541139776 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 7020206314049) ^ 432571712 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_7998040021757 : Nat.Prime 7998040021757 := by
  apply lucas_primality 7998040021757 (2 : ZMod 7998040021757)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (67, 1), (461, 1), (3547, 1), (18251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (67, 1), (461, 1), (3547, 1), (18251, 1)] : List FactorBlock).map factorBlockValue).prod) = 7998040021757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_67
      · exact prime_oneHundredFiftyNineFA_461
      · exact prime_oneHundredFiftyNineFA_3547
      · exact prime_oneHundredFiftyNineFA_18251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7998040021757) ^ 3999020010878 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 7998040021757) ^ 119373731668 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 7998040021757) ^ 17349327596 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 7998040021757) ^ 2254874548 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 7998040021757) ^ 438224756 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_11364481303667 : Nat.Prime 11364481303667 := by
  apply lucas_primality 11364481303667 (2 : ZMod 11364481303667)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (14407, 1), (12722849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (14407, 1), (12722849, 1)] : List FactorBlock).map factorBlockValue).prod) = 11364481303667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_31
      · exact prime_oneHundredFiftyNineFA_14407
      · exact prime_oneHundredFiftyNineFA_12722849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11364481303667) ^ 5682240651833 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 11364481303667) ^ 366596171086 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 11364481303667) ^ 788816638 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 11364481303667) ^ 893234 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_15902382581257 : Nat.Prime 15902382581257 := by
  apply lucas_primality 15902382581257 (10 : ZMod 15902382581257)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (12413, 1), (53379463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (12413, 1), (53379463, 1)] : List FactorBlock).map factorBlockValue).prod) = 15902382581257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_12413
      · exact prime_oneHundredFiftyNineFA_53379463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 15902382581257) ^ 7951191290628 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (10 : ZMod 15902382581257) ^ 5300794193752 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (10 : ZMod 15902382581257) ^ 1281107112 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (10 : ZMod 15902382581257) ^ 297912 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_16491666006401 : Nat.Prime 16491666006401 := by
  apply lucas_primality 16491666006401 (3 : ZMod 16491666006401)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 2), (13, 1), (23, 1), (17236273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 2), (13, 1), (23, 1), (17236273, 1)] : List FactorBlock).map factorBlockValue).prod) = 16491666006401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_13
      · exact prime_oneHundredFiftyNineFA_23
      · exact prime_oneHundredFiftyNineFA_17236273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 16491666006401) ^ 8245833003200 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 16491666006401) ^ 3298333201280 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 16491666006401) ^ 1268589692800 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 16491666006401) ^ 717028956800 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 16491666006401) ^ 956800 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_22745927311337 : Nat.Prime 22745927311337 := by
  apply lucas_primality 22745927311337 (3 : ZMod 22745927311337)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (43, 1), (67, 1), (499, 1), (1977743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (43, 1), (67, 1), (499, 1), (1977743, 1)] : List FactorBlock).map factorBlockValue).prod) = 22745927311337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_43
      · exact prime_oneHundredFiftyNineFA_67
      · exact prime_oneHundredFiftyNineFA_499
      · exact prime_oneHundredFiftyNineFA_1977743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 22745927311337) ^ 11372963655668 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 22745927311337) ^ 528975053752 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 22745927311337) ^ 339491452408 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 22745927311337) ^ 45583020664 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 22745927311337) ^ 11500952 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_26536706602061 : Nat.Prime 26536706602061 := by
  apply lucas_primality 26536706602061 (2 : ZMod 26536706602061)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (191, 1), (6946781833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (191, 1), (6946781833, 1)] : List FactorBlock).map factorBlockValue).prod) = 26536706602061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_191
      · exact prime_oneHundredFiftyNineFA_6946781833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 26536706602061) ^ 13268353301030 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 26536706602061) ^ 5307341320412 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 26536706602061) ^ 138935636660 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 26536706602061) ^ 3820 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_31440271855879 : Nat.Prime 31440271855879 := by
  apply lucas_primality 31440271855879 (3 : ZMod 31440271855879)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (53, 1), (44699, 1), (737293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (53, 1), (44699, 1), (737293, 1)] : List FactorBlock).map factorBlockValue).prod) = 31440271855879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_53
      · exact prime_oneHundredFiftyNineFA_44699
      · exact prime_oneHundredFiftyNineFA_737293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 31440271855879) ^ 15720135927939 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 31440271855879) ^ 10480090618626 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 31440271855879) ^ 593212676526 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 31440271855879) ^ 703377522 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 31440271855879) ^ 42642846 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_36844185754483 : Nat.Prime 36844185754483 := by
  apply lucas_primality 36844185754483 (2 : ZMod 36844185754483)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (79, 1), (163, 1), (11090077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (79, 1), (163, 1), (11090077, 1)] : List FactorBlock).map factorBlockValue).prod) = 36844185754483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_43
      · exact prime_oneHundredFiftyNineFA_79
      · exact prime_oneHundredFiftyNineFA_163
      · exact prime_oneHundredFiftyNineFA_11090077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 36844185754483) ^ 18422092877241 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 36844185754483) ^ 12281395251494 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 36844185754483) ^ 856841529174 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 36844185754483) ^ 466382098158 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 36844185754483) ^ 226037949414 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 36844185754483) ^ 3322266 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_44913948161041 : Nat.Prime 44913948161041 := by
  apply lucas_primality 44913948161041 (23 : ZMod 44913948161041)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5, 1), (7, 3), (47, 1), (1289839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5, 1), (7, 3), (47, 1), (1289839, 1)] : List FactorBlock).map factorBlockValue).prod) = 44913948161041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_47
      · exact prime_oneHundredFiftyNineFA_1289839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 44913948161041) ^ 22456974080520 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (23 : ZMod 44913948161041) ^ 14971316053680 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (23 : ZMod 44913948161041) ^ 8982789632208 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (23 : ZMod 44913948161041) ^ 6416278308720 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (23 : ZMod 44913948161041) ^ 955615918320 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (23 : ZMod 44913948161041) ^ 34821360 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_45752552594669 : Nat.Prime 45752552594669 := by
  apply lucas_primality 45752552594669 (2 : ZMod 45752552594669)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) = 45752552594669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_47
      · exact prime_oneHundredFiftyNineFA_243364641461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 45752552594669) ^ 22876276297334 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 973458565844 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 188 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_49069275802777 : Nat.Prime 49069275802777 := by
  apply lucas_primality 49069275802777 (5 : ZMod 49069275802777)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (19, 1), (73, 1), (769, 1), (212987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (19, 1), (73, 1), (769, 1), (212987, 1)] : List FactorBlock).map factorBlockValue).prod) = 49069275802777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_19
      · exact prime_oneHundredFiftyNineFA_73
      · exact prime_oneHundredFiftyNineFA_769
      · exact prime_oneHundredFiftyNineFA_212987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 49069275802777) ^ 24534637901388 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 49069275802777) ^ 16356425267592 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 49069275802777) ^ 2582593463304 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 49069275802777) ^ 672181860312 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 49069275802777) ^ 63809201304 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 49069275802777) ^ 230386248 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_56171285512819 : Nat.Prime 56171285512819 := by
  apply lucas_primality 56171285512819 (2 : ZMod 56171285512819)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (79, 1), (277, 1), (463, 1), (132001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (79, 1), (277, 1), (463, 1), (132001, 1)] : List FactorBlock).map factorBlockValue).prod) = 56171285512819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_79
      · exact prime_oneHundredFiftyNineFA_277
      · exact prime_oneHundredFiftyNineFA_463
      · exact prime_oneHundredFiftyNineFA_132001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 56171285512819) ^ 28085642756409 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 56171285512819) ^ 18723761837606 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 56171285512819) ^ 8024469358974 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 56171285512819) ^ 711028930542 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 56171285512819) ^ 202784424234 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 56171285512819) ^ 121320271086 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 56171285512819) ^ 425536818 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_62219975203933 : Nat.Prime 62219975203933 := by
  apply lucas_primality 62219975203933 (14 : ZMod 62219975203933)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (13, 1), (89, 1), (640202239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (13, 1), (89, 1), (640202239, 1)] : List FactorBlock).map factorBlockValue).prod) = 62219975203933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_13
      · exact prime_oneHundredFiftyNineFA_89
      · exact prime_oneHundredFiftyNineFA_640202239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 62219975203933) ^ 31109987601966 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (14 : ZMod 62219975203933) ^ 20739991734644 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (14 : ZMod 62219975203933) ^ 8888567886276 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (14 : ZMod 62219975203933) ^ 4786151938764 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (14 : ZMod 62219975203933) ^ 699100844988 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (14 : ZMod 62219975203933) ^ 97188 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_66260726117293 : Nat.Prime 66260726117293 := by
  apply lucas_primality 66260726117293 (2 : ZMod 66260726117293)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (19793, 1), (39853391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (19793, 1), (39853391, 1)] : List FactorBlock).map factorBlockValue).prod) = 66260726117293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_19793
      · exact prime_oneHundredFiftyNineFA_39853391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 66260726117293) ^ 33130363058646 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 66260726117293) ^ 22086908705764 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 66260726117293) ^ 9465818016756 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 66260726117293) ^ 3347684844 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 66260726117293) ^ 1662612 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_71479381476463 : Nat.Prime 71479381476463 := by
  apply lucas_primality 71479381476463 (5 : ZMod 71479381476463)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (811, 1), (14689556407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (811, 1), (14689556407, 1)] : List FactorBlock).map factorBlockValue).prod) = 71479381476463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_811
      · exact prime_oneHundredFiftyNineFA_14689556407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 71479381476463) ^ 35739690738231 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 71479381476463) ^ 23826460492154 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 71479381476463) ^ 88137338442 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 71479381476463) ^ 4866 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_91044981601837 : Nat.Prime 91044981601837 := by
  apply lucas_primality 91044981601837 (5 : ZMod 91044981601837)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (37, 1), (103, 1), (131, 1), (479, 1), (31727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (37, 1), (103, 1), (131, 1), (479, 1), (31727, 1)] : List FactorBlock).map factorBlockValue).prod) = 91044981601837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_37
      · exact prime_oneHundredFiftyNineFA_103
      · exact prime_oneHundredFiftyNineFA_131
      · exact prime_oneHundredFiftyNineFA_479
      · exact prime_oneHundredFiftyNineFA_31727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 91044981601837) ^ 45522490800918 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 91044981601837) ^ 30348327200612 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 91044981601837) ^ 2460675178428 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 91044981601837) ^ 883931860212 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 91044981601837) ^ 694999859556 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 91044981601837) ^ 190073030484 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 91044981601837) ^ 2869637268 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_113074463426549 : Nat.Prime 113074463426549 := by
  apply lucas_primality 113074463426549 (2 : ZMod 113074463426549)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (2174508912049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (2174508912049, 1)] : List FactorBlock).map factorBlockValue).prod) = 113074463426549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_13
      · exact prime_oneHundredFiftyNineFA_2174508912049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 113074463426549) ^ 56537231713274 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 113074463426549) ^ 8698035648196 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 113074463426549) ^ 52 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_140287963500577 : Nat.Prime 140287963500577 := by
  apply lucas_primality 140287963500577 (5 : ZMod 140287963500577)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (823, 1), (591872399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (823, 1), (591872399, 1)] : List FactorBlock).map factorBlockValue).prod) = 140287963500577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_823
      · exact prime_oneHundredFiftyNineFA_591872399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 140287963500577) ^ 70143981750288 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 140287963500577) ^ 46762654500192 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 140287963500577) ^ 170459250912 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 140287963500577) ^ 237024 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_147906298737313 : Nat.Prime 147906298737313 := by
  apply lucas_primality 147906298737313 (5 : ZMod 147906298737313)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (43, 1), (131, 1), (337, 1), (811607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (43, 1), (131, 1), (337, 1), (811607, 1)] : List FactorBlock).map factorBlockValue).prod) = 147906298737313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_43
      · exact prime_oneHundredFiftyNineFA_131
      · exact prime_oneHundredFiftyNineFA_337
      · exact prime_oneHundredFiftyNineFA_811607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 147906298737313) ^ 73953149368656 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 147906298737313) ^ 49302099579104 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 147906298737313) ^ 3439681365984 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 147906298737313) ^ 1129055715552 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 147906298737313) ^ 438891094176 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 147906298737313) ^ 182238816 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_190220427427301 : Nat.Prime 190220427427301 := by
  apply lucas_primality 190220427427301 (3 : ZMod 190220427427301)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (29, 1), (65593250837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (29, 1), (65593250837, 1)] : List FactorBlock).map factorBlockValue).prod) = 190220427427301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_29
      · exact prime_oneHundredFiftyNineFA_65593250837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 190220427427301) ^ 95110213713650 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 190220427427301) ^ 38044085485460 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 190220427427301) ^ 6559325083700 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 190220427427301) ^ 2900 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_226148926853099 : Nat.Prime 226148926853099 := by
  apply lucas_primality 226148926853099 (2 : ZMod 226148926853099)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (113074463426549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (113074463426549, 1)] : List FactorBlock).map factorBlockValue).prod) = 226148926853099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_113074463426549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 226148926853099) ^ 113074463426549 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 226148926853099) ^ 2 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_306139289307503 : Nat.Prime 306139289307503 := by
  apply lucas_primality 306139289307503 (5 : ZMod 306139289307503)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (71, 1), (3217, 1), (95737399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (71, 1), (3217, 1), (95737399, 1)] : List FactorBlock).map factorBlockValue).prod) = 306139289307503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_71
      · exact prime_oneHundredFiftyNineFA_3217
      · exact prime_oneHundredFiftyNineFA_95737399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 306139289307503) ^ 153069644653751 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 306139289307503) ^ 43734184186786 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 306139289307503) ^ 4311820976162 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 306139289307503) ^ 95162974606 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 306139289307503) ^ 3197698 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_332054436000041 : Nat.Prime 332054436000041 := by
  apply lucas_primality 332054436000041 (3 : ZMod 332054436000041)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (19, 1), (79259, 1), (424037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (19, 1), (79259, 1), (424037, 1)] : List FactorBlock).map factorBlockValue).prod) = 332054436000041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_13
      · exact prime_oneHundredFiftyNineFA_19
      · exact prime_oneHundredFiftyNineFA_79259
      · exact prime_oneHundredFiftyNineFA_424037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 332054436000041) ^ 166027218000020 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 332054436000041) ^ 66410887200008 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 332054436000041) ^ 25542648923080 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 332054436000041) ^ 17476549263160 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 332054436000041) ^ 4189485560 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 332054436000041) ^ 783078920 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_366020420757353 : Nat.Prime 366020420757353 := by
  apply lucas_primality 366020420757353 (3 : ZMod 366020420757353)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) = 366020420757353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_45752552594669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 366020420757353) ^ 183010210378676 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 366020420757353) ^ 8 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_381369995496449 : Nat.Prime 381369995496449 := by
  apply lucas_primality 381369995496449 (6 : ZMod 381369995496449)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (7, 1), (151, 1), (227, 1), (449, 1), (3457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (7, 1), (151, 1), (227, 1), (449, 1), (3457, 1)] : List FactorBlock).map factorBlockValue).prod) = 381369995496449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_151
      · exact prime_oneHundredFiftyNineFA_227
      · exact prime_oneHundredFiftyNineFA_449
      · exact prime_oneHundredFiftyNineFA_3457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 381369995496449) ^ 190684997748224 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (6 : ZMod 381369995496449) ^ 54481427928064 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (6 : ZMod 381369995496449) ^ 2525629109248 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (6 : ZMod 381369995496449) ^ 1680044033024 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (6 : ZMod 381369995496449) ^ 849376381952 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (6 : ZMod 381369995496449) ^ 110318193664 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_562154279761651 : Nat.Prime 562154279761651 := by
  apply lucas_primality 562154279761651 (3 : ZMod 562154279761651)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (283, 1), (67129, 1), (197273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (283, 1), (67129, 1), (197273, 1)] : List FactorBlock).map factorBlockValue).prod) = 562154279761651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_283
      · exact prime_oneHundredFiftyNineFA_67129
      · exact prime_oneHundredFiftyNineFA_197273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 562154279761651) ^ 281077139880825 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 562154279761651) ^ 187384759920550 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 562154279761651) ^ 112430855952330 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 562154279761651) ^ 1986410882550 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 562154279761651) ^ 8374238850 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 562154279761651) ^ 2849626050 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_576818225471149 : Nat.Prime 576818225471149 := by
  apply lucas_primality 576818225471149 (2 : ZMod 576818225471149)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (5179, 1), (545962603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (5179, 1), (545962603, 1)] : List FactorBlock).map factorBlockValue).prod) = 576818225471149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_17
      · exact prime_oneHundredFiftyNineFA_5179
      · exact prime_oneHundredFiftyNineFA_545962603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 576818225471149) ^ 288409112735574 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 576818225471149) ^ 192272741823716 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 576818225471149) ^ 33930483851244 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 576818225471149) ^ 111376371012 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 576818225471149) ^ 1056516 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_762739990992899 : Nat.Prime 762739990992899 := by
  apply lucas_primality 762739990992899 (2 : ZMod 762739990992899)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (381369995496449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (381369995496449, 1)] : List FactorBlock).map factorBlockValue).prod) = 762739990992899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_381369995496449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 762739990992899) ^ 381369995496449 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 762739990992899) ^ 2 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_953098149107887 : Nat.Prime 953098149107887 := by
  apply lucas_primality 953098149107887 (5 : ZMod 953098149107887)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4065767, 1), (39070043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4065767, 1), (39070043, 1)] : List FactorBlock).map factorBlockValue).prod) = 953098149107887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_4065767
      · exact prime_oneHundredFiftyNineFA_39070043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 953098149107887) ^ 476549074553943 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 953098149107887) ^ 317699383035962 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 953098149107887) ^ 234420258 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 953098149107887) ^ 24394602 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_1411929592882729 : Nat.Prime 1411929592882729 := by
  apply lucas_primality 1411929592882729 (11 : ZMod 1411929592882729)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (131, 1), (449087020637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (131, 1), (449087020637, 1)] : List FactorBlock).map factorBlockValue).prod) = 1411929592882729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_131
      · exact prime_oneHundredFiftyNineFA_449087020637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 1411929592882729) ^ 705964796441364 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (11 : ZMod 1411929592882729) ^ 470643197627576 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (11 : ZMod 1411929592882729) ^ 10778088495288 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (11 : ZMod 1411929592882729) ^ 3144 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_1509133049082193 : Nat.Prime 1509133049082193 := by
  apply lucas_primality 1509133049082193 (5 : ZMod 1509133049082193)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (31440271855879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (31440271855879, 1)] : List FactorBlock).map factorBlockValue).prod) = 1509133049082193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_31440271855879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1509133049082193) ^ 754566524541096 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1509133049082193) ^ 503044349694064 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1509133049082193) ^ 48 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_3293757650744591 : Nat.Prime 3293757650744591 := by
  apply lucas_primality 3293757650744591 (7 : ZMod 3293757650744591)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (377393, 1), (872765963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (377393, 1), (872765963, 1)] : List FactorBlock).map factorBlockValue).prod) = 3293757650744591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_377393
      · exact prime_oneHundredFiftyNineFA_872765963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 3293757650744591) ^ 1646878825372295 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 3293757650744591) ^ 658751530148918 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 3293757650744591) ^ 8727659630 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 3293757650744591) ^ 3773930 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_3463258354190329 : Nat.Prime 3463258354190329 := by
  apply lucas_primality 3463258354190329 (11 : ZMod 3463258354190329)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (29, 1), (307423, 1), (16185991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (29, 1), (307423, 1), (16185991, 1)] : List FactorBlock).map factorBlockValue).prod) = 3463258354190329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_29
      · exact prime_oneHundredFiftyNineFA_307423
      · exact prime_oneHundredFiftyNineFA_16185991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 3463258354190329) ^ 1731629177095164 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (11 : ZMod 3463258354190329) ^ 1154419451396776 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (11 : ZMod 3463258354190329) ^ 119422701868632 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (11 : ZMod 3463258354190329) ^ 11265449736 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (11 : ZMod 3463258354190329) ^ 213966408 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_5503907143145219 : Nat.Prime 5503907143145219 := by
  apply lucas_primality 5503907143145219 (2 : ZMod 5503907143145219)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (193, 1), (349, 1), (79357, 1), (514841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (193, 1), (349, 1), (79357, 1), (514841, 1)] : List FactorBlock).map factorBlockValue).prod) = 5503907143145219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_193
      · exact prime_oneHundredFiftyNineFA_349
      · exact prime_oneHundredFiftyNineFA_79357
      · exact prime_oneHundredFiftyNineFA_514841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5503907143145219) ^ 2751953571572609 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5503907143145219) ^ 28517653591426 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5503907143145219) ^ 15770507573482 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5503907143145219) ^ 69356290474 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5503907143145219) ^ 10690498898 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_6209783323944127 : Nat.Prime 6209783323944127 := by
  apply lucas_primality 6209783323944127 (5 : ZMod 6209783323944127)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (349, 1), (10433, 1), (284243513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (349, 1), (10433, 1), (284243513, 1)] : List FactorBlock).map factorBlockValue).prod) = 6209783323944127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_349
      · exact prime_oneHundredFiftyNineFA_10433
      · exact prime_oneHundredFiftyNineFA_284243513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6209783323944127) ^ 3104891661972063 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 6209783323944127) ^ 2069927774648042 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 6209783323944127) ^ 17793075426774 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 6209783323944127) ^ 595205916222 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 6209783323944127) ^ 21846702 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_7934570924686361 : Nat.Prime 7934570924686361 := by
  apply lucas_primality 7934570924686361 (3 : ZMod 7934570924686361)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (787, 1), (7321, 1), (34428517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (787, 1), (7321, 1), (34428517, 1)] : List FactorBlock).map factorBlockValue).prod) = 7934570924686361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_787
      · exact prime_oneHundredFiftyNineFA_7321
      · exact prime_oneHundredFiftyNineFA_34428517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7934570924686361) ^ 3967285462343180 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 7934570924686361) ^ 1586914184937272 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 7934570924686361) ^ 10082046918280 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 7934570924686361) ^ 1083809715160 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 7934570924686361) ^ 230465080 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_21163655729137391 : Nat.Prime 21163655729137391 := by
  apply lucas_primality 21163655729137391 (7 : ZMod 21163655729137391)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (193, 1), (1566517818589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (193, 1), (1566517818589, 1)] : List FactorBlock).map factorBlockValue).prod) = 21163655729137391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_193
      · exact prime_oneHundredFiftyNineFA_1566517818589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 21163655729137391) ^ 10581827864568695 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 21163655729137391) ^ 4232731145827478 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 21163655729137391) ^ 3023379389876770 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 21163655729137391) ^ 109656247301230 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 21163655729137391) ^ 13510 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_23747034664190251 : Nat.Prime 23747034664190251 := by
  apply lucas_primality 23747034664190251 (10 : ZMod 23747034664190251)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 3), (7, 1), (1933, 1), (780004259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 3), (7, 1), (1933, 1), (780004259, 1)] : List FactorBlock).map factorBlockValue).prod) = 23747034664190251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_1933
      · exact prime_oneHundredFiftyNineFA_780004259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 23747034664190251) ^ 11873517332095125 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (10 : ZMod 23747034664190251) ^ 7915678221396750 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (10 : ZMod 23747034664190251) ^ 4749406932838050 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (10 : ZMod 23747034664190251) ^ 3392433523455750 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (10 : ZMod 23747034664190251) ^ 12285067079250 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (10 : ZMod 23747034664190251) ^ 30444750 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_32209181421770699 : Nat.Prime 32209181421770699 := by
  apply lucas_primality 32209181421770699 (2 : ZMod 32209181421770699)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (257, 1), (461, 1), (7995888361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (257, 1), (461, 1), (7995888361, 1)] : List FactorBlock).map factorBlockValue).prod) = 32209181421770699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_17
      · exact prime_oneHundredFiftyNineFA_257
      · exact prime_oneHundredFiftyNineFA_461
      · exact prime_oneHundredFiftyNineFA_7995888361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 32209181421770699) ^ 16104590710885349 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 32209181421770699) ^ 1894657730692394 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 32209181421770699) ^ 125327554170314 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 32209181421770699) ^ 69868072498418 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 32209181421770699) ^ 4028218 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_32795840804090437 : Nat.Prime 32795840804090437 := by
  apply lucas_primality 32795840804090437 (5 : ZMod 32795840804090437)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (37, 1), (281, 1), (1621, 1), (18017891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (37, 1), (281, 1), (1621, 1), (18017891, 1)] : List FactorBlock).map factorBlockValue).prod) = 32795840804090437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_37
      · exact prime_oneHundredFiftyNineFA_281
      · exact prime_oneHundredFiftyNineFA_1621
      · exact prime_oneHundredFiftyNineFA_18017891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 32795840804090437) ^ 16397920402045218 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 32795840804090437) ^ 10931946934696812 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 32795840804090437) ^ 886374075786228 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 32795840804090437) ^ 116711177238756 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 32795840804090437) ^ 20231857374516 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 32795840804090437) ^ 1820181996 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_33823354021088083 : Nat.Prime 33823354021088083 := by
  apply lucas_primality 33823354021088083 (2 : ZMod 33823354021088083)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (73, 1), (7020206314049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (73, 1), (7020206314049, 1)] : List FactorBlock).map factorBlockValue).prod) = 33823354021088083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_11
      · exact prime_oneHundredFiftyNineFA_73
      · exact prime_oneHundredFiftyNineFA_7020206314049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 33823354021088083) ^ 16911677010544041 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 33823354021088083) ^ 11274451340362694 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 33823354021088083) ^ 3074850365553462 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 33823354021088083) ^ 463333616727234 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 33823354021088083) ^ 4818 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_34516943995193707 : Nat.Prime 34516943995193707 := by
  apply lucas_primality 34516943995193707 (2 : ZMod 34516943995193707)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (6827, 1), (120691, 1), (6981943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (6827, 1), (120691, 1), (6981943, 1)] : List FactorBlock).map factorBlockValue).prod) = 34516943995193707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_6827
      · exact prime_oneHundredFiftyNineFA_120691
      · exact prime_oneHundredFiftyNineFA_6981943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 34516943995193707) ^ 17258471997596853 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 34516943995193707) ^ 11505647998397902 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 34516943995193707) ^ 5055946095678 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 34516943995193707) ^ 285994349166 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 34516943995193707) ^ 4943744742 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_42219111271378541 : Nat.Prime 42219111271378541 := by
  apply lucas_primality 42219111271378541 (2 : ZMod 42219111271378541)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (47, 1), (44913948161041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (47, 1), (44913948161041, 1)] : List FactorBlock).map factorBlockValue).prod) = 42219111271378541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_47
      · exact prime_oneHundredFiftyNineFA_44913948161041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 42219111271378541) ^ 21109555635689270 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 42219111271378541) ^ 8443822254275708 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 42219111271378541) ^ 898278963220820 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 42219111271378541) ^ 940 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_47607425548118167 : Nat.Prime 47607425548118167 := by
  apply lucas_primality 47607425548118167 (3 : ZMod 47607425548118167)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7934570924686361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7934570924686361, 1)] : List FactorBlock).map factorBlockValue).prod) = 47607425548118167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_7934570924686361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 47607425548118167) ^ 23803712774059083 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 47607425548118167) ^ 15869141849372722 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 47607425548118167) ^ 6 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_56053603459682809 : Nat.Prime 56053603459682809 := by
  apply lucas_primality 56053603459682809 (13 : ZMod 56053603459682809)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (293, 1), (421, 1), (2704858427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (293, 1), (421, 1), (2704858427, 1)] : List FactorBlock).map factorBlockValue).prod) = 56053603459682809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_293
      · exact prime_oneHundredFiftyNineFA_421
      · exact prime_oneHundredFiftyNineFA_2704858427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 56053603459682809) ^ 28026801729841404 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (13 : ZMod 56053603459682809) ^ 18684534486560936 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (13 : ZMod 56053603459682809) ^ 8007657637097544 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (13 : ZMod 56053603459682809) ^ 191309226824856 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (13 : ZMod 56053603459682809) ^ 133143951210648 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (13 : ZMod 56053603459682809) ^ 20723304 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_67417440473661349 : Nat.Prime 67417440473661349 := by
  apply lucas_primality 67417440473661349 (6 : ZMod 67417440473661349)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (569, 1), (677, 1), (2083492969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (569, 1), (677, 1), (2083492969, 1)] : List FactorBlock).map factorBlockValue).prod) = 67417440473661349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_569
      · exact prime_oneHundredFiftyNineFA_677
      · exact prime_oneHundredFiftyNineFA_2083492969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 67417440473661349) ^ 33708720236830674 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (6 : ZMod 67417440473661349) ^ 22472480157887116 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (6 : ZMod 67417440473661349) ^ 9631062924808764 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (6 : ZMod 67417440473661349) ^ 118484078161092 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (6 : ZMod 67417440473661349) ^ 99582629946324 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (6 : ZMod 67417440473661349) ^ 32357892 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_119008016981119919 : Nat.Prime 119008016981119919 := by
  apply lucas_primality 119008016981119919 (7 : ZMod 119008016981119919)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (756739, 1), (78632141981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (756739, 1), (78632141981, 1)] : List FactorBlock).map factorBlockValue).prod) = 119008016981119919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_756739
      · exact prime_oneHundredFiftyNineFA_78632141981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 119008016981119919) ^ 59504008490559959 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 119008016981119919) ^ 157264283962 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 119008016981119919) ^ 1513478 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_149246820764868341 : Nat.Prime 149246820764868341 := by
  apply lucas_primality 149246820764868341 (3 : ZMod 149246820764868341)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (41, 1), (659, 1), (276188646443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (41, 1), (659, 1), (276188646443, 1)] : List FactorBlock).map factorBlockValue).prod) = 149246820764868341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_41
      · exact prime_oneHundredFiftyNineFA_659
      · exact prime_oneHundredFiftyNineFA_276188646443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 149246820764868341) ^ 74623410382434170 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 149246820764868341) ^ 29849364152973668 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 149246820764868341) ^ 3640166360118740 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 149246820764868341) ^ 226474690083260 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 149246820764868341) ^ 540380 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_186619825497697463 : Nat.Prime 186619825497697463 := by
  apply lucas_primality 186619825497697463 (5 : ZMod 186619825497697463)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (16427, 1), (436944396181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (16427, 1), (436944396181, 1)] : List FactorBlock).map factorBlockValue).prod) = 186619825497697463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_13
      · exact prime_oneHundredFiftyNineFA_16427
      · exact prime_oneHundredFiftyNineFA_436944396181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 186619825497697463) ^ 93309912748848731 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 186619825497697463) ^ 14355371192130574 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 186619825497697463) ^ 11360554300706 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 186619825497697463) ^ 427102 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_222938340944796773 : Nat.Prime 222938340944796773 := by
  apply lucas_primality 222938340944796773 (2 : ZMod 222938340944796773)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (293, 1), (190220427427301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (293, 1), (190220427427301, 1)] : List FactorBlock).map factorBlockValue).prod) = 222938340944796773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_293
      · exact prime_oneHundredFiftyNineFA_190220427427301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 222938340944796773) ^ 111469170472398386 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 222938340944796773) ^ 760881709709204 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 222938340944796773) ^ 1172 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_298493641529736683 : Nat.Prime 298493641529736683 := by
  apply lucas_primality 298493641529736683 (2 : ZMod 298493641529736683)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (149246820764868341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (149246820764868341, 1)] : List FactorBlock).map factorBlockValue).prod) = 298493641529736683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_149246820764868341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 298493641529736683) ^ 149246820764868341 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 298493641529736683) ^ 2 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_429586205299135447 : Nat.Prime 429586205299135447 := by
  apply lucas_primality 429586205299135447 (3 : ZMod 429586205299135447)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (337, 1), (577, 1), (40841, 1), (9015649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (337, 1), (577, 1), (40841, 1), (9015649, 1)] : List FactorBlock).map factorBlockValue).prod) = 429586205299135447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_337
      · exact prime_oneHundredFiftyNineFA_577
      · exact prime_oneHundredFiftyNineFA_40841
      · exact prime_oneHundredFiftyNineFA_9015649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 429586205299135447) ^ 214793102649567723 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 429586205299135447) ^ 143195401766378482 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 429586205299135447) ^ 1274736514240758 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 429586205299135447) ^ 744516820275798 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 429586205299135447) ^ 10518503594406 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 429586205299135447) ^ 47648949654 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_447361700242105757 : Nat.Prime 447361700242105757 := by
  apply lucas_primality 447361700242105757 (2 : ZMod 447361700242105757)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (119270369, 1), (937705031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (119270369, 1), (937705031, 1)] : List FactorBlock).map factorBlockValue).prod) = 447361700242105757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_119270369
      · exact prime_oneHundredFiftyNineFA_937705031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 447361700242105757) ^ 223680850121052878 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 447361700242105757) ^ 3750820124 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 447361700242105757) ^ 477081476 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_617397497147537221 : Nat.Prime 617397497147537221 := by
  apply lucas_primality 617397497147537221 (7 : ZMod 617397497147537221)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (6791, 1), (69389, 1), (21836813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (6791, 1), (69389, 1), (21836813, 1)] : List FactorBlock).map factorBlockValue).prod) = 617397497147537221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_6791
      · exact prime_oneHundredFiftyNineFA_69389
      · exact prime_oneHundredFiftyNineFA_21836813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 617397497147537221) ^ 308698748573768610 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 617397497147537221) ^ 205799165715845740 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 617397497147537221) ^ 123479499429507444 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 617397497147537221) ^ 90914077035420 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 617397497147537221) ^ 8897627824980 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 617397497147537221) ^ 28273241940 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_1508608676988160103 : Nat.Prime 1508608676988160103 := by
  apply lucas_primality 1508608676988160103 (5 : ZMod 1508608676988160103)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (32795840804090437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (32795840804090437, 1)] : List FactorBlock).map factorBlockValue).prod) = 1508608676988160103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_23
      · exact prime_oneHundredFiftyNineFA_32795840804090437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1508608676988160103) ^ 754304338494080051 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1508608676988160103) ^ 65591681608180874 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1508608676988160103) ^ 46 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_1605316070217318001 : Nat.Prime 1605316070217318001 := by
  apply lucas_primality 1605316070217318001 (31 : ZMod 1605316070217318001)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 3), (19, 1), (257, 1), (953, 1), (7177, 1), (8011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 3), (19, 1), (257, 1), (953, 1), (7177, 1), (8011, 1)] : List FactorBlock).map factorBlockValue).prod) = 1605316070217318001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_19
      · exact prime_oneHundredFiftyNineFA_257
      · exact prime_oneHundredFiftyNineFA_953
      · exact prime_oneHundredFiftyNineFA_7177
      · exact prime_oneHundredFiftyNineFA_8011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 1605316070217318001) ^ 802658035108659000 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (31 : ZMod 1605316070217318001) ^ 535105356739106000 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (31 : ZMod 1605316070217318001) ^ 321063214043463600 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (31 : ZMod 1605316070217318001) ^ 84490319485122000 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (31 : ZMod 1605316070217318001) ^ 6246366031974000 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (31 : ZMod 1605316070217318001) ^ 1684486957206000 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (31 : ZMod 1605316070217318001) ^ 223675082934000 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (31 : ZMod 1605316070217318001) ^ 200388973938000 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_1957807607855321821 : Nat.Prime 1957807607855321821 := by
  apply lucas_primality 1957807607855321821 (2 : ZMod 1957807607855321821)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 2), (31, 1), (229, 1), (27197869187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 2), (31, 1), (229, 1), (27197869187, 1)] : List FactorBlock).map factorBlockValue).prod) = 1957807607855321821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_13
      · exact prime_oneHundredFiftyNineFA_31
      · exact prime_oneHundredFiftyNineFA_229
      · exact prime_oneHundredFiftyNineFA_27197869187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1957807607855321821) ^ 978903803927660910 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1957807607855321821) ^ 652602535951773940 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1957807607855321821) ^ 391561521571064364 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1957807607855321821) ^ 150600585219640140 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1957807607855321821) ^ 63155084124365220 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1957807607855321821) ^ 8549378200241580 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1957807607855321821) ^ 71983860 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_2138652676301314223 : Nat.Prime 2138652676301314223 := by
  apply lucas_primality 2138652676301314223 (7 : ZMod 2138652676301314223)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (43, 1), (641, 1), (5542245236371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (43, 1), (641, 1), (5542245236371, 1)] : List FactorBlock).map factorBlockValue).prod) = 2138652676301314223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_43
      · exact prime_oneHundredFiftyNineFA_641
      · exact prime_oneHundredFiftyNineFA_5542245236371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2138652676301314223) ^ 1069326338150657111 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 2138652676301314223) ^ 305521810900187746 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 2138652676301314223) ^ 49736108751193354 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 2138652676301314223) ^ 3336431632295342 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 2138652676301314223) ^ 385882 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_3005535128788957469 : Nat.Prime 3005535128788957469 := by
  apply lucas_primality 3005535128788957469 (2 : ZMod 3005535128788957469)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 2), (6209783323944127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 2), (6209783323944127, 1)] : List FactorBlock).map factorBlockValue).prod) = 3005535128788957469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_11
      · exact prime_oneHundredFiftyNineFA_6209783323944127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3005535128788957469) ^ 1502767564394478734 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3005535128788957469) ^ 273230466253541588 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3005535128788957469) ^ 484 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_3048207908181478079 : Nat.Prime 3048207908181478079 := by
  apply lucas_primality 3048207908181478079 (7 : ZMod 3048207908181478079)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (542461, 1), (2809610191499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (542461, 1), (2809610191499, 1)] : List FactorBlock).map factorBlockValue).prod) = 3048207908181478079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_542461
      · exact prime_oneHundredFiftyNineFA_2809610191499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 3048207908181478079) ^ 1524103954090739039 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 3048207908181478079) ^ 5619220382998 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 3048207908181478079) ^ 1084922 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_3732418910315129977 : Nat.Prime 3732418910315129977 := by
  apply lucas_primality 3732418910315129977 (5 : ZMod 3732418910315129977)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (34129, 1), (456647, 1), (1108747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (34129, 1), (456647, 1), (1108747, 1)] : List FactorBlock).map factorBlockValue).prod) = 3732418910315129977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_34129
      · exact prime_oneHundredFiftyNineFA_456647
      · exact prime_oneHundredFiftyNineFA_1108747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3732418910315129977) ^ 1866209455157564988 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 3732418910315129977) ^ 1244139636771709992 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 3732418910315129977) ^ 109362094122744 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 3732418910315129977) ^ 8173532094408 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 3732418910315129977) ^ 3366339580008 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_4277305352602628447 : Nat.Prime 4277305352602628447 := by
  apply lucas_primality 4277305352602628447 (5 : ZMod 4277305352602628447)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2138652676301314223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2138652676301314223, 1)] : List FactorBlock).map factorBlockValue).prod) = 4277305352602628447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_2138652676301314223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 4277305352602628447) ^ 2138652676301314223 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 4277305352602628447) ^ 2 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_5924407526678798057 : Nat.Prime 5924407526678798057 := by
  apply lucas_primality 5924407526678798057 (3 : ZMod 5924407526678798057)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (41, 1), (59, 1), (306139289307503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (41, 1), (59, 1), (306139289307503, 1)] : List FactorBlock).map factorBlockValue).prod) = 5924407526678798057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_41
      · exact prime_oneHundredFiftyNineFA_59
      · exact prime_oneHundredFiftyNineFA_306139289307503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5924407526678798057) ^ 2962203763339399028 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5924407526678798057) ^ 144497744553141416 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5924407526678798057) ^ 100413686892860984 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5924407526678798057) ^ 19352 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_8491168222817651923 : Nat.Prime 8491168222817651923 := by
  apply lucas_primality 8491168222817651923 (2 : ZMod 8491168222817651923)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (34516943995193707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (34516943995193707, 1)] : List FactorBlock).map factorBlockValue).prod) = 8491168222817651923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_41
      · exact prime_oneHundredFiftyNineFA_34516943995193707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8491168222817651923) ^ 4245584111408825961 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8491168222817651923) ^ 2830389407605883974 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8491168222817651923) ^ 207101663971162242 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8491168222817651923) ^ 246 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_8947234004842115141 : Nat.Prime 8947234004842115141 := by
  apply lucas_primality 8947234004842115141 (3 : ZMod 8947234004842115141)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (447361700242105757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (447361700242105757, 1)] : List FactorBlock).map factorBlockValue).prod) = 8947234004842115141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_447361700242105757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 8947234004842115141) ^ 4473617002421057570 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 8947234004842115141) ^ 1789446800968423028 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 8947234004842115141) ^ 20 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_12561721862134067009 : Nat.Prime 12561721862134067009 := by
  apply lucas_primality 12561721862134067009 (3 : ZMod 12561721862134067009)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (353, 1), (5743, 1), (7321, 1), (13224683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (353, 1), (5743, 1), (7321, 1), (13224683, 1)] : List FactorBlock).map factorBlockValue).prod) = 12561721862134067009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_353
      · exact prime_oneHundredFiftyNineFA_5743
      · exact prime_oneHundredFiftyNineFA_7321
      · exact prime_oneHundredFiftyNineFA_13224683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 12561721862134067009) ^ 6280860931067033504 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 12561721862134067009) ^ 35585614340323136 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 12561721862134067009) ^ 2187310092657856 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 12561721862134067009) ^ 1715847816163648 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 12561721862134067009) ^ 949869411776 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_16715643925665254249 : Nat.Prime 16715643925665254249 := by
  apply lucas_primality 16715643925665254249 (3 : ZMod 16715643925665254249)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (298493641529736683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (298493641529736683, 1)] : List FactorBlock).map factorBlockValue).prod) = 16715643925665254249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_298493641529736683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 16715643925665254249) ^ 8357821962832627124 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 16715643925665254249) ^ 2387949132237893464 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 16715643925665254249) ^ 56 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_19909039244896649699 : Nat.Prime 19909039244896649699 := by
  apply lucas_primality 19909039244896649699 (2 : ZMod 19909039244896649699)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (421, 1), (762739990992899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (421, 1), (762739990992899, 1)] : List FactorBlock).map factorBlockValue).prod) = 19909039244896649699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_31
      · exact prime_oneHundredFiftyNineFA_421
      · exact prime_oneHundredFiftyNineFA_762739990992899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 19909039244896649699) ^ 9954519622448324849 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 19909039244896649699) ^ 642227072416020958 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 19909039244896649699) ^ 47289879441559738 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 19909039244896649699) ^ 26102 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_22317101458347153313 : Nat.Prime 22317101458347153313 := by
  apply lucas_primality 22317101458347153313 (5 : ZMod 22317101458347153313)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (11913173, 1), (6504558913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (11913173, 1), (6504558913, 1)] : List FactorBlock).map factorBlockValue).prod) = 22317101458347153313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_11913173
      · exact prime_oneHundredFiftyNineFA_6504558913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 22317101458347153313) ^ 11158550729173576656 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 22317101458347153313) ^ 7439033819449051104 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 22317101458347153313) ^ 1873312966944 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 22317101458347153313) ^ 3430993824 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_33255808765021652123 : Nat.Prime 33255808765021652123 := by
  apply lucas_primality 33255808765021652123 (2 : ZMod 33255808765021652123)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (18065417, 1), (920427376933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (18065417, 1), (920427376933, 1)] : List FactorBlock).map factorBlockValue).prod) = 33255808765021652123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_18065417
      · exact prime_oneHundredFiftyNineFA_920427376933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 33255808765021652123) ^ 16627904382510826061 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 33255808765021652123) ^ 1840854753866 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 33255808765021652123) ^ 36130834 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_44454448891364149873 : Nat.Prime 44454448891364149873 := by
  apply lucas_primality 44454448891364149873 (10 : ZMod 44454448891364149873)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (13, 1), (23747034664190251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (13, 1), (23747034664190251, 1)] : List FactorBlock).map factorBlockValue).prod) = 44454448891364149873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_13
      · exact prime_oneHundredFiftyNineFA_23747034664190251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 44454448891364149873) ^ 22227224445682074936 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (10 : ZMod 44454448891364149873) ^ 14818149630454716624 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (10 : ZMod 44454448891364149873) ^ 3419572991643396144 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (10 : ZMod 44454448891364149873) ^ 1872 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_66329886932288418827 : Nat.Prime 66329886932288418827 := by
  apply lucas_primality 66329886932288418827 (2 : ZMod 66329886932288418827)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (347, 1), (20747, 1), (263537, 1), (296279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (347, 1), (20747, 1), (263537, 1), (296279, 1)] : List FactorBlock).map factorBlockValue).prod) = 66329886932288418827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_59
      · exact prime_oneHundredFiftyNineFA_347
      · exact prime_oneHundredFiftyNineFA_20747
      · exact prime_oneHundredFiftyNineFA_263537
      · exact prime_oneHundredFiftyNineFA_296279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 66329886932288418827) ^ 33164943466144209413 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 66329886932288418827) ^ 1124235371733702014 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 66329886932288418827) ^ 191152411908612158 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 66329886932288418827) ^ 3197083285886558 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 66329886932288418827) ^ 251690984310698 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 66329886932288418827) ^ 223876437183494 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_66511617530043304247 : Nat.Prime 66511617530043304247 := by
  apply lucas_primality 66511617530043304247 (5 : ZMod 66511617530043304247)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (33255808765021652123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (33255808765021652123, 1)] : List FactorBlock).map factorBlockValue).prod) = 66511617530043304247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_33255808765021652123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 66511617530043304247) ^ 33255808765021652123 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 66511617530043304247) ^ 2 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_67423274949127356043 : Nat.Prime 67423274949127356043 := by
  apply lucas_primality 67423274949127356043 (3 : ZMod 67423274949127356043)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (1605316070217318001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (1605316070217318001, 1)] : List FactorBlock).map factorBlockValue).prod) = 67423274949127356043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_1605316070217318001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 67423274949127356043) ^ 33711637474563678021 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 67423274949127356043) ^ 22474424983042452014 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 67423274949127356043) ^ 9631896421303908006 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 67423274949127356043) ^ 42 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_70428999594827662457 : Nat.Prime 70428999594827662457 := by
  apply lucas_primality 70428999594827662457 (3 : ZMod 70428999594827662457)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11483, 1), (28403, 1), (26992428143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11483, 1), (28403, 1), (26992428143, 1)] : List FactorBlock).map factorBlockValue).prod) = 70428999594827662457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_11483
      · exact prime_oneHundredFiftyNineFA_28403
      · exact prime_oneHundredFiftyNineFA_26992428143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 70428999594827662457) ^ 35214499797413831228 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 70428999594827662457) ^ 6133327492365032 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 70428999594827662457) ^ 2479632418928552 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 70428999594827662457) ^ 2609213192 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_256223811061086791179 : Nat.Prime 256223811061086791179 := by
  apply lucas_primality 256223811061086791179 (2 : ZMod 256223811061086791179)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) = 256223811061086791179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_17
      · exact prime_oneHundredFiftyNineFA_6863
      · exact prime_oneHundredFiftyNineFA_366020420757353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 256223811061086791179) ^ 128111905530543395589 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 85407937020362263726 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 15071988885946281834 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 37334082917250006 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 700026 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_336136413140095205089 : Nat.Prime 336136413140095205089 := by
  apply lucas_primality 336136413140095205089 (17 : ZMod 336136413140095205089)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (11, 1), (431, 1), (727, 1), (138401, 1), (2446693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (11, 1), (431, 1), (727, 1), (138401, 1), (2446693, 1)] : List FactorBlock).map factorBlockValue).prod) = 336136413140095205089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_11
      · exact prime_oneHundredFiftyNineFA_431
      · exact prime_oneHundredFiftyNineFA_727
      · exact prime_oneHundredFiftyNineFA_138401
      · exact prime_oneHundredFiftyNineFA_2446693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 336136413140095205089) ^ 168068206570047602544 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (17 : ZMod 336136413140095205089) ^ 112045471046698401696 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (17 : ZMod 336136413140095205089) ^ 30557855740008655008 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (17 : ZMod 336136413140095205089) ^ 779898870394652448 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (17 : ZMod 336136413140095205089) ^ 462360953425165344 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (17 : ZMod 336136413140095205089) ^ 2428713760305888 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (17 : ZMod 336136413140095205089) ^ 137383976306016 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_342017481667622015413 : Nat.Prime 342017481667622015413 := by
  apply lucas_primality 342017481667622015413 (2 : ZMod 342017481667622015413)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (4057, 1), (145517, 1), (16092631393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (4057, 1), (145517, 1), (16092631393, 1)] : List FactorBlock).map factorBlockValue).prod) = 342017481667622015413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_4057
      · exact prime_oneHundredFiftyNineFA_145517
      · exact prime_oneHundredFiftyNineFA_16092631393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 342017481667622015413) ^ 171008740833811007706 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 342017481667622015413) ^ 114005827222540671804 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 342017481667622015413) ^ 84303051926946516 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 342017481667622015413) ^ 2350361000210436 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 342017481667622015413) ^ 21253048884 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_417686148190500523487 : Nat.Prime 417686148190500523487 := by
  apply lucas_primality 417686148190500523487 (5 : ZMod 417686148190500523487)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (269, 1), (547, 1), (1861583, 1), (762426647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (269, 1), (547, 1), (1861583, 1), (762426647, 1)] : List FactorBlock).map factorBlockValue).prod) = 417686148190500523487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_269
      · exact prime_oneHundredFiftyNineFA_547
      · exact prime_oneHundredFiftyNineFA_1861583
      · exact prime_oneHundredFiftyNineFA_762426647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 417686148190500523487) ^ 208843074095250261743 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 417686148190500523487) ^ 1552736610373607894 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 417686148190500523487) ^ 763594420823584138 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 417686148190500523487) ^ 224371488239042 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 417686148190500523487) ^ 547837814738 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_522766932770166402449 : Nat.Prime 522766932770166402449 := by
  apply lucas_primality 522766932770166402449 (3 : ZMod 522766932770166402449)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (29, 1), (31, 1), (1471, 1), (83203, 1), (22841963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (29, 1), (31, 1), (1471, 1), (83203, 1), (22841963, 1)] : List FactorBlock).map factorBlockValue).prod) = 522766932770166402449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_13
      · exact prime_oneHundredFiftyNineFA_29
      · exact prime_oneHundredFiftyNineFA_31
      · exact prime_oneHundredFiftyNineFA_1471
      · exact prime_oneHundredFiftyNineFA_83203
      · exact prime_oneHundredFiftyNineFA_22841963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 522766932770166402449) ^ 261383466385083201224 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 522766932770166402449) ^ 40212840982320492496 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 522766932770166402449) ^ 18026445957591944912 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 522766932770166402449) ^ 16863449444198916208 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 522766932770166402449) ^ 355382007321663088 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 522766932770166402449) ^ 6283029851930416 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 522766932770166402449) ^ 22886252498096 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_670823648355116296133 : Nat.Prime 670823648355116296133 := by
  apply lucas_primality 670823648355116296133 (2 : ZMod 670823648355116296133)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (127, 1), (4554743, 1), (289921734953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (127, 1), (4554743, 1), (289921734953, 1)] : List FactorBlock).map factorBlockValue).prod) = 670823648355116296133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_127
      · exact prime_oneHundredFiftyNineFA_4554743
      · exact prime_oneHundredFiftyNineFA_289921734953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 670823648355116296133) ^ 335411824177558148066 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 670823648355116296133) ^ 5282075971300128316 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 670823648355116296133) ^ 147280241356124 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 670823648355116296133) ^ 2313809444 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_889116774081175360157 : Nat.Prime 889116774081175360157 := by
  apply lucas_primality 889116774081175360157 (2 : ZMod 889116774081175360157)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (53, 1), (109, 1), (10601, 1), (139759, 1), (25969873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (53, 1), (109, 1), (10601, 1), (139759, 1), (25969873, 1)] : List FactorBlock).map factorBlockValue).prod) = 889116774081175360157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_53
      · exact prime_oneHundredFiftyNineFA_109
      · exact prime_oneHundredFiftyNineFA_10601
      · exact prime_oneHundredFiftyNineFA_139759
      · exact prime_oneHundredFiftyNineFA_25969873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 889116774081175360157) ^ 444558387040587680078 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 889116774081175360157) ^ 16775788190210855852 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 889116774081175360157) ^ 8157034624597939084 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 889116774081175360157) ^ 83871028589866556 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 889116774081175360157) ^ 6361785459835684 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 889116774081175360157) ^ 34236469854172 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_1152678511166329677349 : Nat.Prime 1152678511166329677349 := by
  apply lucas_primality 1152678511166329677349 (2 : ZMod 1152678511166329677349)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (7, 1), (13, 1), (19, 2), (61, 1), (131, 1), (13552314197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (7, 1), (13, 1), (19, 2), (61, 1), (131, 1), (13552314197, 1)] : List FactorBlock).map factorBlockValue).prod) = 1152678511166329677349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_13
      · exact prime_oneHundredFiftyNineFA_19
      · exact prime_oneHundredFiftyNineFA_61
      · exact prime_oneHundredFiftyNineFA_131
      · exact prime_oneHundredFiftyNineFA_13552314197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1152678511166329677349) ^ 576339255583164838674 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1152678511166329677349) ^ 384226170388776559116 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1152678511166329677349) ^ 164668358738047096764 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1152678511166329677349) ^ 88667577782025359796 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1152678511166329677349) ^ 60667290061385772492 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1152678511166329677349) ^ 18896369035513601268 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1152678511166329677349) ^ 8799072604323127308 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1152678511166329677349) ^ 85053998484 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_2771173502175542570419 : Nat.Prime 2771173502175542570419 := by
  apply lucas_primality 2771173502175542570419 (2 : ZMod 2771173502175542570419)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (17, 1), (23, 1), (53, 1), (34252279, 1), (50052643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (17, 1), (23, 1), (53, 1), (34252279, 1), (50052643, 1)] : List FactorBlock).map factorBlockValue).prod) = 2771173502175542570419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_13
      · exact prime_oneHundredFiftyNineFA_17
      · exact prime_oneHundredFiftyNineFA_23
      · exact prime_oneHundredFiftyNineFA_53
      · exact prime_oneHundredFiftyNineFA_34252279
      · exact prime_oneHundredFiftyNineFA_50052643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2771173502175542570419) ^ 1385586751087771285209 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2771173502175542570419) ^ 923724500725180856806 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2771173502175542570419) ^ 213167192475041736186 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2771173502175542570419) ^ 163010206010326033554 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2771173502175542570419) ^ 120485804442414894366 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2771173502175542570419) ^ 52286292493878161706 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2771173502175542570419) ^ 80904791829342 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2771173502175542570419) ^ 55365178261926 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_3074685732733041494149 : Nat.Prime 3074685732733041494149 := by
  apply lucas_primality 3074685732733041494149 (2 : ZMod 3074685732733041494149)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) = 3074685732733041494149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_256223811061086791179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3074685732733041494149) ^ 1537342866366520747074 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 1024895244244347164716 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 12 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_4553963459756815472759 : Nat.Prime 4553963459756815472759 := by
  apply lucas_primality 4553963459756815472759 (19 : ZMod 4553963459756815472759)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (29, 1), (1579, 1), (1873, 1), (2042200077481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (29, 1), (1579, 1), (1873, 1), (2042200077481, 1)] : List FactorBlock).map factorBlockValue).prod) = 4553963459756815472759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_13
      · exact prime_oneHundredFiftyNineFA_29
      · exact prime_oneHundredFiftyNineFA_1579
      · exact prime_oneHundredFiftyNineFA_1873
      · exact prime_oneHundredFiftyNineFA_2042200077481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 4553963459756815472759) ^ 2276981729878407736379 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (19 : ZMod 4553963459756815472759) ^ 350304881519755036366 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (19 : ZMod 4553963459756815472759) ^ 157033222750235016302 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (19 : ZMod 4553963459756815472759) ^ 2884080721821922402 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (19 : ZMod 4553963459756815472759) ^ 2431373977446244246 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (19 : ZMod 4553963459756815472759) ^ 2229930118 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_4610714044665318709397 : Nat.Prime 4610714044665318709397 := by
  apply lucas_primality 4610714044665318709397 (2 : ZMod 4610714044665318709397)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1152678511166329677349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1152678511166329677349, 1)] : List FactorBlock).map factorBlockValue).prod) = 4610714044665318709397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_1152678511166329677349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 4610714044665318709397) ^ 2305357022332659354698 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4610714044665318709397) ^ 4 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_11476139938764072156677 : Nat.Prime 11476139938764072156677 := by
  apply lucas_primality 11476139938764072156677 (2 : ZMod 11476139938764072156677)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (13, 1), (1982587, 1), (15902382581257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (13, 1), (1982587, 1), (15902382581257, 1)] : List FactorBlock).map factorBlockValue).prod) = 11476139938764072156677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_13
      · exact prime_oneHundredFiftyNineFA_1982587
      · exact prime_oneHundredFiftyNineFA_15902382581257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11476139938764072156677) ^ 5738069969382036078338 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 11476139938764072156677) ^ 1639448562680581736668 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 11476139938764072156677) ^ 882779995289544012052 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 11476139938764072156677) ^ 5788467259577548 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 11476139938764072156677) ^ 721661668 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_23980393550586262495571 : Nat.Prime 23980393550586262495571 := by
  apply lucas_primality 23980393550586262495571 (2 : ZMod 23980393550586262495571)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (59, 1), (197, 1), (2156117, 1), (5628813031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (59, 1), (197, 1), (2156117, 1), (5628813031, 1)] : List FactorBlock).map factorBlockValue).prod) = 23980393550586262495571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_17
      · exact prime_oneHundredFiftyNineFA_59
      · exact prime_oneHundredFiftyNineFA_197
      · exact prime_oneHundredFiftyNineFA_2156117
      · exact prime_oneHundredFiftyNineFA_5628813031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 23980393550586262495571) ^ 11990196775293131247785 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 23980393550586262495571) ^ 4796078710117252499114 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 23980393550586262495571) ^ 1410611385328603676210 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 23980393550586262495571) ^ 406447348315021398230 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 23980393550586262495571) ^ 121727886043585088810 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 23980393550586262495571) ^ 11122027956083210 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 23980393550586262495571) ^ 4260293141470 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_26948355208311503511221 : Nat.Prime 26948355208311503511221 := by
  apply lucas_primality 26948355208311503511221 (2 : ZMod 26948355208311503511221)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (67, 1), (839117, 1), (1843578322123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (67, 1), (839117, 1), (1843578322123, 1)] : List FactorBlock).map factorBlockValue).prod) = 26948355208311503511221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_13
      · exact prime_oneHundredFiftyNineFA_67
      · exact prime_oneHundredFiftyNineFA_839117
      · exact prime_oneHundredFiftyNineFA_1843578322123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 26948355208311503511221) ^ 13474177604155751755610 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 26948355208311503511221) ^ 5389671041662300702244 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 26948355208311503511221) ^ 2072950400639346423940 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 26948355208311503511221) ^ 402214256840470201660 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 26948355208311503511221) ^ 32115134371382660 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 26948355208311503511221) ^ 14617418140 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_36885712357322549675177 : Nat.Prime 36885712357322549675177 := by
  apply lucas_primality 36885712357322549675177 (3 : ZMod 36885712357322549675177)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (4610714044665318709397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (4610714044665318709397, 1)] : List FactorBlock).map factorBlockValue).prod) = 36885712357322549675177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_4610714044665318709397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 36885712357322549675177) ^ 18442856178661274837588 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 36885712357322549675177) ^ 8 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_47356998990119940549269 : Nat.Prime 47356998990119940549269 := by
  apply lucas_primality 47356998990119940549269 (2 : ZMod 47356998990119940549269)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (211213, 1), (56053603459682809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (211213, 1), (56053603459682809, 1)] : List FactorBlock).map factorBlockValue).prod) = 47356998990119940549269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_211213
      · exact prime_oneHundredFiftyNineFA_56053603459682809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 47356998990119940549269) ^ 23678499495059970274634 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 47356998990119940549269) ^ 224214413838731236 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 47356998990119940549269) ^ 844852 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_158573863103064139659323 : Nat.Prime 158573863103064139659323 := by
  apply lucas_primality 158573863103064139659323 (2 : ZMod 158573863103064139659323)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (179, 1), (503, 1), (127363, 1), (6914126395331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (179, 1), (503, 1), (127363, 1), (6914126395331, 1)] : List FactorBlock).map factorBlockValue).prod) = 158573863103064139659323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_179
      · exact prime_oneHundredFiftyNineFA_503
      · exact prime_oneHundredFiftyNineFA_127363
      · exact prime_oneHundredFiftyNineFA_6914126395331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 158573863103064139659323) ^ 79286931551532069829661 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 158573863103064139659323) ^ 885887503369073405918 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 158573863103064139659323) ^ 315256189071698090774 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 158573863103064139659323) ^ 1245054396512834494 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 158573863103064139659323) ^ 22934764862 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_448917076797523931142103 : Nat.Prime 448917076797523931142103 := by
  apply lucas_primality 448917076797523931142103 (5 : ZMod 448917076797523931142103)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (167, 1), (1221271069, 1), (366848151979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (167, 1), (1221271069, 1), (366848151979, 1)] : List FactorBlock).map factorBlockValue).prod) = 448917076797523931142103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_167
      · exact prime_oneHundredFiftyNineFA_1221271069
      · exact prime_oneHundredFiftyNineFA_366848151979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 448917076797523931142103) ^ 224458538398761965571051 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 448917076797523931142103) ^ 149639025599174643714034 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 448917076797523931142103) ^ 2688126208368406773306 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 448917076797523931142103) ^ 367581848282958 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 448917076797523931142103) ^ 1223713611138 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_1226433932515291347353801 : Nat.Prime 1226433932515291347353801 := by
  apply lucas_primality 1226433932515291347353801 (3 : ZMod 1226433932515291347353801)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (7, 1), (18401, 1), (47607425548118167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (7, 1), (18401, 1), (47607425548118167, 1)] : List FactorBlock).map factorBlockValue).prod) = 1226433932515291347353801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_18401
      · exact prime_oneHundredFiftyNineFA_47607425548118167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1226433932515291347353801) ^ 613216966257645673676900 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1226433932515291347353801) ^ 245286786503058269470760 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1226433932515291347353801) ^ 175204847502184478193400 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1226433932515291347353801) ^ 66650395767365433800 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1226433932515291347353801) ^ 25761400 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_1327958084237678134267049 : Nat.Prime 1327958084237678134267049 := by
  apply lucas_primality 1327958084237678134267049 (3 : ZMod 1327958084237678134267049)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (17, 1), (1272258079, 1), (697714190897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (17, 1), (1272258079, 1), (697714190897, 1)] : List FactorBlock).map factorBlockValue).prod) = 1327958084237678134267049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_11
      · exact prime_oneHundredFiftyNineFA_17
      · exact prime_oneHundredFiftyNineFA_1272258079
      · exact prime_oneHundredFiftyNineFA_697714190897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1327958084237678134267049) ^ 663979042118839067133524 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1327958084237678134267049) ^ 120723462203425284933368 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1327958084237678134267049) ^ 78115181425745772603944 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1327958084237678134267049) ^ 1043780429581912 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1327958084237678134267049) ^ 1903298086184 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_2270541901563560845675333 : Nat.Prime 2270541901563560845675333 := by
  apply lucas_primality 2270541901563560845675333 (2 : ZMod 2270541901563560845675333)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (151, 1), (417686148190500523487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (151, 1), (417686148190500523487, 1)] : List FactorBlock).map factorBlockValue).prod) = 2270541901563560845675333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_151
      · exact prime_oneHundredFiftyNineFA_417686148190500523487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2270541901563560845675333) ^ 1135270950781780422837666 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2270541901563560845675333) ^ 756847300521186948558444 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2270541901563560845675333) ^ 15036701334858018845532 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2270541901563560845675333) ^ 5436 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_2311954968420681433245271 : Nat.Prime 2311954968420681433245271 := by
  apply lucas_primality 2311954968420681433245271 (3 : ZMod 2311954968420681433245271)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (7207, 1), (16062367, 1), (31701130841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (7207, 1), (16062367, 1), (31701130841, 1)] : List FactorBlock).map factorBlockValue).prod) = 2311954968420681433245271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_7207
      · exact prime_oneHundredFiftyNineFA_16062367
      · exact prime_oneHundredFiftyNineFA_31701130841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2311954968420681433245271) ^ 1155977484210340716622635 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2311954968420681433245271) ^ 770651656140227144415090 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2311954968420681433245271) ^ 462390993684136286649054 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2311954968420681433245271) ^ 330279281202954490463610 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2311954968420681433245271) ^ 320792974666391207610 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2311954968420681433245271) ^ 143936131481784810 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2311954968420681433245271) ^ 72929731750470 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_2350078567957453724565959 : Nat.Prime 2350078567957453724565959 := by
  apply lucas_primality 2350078567957453724565959 (7 : ZMod 2350078567957453724565959)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (23980393550586262495571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (23980393550586262495571, 1)] : List FactorBlock).map factorBlockValue).prod) = 2350078567957453724565959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_23980393550586262495571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 2350078567957453724565959) ^ 1175039283978726862282979 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 2350078567957453724565959) ^ 335725509708207674937994 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 2350078567957453724565959) ^ 98 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_2393984291948100735772223 : Nat.Prime 2393984291948100735772223 := by
  apply lucas_primality 2393984291948100735772223 (5 : ZMod 2393984291948100735772223)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (563, 1), (3803, 1), (9281, 1), (1369793, 1), (1911961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (563, 1), (3803, 1), (9281, 1), (1369793, 1), (1911961, 1)] : List FactorBlock).map factorBlockValue).prod) = 2393984291948100735772223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_23
      · exact prime_oneHundredFiftyNineFA_563
      · exact prime_oneHundredFiftyNineFA_3803
      · exact prime_oneHundredFiftyNineFA_9281
      · exact prime_oneHundredFiftyNineFA_1369793
      · exact prime_oneHundredFiftyNineFA_1911961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2393984291948100735772223) ^ 1196992145974050367886111 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 2393984291948100735772223) ^ 104086273562960901555314 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 2393984291948100735772223) ^ 4252192348042807701194 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 2393984291948100735772223) ^ 629498893491480603674 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 2393984291948100735772223) ^ 257944649493384412862 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 2393984291948100735772223) ^ 1747697857959633854 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 2393984291948100735772223) ^ 1252109374588760302 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_2655916168475356268534099 : Nat.Prime 2655916168475356268534099 := by
  apply lucas_primality 2655916168475356268534099 (2 : ZMod 2655916168475356268534099)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1327958084237678134267049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1327958084237678134267049, 1)] : List FactorBlock).map factorBlockValue).prod) = 2655916168475356268534099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_1327958084237678134267049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 2655916168475356268534099) ^ 1327958084237678134267049 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2655916168475356268534099) ^ 2 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_3371241653019167252049973 : Nat.Prime 3371241653019167252049973 := by
  apply lucas_primality 3371241653019167252049973 (2 : ZMod 3371241653019167252049973)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (13, 1), (47, 1), (79, 1), (7103, 1), (91044981601837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (13, 1), (47, 1), (79, 1), (7103, 1), (91044981601837, 1)] : List FactorBlock).map factorBlockValue).prod) = 3371241653019167252049973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_13
      · exact prime_oneHundredFiftyNineFA_47
      · exact prime_oneHundredFiftyNineFA_79
      · exact prime_oneHundredFiftyNineFA_7103
      · exact prime_oneHundredFiftyNineFA_91044981601837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3371241653019167252049973) ^ 1685620826509583626024986 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3371241653019167252049973) ^ 1123747217673055750683324 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3371241653019167252049973) ^ 259326281001474404003844 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3371241653019167252049973) ^ 71728545808918452171276 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3371241653019167252049973) ^ 42673944974926167747468 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3371241653019167252049973) ^ 474622223429419576524 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3371241653019167252049973) ^ 37028308356 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_3872451941007946891916579 : Nat.Prime 3872451941007946891916579 := by
  apply lucas_primality 3872451941007946891916579 (2 : ZMod 3872451941007946891916579)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 2), (41, 1), (823, 1), (34589, 1), (4595440430387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 2), (41, 1), (823, 1), (34589, 1), (4595440430387, 1)] : List FactorBlock).map factorBlockValue).prod) = 3872451941007946891916579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_19
      · exact prime_oneHundredFiftyNineFA_41
      · exact prime_oneHundredFiftyNineFA_823
      · exact prime_oneHundredFiftyNineFA_34589
      · exact prime_oneHundredFiftyNineFA_4595440430387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3872451941007946891916579) ^ 1936225970503973445958289 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3872451941007946891916579) ^ 203813260053049836416662 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3872451941007946891916579) ^ 94450047341657241266258 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3872451941007946891916579) ^ 4705287899159109224686 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3872451941007946891916579) ^ 111956169331520046602 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3872451941007946891916579) ^ 842672644694 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_3875086262056251617693393 : Nat.Prime 3875086262056251617693393 := by
  apply lucas_primality 3875086262056251617693393 (3 : ZMod 3875086262056251617693393)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (131, 1), (35831, 1), (1493719, 1), (34543175743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (131, 1), (35831, 1), (1493719, 1), (34543175743, 1)] : List FactorBlock).map factorBlockValue).prod) = 3875086262056251617693393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_131
      · exact prime_oneHundredFiftyNineFA_35831
      · exact prime_oneHundredFiftyNineFA_1493719
      · exact prime_oneHundredFiftyNineFA_34543175743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3875086262056251617693393) ^ 1937543131028125808846696 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 3875086262056251617693393) ^ 29580811160734745173232 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 3875086262056251617693393) ^ 108148984456371622832 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 3875086262056251617693393) ^ 2594253846979419568 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 3875086262056251617693393) ^ 112180949744944 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_4408236629044597377630713 : Nat.Prime 4408236629044597377630713 := by
  apply lucas_primality 4408236629044597377630713 (3 : ZMod 4408236629044597377630713)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 2), (4553963459756815472759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 2), (4553963459756815472759, 1)] : List FactorBlock).map factorBlockValue).prod) = 4408236629044597377630713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_11
      · exact prime_oneHundredFiftyNineFA_4553963459756815472759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4408236629044597377630713) ^ 2204118314522298688815356 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 4408236629044597377630713) ^ 400748784458599761602792 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 4408236629044597377630713) ^ 968 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_5311832336950712537068199 : Nat.Prime 5311832336950712537068199 := by
  apply lucas_primality 5311832336950712537068199 (7 : ZMod 5311832336950712537068199)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2655916168475356268534099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2655916168475356268534099, 1)] : List FactorBlock).map factorBlockValue).prod) = 5311832336950712537068199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_2655916168475356268534099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 5311832336950712537068199) ^ 2655916168475356268534099 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (7 : ZMod 5311832336950712537068199) ^ 2 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_12208900082636147689439923 : Nat.Prime 12208900082636147689439923 := by
  apply lucas_primality 12208900082636147689439923 (2 : ZMod 12208900082636147689439923)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (443, 1), (16503636659, 1), (278318393651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (443, 1), (16503636659, 1), (278318393651, 1)] : List FactorBlock).map factorBlockValue).prod) = 12208900082636147689439923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_443
      · exact prime_oneHundredFiftyNineFA_16503636659
      · exact prime_oneHundredFiftyNineFA_278318393651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12208900082636147689439923) ^ 6104450041318073844719961 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 12208900082636147689439923) ^ 4069633360878715896479974 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 12208900082636147689439923) ^ 27559593865995818712054 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 12208900082636147689439923) ^ 739770290324358 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 12208900082636147689439923) ^ 43866666239622 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_13027057142920912402931843 : Nat.Prime 13027057142920912402931843 := by
  apply lucas_primality 13027057142920912402931843 (2 : ZMod 13027057142920912402931843)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (39521, 1), (425422253, 1), (387407651717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (39521, 1), (425422253, 1), (387407651717, 1)] : List FactorBlock).map factorBlockValue).prod) = 13027057142920912402931843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_39521
      · exact prime_oneHundredFiftyNineFA_425422253
      · exact prime_oneHundredFiftyNineFA_387407651717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13027057142920912402931843) ^ 6513528571460456201465921 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 13027057142920912402931843) ^ 329623672045770916802 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 13027057142920912402931843) ^ 30621475607015114 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 13027057142920912402931843) ^ 33626225721626 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_63399809299274457326916187 : Nat.Prime 63399809299274457326916187 := by
  apply lucas_primality 63399809299274457326916187 (5 : ZMod 63399809299274457326916187)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (29, 1), (173, 1), (193, 1), (19597, 1), (11364481303667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (29, 1), (173, 1), (193, 1), (19597, 1), (11364481303667, 1)] : List FactorBlock).map factorBlockValue).prod) = 63399809299274457326916187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_29
      · exact prime_oneHundredFiftyNineFA_173
      · exact prime_oneHundredFiftyNineFA_193
      · exact prime_oneHundredFiftyNineFA_19597
      · exact prime_oneHundredFiftyNineFA_11364481303667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 63399809299274457326916187) ^ 31699904649637228663458093 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 63399809299274457326916187) ^ 21133269766424819108972062 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 63399809299274457326916187) ^ 9057115614182065332416598 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 63399809299274457326916187) ^ 2186200320664636459548834 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 63399809299274457326916187) ^ 366472886122973741774082 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 63399809299274457326916187) ^ 328496421239764027600602 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 63399809299274457326916187) ^ 3235179328431620009538 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (5 : ZMod 63399809299274457326916187) ^ 5578768410558 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_431147785716396252234647923 : Nat.Prime 431147785716396252234647923 := by
  apply lucas_primality 431147785716396252234647923 (2 : ZMod 431147785716396252234647923)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (47, 1), (15541, 1), (4277305352602628447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (47, 1), (15541, 1), (4277305352602628447, 1)] : List FactorBlock).map factorBlockValue).prod) = 431147785716396252234647923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_23
      · exact prime_oneHundredFiftyNineFA_47
      · exact prime_oneHundredFiftyNineFA_15541
      · exact prime_oneHundredFiftyNineFA_4277305352602628447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 431147785716396252234647923) ^ 215573892858198126117323961 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 431147785716396252234647923) ^ 143715928572132084078215974 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 431147785716396252234647923) ^ 18745555900712880531941214 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 431147785716396252234647923) ^ 9173357142902047919886126 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 431147785716396252234647923) ^ 27742602516980648107242 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 431147785716396252234647923) ^ 100798926 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_480768374865342112466257019 : Nat.Prime 480768374865342112466257019 := by
  apply lucas_primality 480768374865342112466257019 (6 : ZMod 480768374865342112466257019)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 3), (19, 1), (36885712357322549675177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 3), (19, 1), (36885712357322549675177, 1)] : List FactorBlock).map factorBlockValue).prod) = 480768374865342112466257019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_19
      · exact prime_oneHundredFiftyNineFA_36885712357322549675177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 480768374865342112466257019) ^ 240384187432671056233128509 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (6 : ZMod 480768374865342112466257019) ^ 68681196409334587495179574 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (6 : ZMod 480768374865342112466257019) ^ 25303598677123269077171422 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (6 : ZMod 480768374865342112466257019) ^ 13034 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_2983816421783313745623912611 : Nat.Prime 2983816421783313745623912611 := by
  apply lucas_primality 2983816421783313745623912611 (2 : ZMod 2983816421783313745623912611)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (11, 1), (3875086262056251617693393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (11, 1), (3875086262056251617693393, 1)] : List FactorBlock).map factorBlockValue).prod) = 2983816421783313745623912611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_11
      · exact prime_oneHundredFiftyNineFA_3875086262056251617693393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2983816421783313745623912611) ^ 1491908210891656872811956305 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2983816421783313745623912611) ^ 596763284356662749124782522 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2983816421783313745623912611) ^ 426259488826187677946273230 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2983816421783313745623912611) ^ 271256038343937613238537510 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2983816421783313745623912611) ^ 770 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_4699510864308719149357662361 : Nat.Prime 4699510864308719149357662361 := by
  apply lucas_primality 4699510864308719149357662361 (26 : ZMod 4699510864308719149357662361)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (53, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (53, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 4699510864308719149357662361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_53
      · exact prime_oneHundredFiftyNineFA_171401
      · exact prime_oneHundredFiftyNineFA_714027719
      · exact prime_oneHundredFiftyNineFA_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 4699510864308719149357662361) ^ 2349755432154359574678831180 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (26 : ZMod 4699510864308719149357662361) ^ 1566503621436239716452554120 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (26 : ZMod 4699510864308719149357662361) ^ 939902172861743829871532472 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (26 : ZMod 4699510864308719149357662361) ^ 88670016307711682063352120 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (26 : ZMod 4699510864308719149357662361) ^ 27418223139355774758360 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (26 : ZMod 4699510864308719149357662361) ^ 6581692473914614440 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (26 : ZMod 4699510864308719149357662361) ^ 778369013809068840 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_5221678738120799054841847069 : Nat.Prime 5221678738120799054841847069 := by
  apply lucas_primality 5221678738120799054841847069 (2 : ZMod 5221678738120799054841847069)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (701, 1), (3613, 1), (5924407526678798057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (701, 1), (3613, 1), (5924407526678798057, 1)] : List FactorBlock).map factorBlockValue).prod) = 5221678738120799054841847069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_29
      · exact prime_oneHundredFiftyNineFA_701
      · exact prime_oneHundredFiftyNineFA_3613
      · exact prime_oneHundredFiftyNineFA_5924407526678798057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5221678738120799054841847069) ^ 2610839369060399527420923534 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5221678738120799054841847069) ^ 1740559579373599684947282356 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5221678738120799054841847069) ^ 180057887521406863960063692 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5221678738120799054841847069) ^ 7448899769073893088219468 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5221678738120799054841847069) ^ 1445247367318239428409036 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5221678738120799054841847069) ^ 881384124 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_5874388580385898936697077951 : Nat.Prime 5874388580385898936697077951 := by
  apply lucas_primality 5874388580385898936697077951 (3 : ZMod 5874388580385898936697077951)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (53, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (53, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 5874388580385898936697077951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_53
      · exact prime_oneHundredFiftyNineFA_171401
      · exact prime_oneHundredFiftyNineFA_714027719
      · exact prime_oneHundredFiftyNineFA_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5874388580385898936697077951) ^ 2937194290192949468348538975 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5874388580385898936697077951) ^ 1958129526795299645565692650 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5874388580385898936697077951) ^ 1174877716077179787339415590 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5874388580385898936697077951) ^ 110837520384639602579190150 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5874388580385898936697077951) ^ 34272778924194718447950 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5874388580385898936697077951) ^ 8227115592393268050 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5874388580385898936697077951) ^ 972961267261336050 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_7832518107181198582262770601 : Nat.Prime 7832518107181198582262770601 := by
  apply lucas_primality 7832518107181198582262770601 (6 : ZMod 7832518107181198582262770601)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (53, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (53, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 7832518107181198582262770601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_53
      · exact prime_oneHundredFiftyNineFA_171401
      · exact prime_oneHundredFiftyNineFA_714027719
      · exact prime_oneHundredFiftyNineFA_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 7832518107181198582262770601) ^ 3916259053590599291131385300 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (6 : ZMod 7832518107181198582262770601) ^ 1566503621436239716452554120 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (6 : ZMod 7832518107181198582262770601) ^ 147783360512852803438920200 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (6 : ZMod 7832518107181198582262770601) ^ 45697038565592957930600 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (6 : ZMod 7832518107181198582262770601) ^ 10969487456524357400 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (6 : ZMod 7832518107181198582262770601) ^ 1297281689681781400 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_46995108643087191493576623619 : Nat.Prime 46995108643087191493576623619 := by
  apply lucas_primality 46995108643087191493576623619 (2 : ZMod 46995108643087191493576623619)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (16843, 1), (69702169, 1), (953098149107887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (16843, 1), (69702169, 1), (953098149107887, 1)] : List FactorBlock).map factorBlockValue).prod) = 46995108643087191493576623619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_7
      · exact prime_oneHundredFiftyNineFA_16843
      · exact prime_oneHundredFiftyNineFA_69702169
      · exact prime_oneHundredFiftyNineFA_953098149107887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 46995108643087191493576623619) ^ 23497554321543595746788311809 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 46995108643087191493576623619) ^ 15665036214362397164525541206 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 46995108643087191493576623619) ^ 6713586949012455927653803374 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 46995108643087191493576623619) ^ 2790186347033615834089926 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 46995108643087191493576623619) ^ 674227349267813911122 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (2 : ZMod 46995108643087191493576623619) ^ 49307732563614 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_93990217286174382987153247241 : Nat.Prime 93990217286174382987153247241 := by
  apply lucas_primality 93990217286174382987153247241 (3 : ZMod 93990217286174382987153247241)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (17, 1), (41, 1), (3371241653019167252049973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (17, 1), (41, 1), (3371241653019167252049973, 1)] : List FactorBlock).map factorBlockValue).prod) = 93990217286174382987153247241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_5
      · exact prime_oneHundredFiftyNineFA_17
      · exact prime_oneHundredFiftyNineFA_41
      · exact prime_oneHundredFiftyNineFA_3371241653019167252049973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 93990217286174382987153247241) ^ 46995108643087191493576623620 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 93990217286174382987153247241) ^ 18798043457234876597430649448 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 93990217286174382987153247241) ^ 5528836310951434293361955720 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 93990217286174382987153247241) ^ 2292444324053033731393981640 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 93990217286174382987153247241) ^ 27880 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyNineFA_187980434572348765974306494467 : Nat.Prime 187980434572348765974306494467 := by
  apply lucas_primality 187980434572348765974306494467 (3 : ZMod 187980434572348765974306494467)
  · rw [← oneHundredFiftyNineFAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (223, 1), (15581651, 1), (3005535128788957469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (223, 1), (15581651, 1), (3005535128788957469, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyNineFA_2
      · exact prime_oneHundredFiftyNineFA_3
      · exact prime_oneHundredFiftyNineFA_223
      · exact prime_oneHundredFiftyNineFA_15581651
      · exact prime_oneHundredFiftyNineFA_3005535128788957469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 187980434572348765974306494467) ^ 93990217286174382987153247233 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 187980434572348765974306494467) ^ 62660144857449588658102164822 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 187980434572348765974306494467) ^ 842961590010532582844423742 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 187980434572348765974306494467) ^ 12064218006958875280566 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide
    · change (3 : ZMod 187980434572348765974306494467) ^ 62544747114 ≠ 1
      rw [← oneHundredFiftyNineFAFastPow_eq_pow]
      decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494394 : Nat.totient 187980434572348765974306494394 = 62611805144991398604240338208 := by
  rw [← show ((([(2, 1), (3, 4), (1453, 1), (12007, 1), (66511617530043304247, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494394 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_3, prime_oneHundredFiftyNineFA_1453, prime_oneHundredFiftyNineFA_12007, prime_oneHundredFiftyNineFA_66511617530043304247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494395 : Nat.totient 187980434572348765974306494395 = 121318464758142883307614268928 := by
  rw [← show ((([(5, 1), (7, 1), (17, 1), (209420447, 1), (1508608676988160103, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494395 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_5, prime_oneHundredFiftyNineFA_7, prime_oneHundredFiftyNineFA_17, prime_oneHundredFiftyNineFA_209420447, prime_oneHundredFiftyNineFA_1508608676988160103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494396 : Nat.totient 187980434572348765974306494396 = 93343414539497815507402863360 := by
  rw [← show ((([(2, 2), (181, 1), (733, 1), (64357477, 1), (5503907143145219, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494396 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_181, prime_oneHundredFiftyNineFA_733, prime_oneHundredFiftyNineFA_64357477, prime_oneHundredFiftyNineFA_5503907143145219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494397 : Nat.totient 187980434572348765974306494397 = 113850087065633638622347393200 := by
  rw [← show ((([(3, 1), (11, 1), (1471, 1), (3872451941007946891916579, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494397 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_3, prime_oneHundredFiftyNineFA_11, prime_oneHundredFiftyNineFA_1471, prime_oneHundredFiftyNineFA_3872451941007946891916579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494398 : Nat.totient 187980434572348765974306494398 = 91697772962117386689320928960 := by
  rw [← show ((([(2, 1), (41, 1), (36844185754483, 1), (62219975203933, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494398 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_41, prime_oneHundredFiftyNineFA_36844185754483, prime_oneHundredFiftyNineFA_62219975203933]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494399 : Nat.totient 187980434572348765974306494399 = 164285400254286600893940336000 := by
  rw [← show ((([(13, 1), (19, 1), (1607, 1), (5460491, 1), (7052371, 1), (12297957071, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494399 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_13, prime_oneHundredFiftyNineFA_19, prime_oneHundredFiftyNineFA_1607, prime_oneHundredFiftyNineFA_5460491, prime_oneHundredFiftyNineFA_7052371, prime_oneHundredFiftyNineFA_12297957071]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494400 : Nat.totient 187980434572348765974306494400 = 49182015358737949156724736000 := by
  rw [← show ((([(2, 6), (3, 1), (5, 2), (53, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494400 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_3, prime_oneHundredFiftyNineFA_5, prime_oneHundredFiftyNineFA_53, prime_oneHundredFiftyNineFA_171401, prime_oneHundredFiftyNineFA_714027719, prime_oneHundredFiftyNineFA_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494401 : Nat.totient 187980434572348765974306494401 = 187980407623993557662796007600 := by
  rw [← show ((([(6975581, 1), (26948355208311503511221, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494401 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_6975581, prime_oneHundredFiftyNineFA_26948355208311503511221]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494402 : Nat.totient 187980434572348765974306494402 = 79197258663848540524564356480 := by
  rw [← show ((([(2, 1), (7, 1), (59, 1), (255961, 1), (889116774081175360157, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494402 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_7, prime_oneHundredFiftyNineFA_59, prime_oneHundredFiftyNineFA_255961, prime_oneHundredFiftyNineFA_889116774081175360157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494403 : Nat.totient 187980434572348765974306494403 = 125306666463489795951130222416 := by
  rw [← show ((([(3, 2), (9199, 1), (2270541901563560845675333, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494403 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_3, prime_oneHundredFiftyNineFA_9199, prime_oneHundredFiftyNineFA_2270541901563560845675333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494404 : Nat.totient 187980434572348765974306494404 = 93831916301546482738635264000 := by
  rw [← show ((([(2, 2), (601, 1), (53791, 1), (789977, 1), (1955687, 1), (940924489, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494404 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_601, prime_oneHundredFiftyNineFA_53791, prime_oneHundredFiftyNineFA_789977, prime_oneHundredFiftyNineFA_1955687, prime_oneHundredFiftyNineFA_940924489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494405 : Nat.totient 187980434572348765974306494405 = 150384347376163014397999283968 := by
  rw [← show ((([(5, 1), (533815433, 1), (70428999594827662457, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494405 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_5, prime_oneHundredFiftyNineFA_533815433, prime_oneHundredFiftyNineFA_70428999594827662457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494406 : Nat.totient 187980434572348765974306494406 = 59830455424366933588419372224 := by
  rw [← show ((([(2, 1), (3, 1), (23, 1), (569, 1), (2393984291948100735772223, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494406 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_3, prime_oneHundredFiftyNineFA_23, prime_oneHundredFiftyNineFA_569, prime_oneHundredFiftyNineFA_2393984291948100735772223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494407 : Nat.totient 187980434572348765974306494407 = 187980434563857597729350494776 := by
  rw [← show ((([(22138347709, 1), (8491168222817651923, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494407 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_22138347709, prime_oneHundredFiftyNineFA_8491168222817651923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494408 : Nat.totient 187980434572348765974306494408 = 84010485137006312856593740800 := by
  rw [← show ((([(2, 3), (11, 2), (61, 1), (3673, 1), (7283, 1), (119008016981119919, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494408 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_11, prime_oneHundredFiftyNineFA_61, prime_oneHundredFiftyNineFA_3673, prime_oneHundredFiftyNineFA_7283, prime_oneHundredFiftyNineFA_119008016981119919]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494409 : Nat.totient 187980434572348765974306494409 = 107386334323613151910446240000 := by
  rw [← show ((([(3, 1), (7, 1), (4349, 1), (21487, 1), (145543, 1), (172751, 1), (3809923631, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494409 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_3, prime_oneHundredFiftyNineFA_7, prime_oneHundredFiftyNineFA_4349, prime_oneHundredFiftyNineFA_21487, prime_oneHundredFiftyNineFA_145543, prime_oneHundredFiftyNineFA_172751, prime_oneHundredFiftyNineFA_3809923631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494410 : Nat.totient 187980434572348765974306494410 = 75157086125242118402790880320 := by
  rw [← show ((([(2, 1), (5, 1), (2143, 1), (207769307, 1), (42219111271378541, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494410 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_5, prime_oneHundredFiftyNineFA_2143, prime_oneHundredFiftyNineFA_207769307, prime_oneHundredFiftyNineFA_42219111271378541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494411 : Nat.totient 187980434572348765974306494411 = 183385699600886399629742467752 := by
  rw [← show ((([(43, 1), (823, 1), (5311832336950712537068199, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494411 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_43, prime_oneHundredFiftyNineFA_823, prime_oneHundredFiftyNineFA_5311832336950712537068199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494412 : Nat.totient 187980434572348765974306494412 = 54072418727240047110711527424 := by
  rw [← show ((([(2, 2), (3, 2), (13, 1), (17, 1), (149, 1), (158573863103064139659323, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494412 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_3, prime_oneHundredFiftyNineFA_13, prime_oneHundredFiftyNineFA_17, prime_oneHundredFiftyNineFA_149, prime_oneHundredFiftyNineFA_158573863103064139659323]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494413 : Nat.totient 187980434572348765974306494413 = 187666608576468520049778433440 := by
  rw [← show ((([(599, 1), (84080531, 1), (3732418910315129977, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494413 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_599, prime_oneHundredFiftyNineFA_84080531, prime_oneHundredFiftyNineFA_3732418910315129977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494414 : Nat.totient 187980434572348765974306494414 = 92666408297092898857364805120 := by
  rw [← show ((([(2, 1), (71, 1), (29778929, 1), (44454448891364149873, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494414 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_71, prime_oneHundredFiftyNineFA_29778929, prime_oneHundredFiftyNineFA_44454448891364149873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494415 : Nat.totient 187980434572348765974306494415 = 96880999444794328883755783680 := by
  rw [← show ((([(3, 1), (5, 1), (47, 1), (79, 1), (1723957, 1), (1957807607855321821, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494415 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_3, prime_oneHundredFiftyNineFA_5, prime_oneHundredFiftyNineFA_47, prime_oneHundredFiftyNineFA_79, prime_oneHundredFiftyNineFA_1723957, prime_oneHundredFiftyNineFA_1957807607855321821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494416 : Nat.totient 187980434572348765974306494416 = 77944129632666238694713196544 := by
  rw [← show ((([(2, 4), (7, 1), (37, 1), (257, 1), (613, 1), (8513, 1), (33823354021088083, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494416 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_7, prime_oneHundredFiftyNineFA_37, prime_oneHundredFiftyNineFA_257, prime_oneHundredFiftyNineFA_613, prime_oneHundredFiftyNineFA_8513, prime_oneHundredFiftyNineFA_33823354021088083]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494417 : Nat.totient 187980434572348765974306494417 = 187980434572281345745527117936 := by
  rw [← show ((([(2788305715133, 1), (67417440473661349, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494417 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2788305715133, prime_oneHundredFiftyNineFA_67417440473661349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494418 : Nat.totient 187980434572348765974306494418 = 59362242495769294843880820240 := by
  rw [← show ((([(2, 1), (3, 1), (19, 1), (77914288607, 1), (21163655729137391, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494418 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_3, prime_oneHundredFiftyNineFA_19, prime_oneHundredFiftyNineFA_77914288607, prime_oneHundredFiftyNineFA_21163655729137391]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494419 : Nat.totient 187980434572348765974306494419 = 164998500444786879288286112160 := by
  rw [← show ((([(11, 1), (29, 1), (1371739483, 1), (429586205299135447, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494419 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_11, prime_oneHundredFiftyNineFA_29, prime_oneHundredFiftyNineFA_1371739483, prime_oneHundredFiftyNineFA_429586205299135447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494420 : Nat.totient 187980434572348765974306494420 = 74998823923206281261137950720 := by
  rw [← show ((([(2, 2), (5, 1), (389, 1), (2595331, 1), (3008207, 1), (3094799945617, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494420 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_5, prime_oneHundredFiftyNineFA_389, prime_oneHundredFiftyNineFA_2595331, prime_oneHundredFiftyNineFA_3008207, prime_oneHundredFiftyNineFA_3094799945617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494421 : Nat.totient 187980434572348765974306494421 = 121277690697648258181447038720 := by
  rw [← show ((([(3, 3), (31, 1), (13435817, 1), (16715643925665254249, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494421 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_3, prime_oneHundredFiftyNineFA_31, prime_oneHundredFiftyNineFA_13435817, prime_oneHundredFiftyNineFA_16715643925665254249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494422 : Nat.totient 187980434572348765974306494422 = 93776116563396395682346501632 := by
  rw [← show ((([(2, 1), (439, 1), (3231185881793, 1), (66260726117293, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494422 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_439, prime_oneHundredFiftyNineFA_3231185881793, prime_oneHundredFiftyNineFA_66260726117293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494423 : Nat.totient 187980434572348765974306494423 = 160308083960494477996908801024 := by
  rw [← show ((([(7, 1), (199, 1), (19267, 1), (49926029, 1), (140287963500577, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494423 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_7, prime_oneHundredFiftyNineFA_199, prime_oneHundredFiftyNineFA_19267, prime_oneHundredFiftyNineFA_49926029, prime_oneHundredFiftyNineFA_140287963500577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494424 : Nat.totient 187980434572348765974306494424 = 62660144857449588658102164800 := by
  rw [← show ((([(2, 3), (3, 1), (7832518107181198582262770601, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494424 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_3, prime_oneHundredFiftyNineFA_7832518107181198582262770601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494425 : Nat.totient 187980434572348765974306494425 = 138357814469756941433711232000 := by
  rw [← show ((([(5, 2), (13, 1), (659, 1), (787, 1), (1931, 1), (2636243, 1), (219079342061, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494425 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_5, prime_oneHundredFiftyNineFA_13, prime_oneHundredFiftyNineFA_659, prime_oneHundredFiftyNineFA_787, prime_oneHundredFiftyNineFA_1931, prime_oneHundredFiftyNineFA_2636243, prime_oneHundredFiftyNineFA_219079342061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494426 : Nat.totient 187980434572348765974306494426 = 93989768369097585463221895740 := by
  rw [← show ((([(2, 1), (209371, 1), (448917076797523931142103, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494426 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_209371, prime_oneHundredFiftyNineFA_448917076797523931142103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494427 : Nat.totient 187980434572348765974306494427 = 125319104999795167351689791520 := by
  rw [← show ((([(3, 1), (126047, 1), (678499, 1), (21696511, 1), (33769121923, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494427 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_3, prime_oneHundredFiftyNineFA_126047, prime_oneHundredFiftyNineFA_678499, prime_oneHundredFiftyNineFA_21696511, prime_oneHundredFiftyNineFA_33769121923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494428 : Nat.totient 187980434572348765974306494428 = 93127921714741590482683951152 := by
  rw [← show ((([(2, 2), (109, 1), (431147785716396252234647923, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494428 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_109, prime_oneHundredFiftyNineFA_431147785716396252234647923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494429 : Nat.totient 187980434572348765974306494429 = 169230467952600423588122470336 := by
  rw [← show ((([(17, 1), (23, 1), (480768374865342112466257019, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494429 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_17, prime_oneHundredFiftyNineFA_23, prime_oneHundredFiftyNineFA_480768374865342112466257019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494430 : Nat.totient 187980434572348765974306494430 = 39060869521527016306349391360 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (7, 2), (11, 1), (3875086262056251617693393, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494430 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_3, prime_oneHundredFiftyNineFA_5, prime_oneHundredFiftyNineFA_7, prime_oneHundredFiftyNineFA_11, prime_oneHundredFiftyNineFA_3875086262056251617693393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494431 : Nat.totient 187980434572348765974306494431 = 184793911650780731427362659392 := by
  rw [← show ((([(89, 1), (173, 1), (12208900082636147689439923, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494431 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_89, prime_oneHundredFiftyNineFA_173, prime_oneHundredFiftyNineFA_12208900082636147689439923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494432 : Nat.totient 187980434572348765974306494432 = 93990217286174382987153247200 := by
  rw [← show ((([(2, 5), (5874388580385898936697077951, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494432 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_5874388580385898936697077951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494433 : Nat.totient 187980434572348765974306494433 = 124389824065062634593794534400 := by
  rw [← show ((([(3, 1), (191, 1), (457, 1), (80233, 1), (8947234004842115141, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494433 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_3, prime_oneHundredFiftyNineFA_191, prime_oneHundredFiftyNineFA_457, prime_oneHundredFiftyNineFA_80233, prime_oneHundredFiftyNineFA_8947234004842115141]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494434 : Nat.totient 187980434572348765974306494434 = 93990217219844496053447816820 := by
  rw [← show ((([(2, 1), (1417011571, 1), (66329886932288418827, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494434 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_1417011571, prime_oneHundredFiftyNineFA_66329886932288418827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494435 : Nat.totient 187980434572348765974306494435 = 149758329842021972393858764800 := by
  rw [← show ((([(5, 1), (263, 1), (2861, 1), (80929, 1), (617397497147537221, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494435 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_5, prime_oneHundredFiftyNineFA_263, prime_oneHundredFiftyNineFA_2861, prime_oneHundredFiftyNineFA_80929, prime_oneHundredFiftyNineFA_617397497147537221]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494436 : Nat.totient 187980434572348765974306494436 = 62014061436769909101672483840 := by
  rw [← show ((([(2, 2), (3, 1), (97, 1), (604907, 1), (2312752087, 1), (115436188111, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494436 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_3, prime_oneHundredFiftyNineFA_97, prime_oneHundredFiftyNineFA_604907, prime_oneHundredFiftyNineFA_2312752087, prime_oneHundredFiftyNineFA_115436188111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494437 : Nat.totient 187980434572348765974306494437 = 152466830250571936351801663488 := by
  rw [← show ((([(7, 1), (19, 1), (1097, 1), (3833, 1), (336136413140095205089, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494437 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_7, prime_oneHundredFiftyNineFA_19, prime_oneHundredFiftyNineFA_1097, prime_oneHundredFiftyNineFA_3833, prime_oneHundredFiftyNineFA_336136413140095205089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494438 : Nat.totient 187980434572348765974306494438 = 85445243084501855437970460672 := by
  rw [← show ((([(2, 1), (13, 1), (137, 1), (157, 1), (643, 1), (522766932770166402449, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494438 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_13, prime_oneHundredFiftyNineFA_137, prime_oneHundredFiftyNineFA_157, prime_oneHundredFiftyNineFA_643, prime_oneHundredFiftyNineFA_522766932770166402449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494439 : Nat.totient 187980434572348765974306494439 = 122249557843992612658681689600 := by
  rw [← show ((([(3, 2), (41, 1), (8647, 1), (35601920213, 1), (1654807199021, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494439 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_3, prime_oneHundredFiftyNineFA_41, prime_oneHundredFiftyNineFA_8647, prime_oneHundredFiftyNineFA_35601920213, prime_oneHundredFiftyNineFA_1654807199021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494440 : Nat.totient 187980434572348765974306494440 = 75192173828939506389722597760 := by
  rw [← show ((([(2, 3), (5, 1), (4699510864308719149357662361, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494440 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_5, prime_oneHundredFiftyNineFA_4699510864308719149357662361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494441 : Nat.totient 187980434572348765974306494441 = 170827704847142268030408378000 := by
  rw [← show ((([(11, 1), (2687, 1), (11313494663, 1), (562154279761651, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494441 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_11, prime_oneHundredFiftyNineFA_2687, prime_oneHundredFiftyNineFA_11313494663, prime_oneHundredFiftyNineFA_562154279761651]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494442 : Nat.totient 187980434572348765974306494442 = 61176447941973048307103754240 := by
  rw [← show ((([(2, 1), (3, 1), (73, 1), (103, 1), (2417, 1), (1438441219, 1), (1198484838211, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494442 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_3, prime_oneHundredFiftyNineFA_73, prime_oneHundredFiftyNineFA_103, prime_oneHundredFiftyNineFA_2417, prime_oneHundredFiftyNineFA_1438441219, prime_oneHundredFiftyNineFA_1198484838211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494443 : Nat.totient 187980434572348765974306494443 = 187467619119299584134720952896 := by
  rw [← show ((([(367, 1), (312047, 1), (29222153, 1), (56171285512819, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494443 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_367, prime_oneHundredFiftyNineFA_312047, prime_oneHundredFiftyNineFA_29222153, prime_oneHundredFiftyNineFA_56171285512819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494444 : Nat.totient 187980434572348765974306494444 = 80560315149577949313369181440 := by
  rw [← show ((([(2, 2), (7, 1), (32063, 1), (374909, 1), (116206091, 1), (4806132109, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494444 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_7, prime_oneHundredFiftyNineFA_32063, prime_oneHundredFiftyNineFA_374909, prime_oneHundredFiftyNineFA_116206091, prime_oneHundredFiftyNineFA_4806132109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494445 : Nat.totient 187980434572348765974306494445 = 100255639668042032662314844160 := by
  rw [← show ((([(3, 1), (5, 1), (195281, 1), (1818233, 1), (4255697, 1), (8293563323, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494445 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_3, prime_oneHundredFiftyNineFA_5, prime_oneHundredFiftyNineFA_195281, prime_oneHundredFiftyNineFA_1818233, prime_oneHundredFiftyNineFA_4255697, prime_oneHundredFiftyNineFA_8293563323]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494446 : Nat.totient 187980434572348765974306494446 = 88370277587305362472173849600 := by
  rw [← show ((([(2, 1), (17, 1), (971, 1), (9871326761, 1), (576818225471149, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494446 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_17, prime_oneHundredFiftyNineFA_971, prime_oneHundredFiftyNineFA_9871326761, prime_oneHundredFiftyNineFA_576818225471149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494447 : Nat.totient 187980434572348765974306494447 = 187954985454949393003598308992 := by
  rw [← show ((([(7537, 1), (369917, 1), (67423274949127356043, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494447 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_7537, prime_oneHundredFiftyNineFA_369917, prime_oneHundredFiftyNineFA_67423274949127356043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494448 : Nat.totient 187980434572348765974306494448 = 60396424665513241555314892800 := by
  rw [← show ((([(2, 4), (3, 3), (29, 1), (701, 1), (3613, 1), (5924407526678798057, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494448 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_3, prime_oneHundredFiftyNineFA_29, prime_oneHundredFiftyNineFA_701, prime_oneHundredFiftyNineFA_3613, prime_oneHundredFiftyNineFA_5924407526678798057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494449 : Nat.totient 187980434572348765974306494449 = 187546263600760781018721914880 := by
  rw [← show ((([(433, 1), (8501447, 1), (13436279, 1), (3800606335681, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494449 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_433, prime_oneHundredFiftyNineFA_8501447, prime_oneHundredFiftyNineFA_13436279, prime_oneHundredFiftyNineFA_3800606335681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494450 : Nat.totient 187980434572348765974306494450 = 75078726133586009216121400320 := by
  rw [← show ((([(2, 1), (5, 2), (683, 1), (26759, 1), (136309, 1), (1509133049082193, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494450 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_5, prime_oneHundredFiftyNineFA_683, prime_oneHundredFiftyNineFA_26759, prime_oneHundredFiftyNineFA_136309, prime_oneHundredFiftyNineFA_1509133049082193]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494451 : Nat.totient 187980434572348765974306494451 = 98816103625475014210549401984 := by
  rw [← show ((([(3, 1), (7, 1), (13, 1), (293, 1), (2350078567957453724565959, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494451 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_3, prime_oneHundredFiftyNineFA_7, prime_oneHundredFiftyNineFA_13, prime_oneHundredFiftyNineFA_293, prime_oneHundredFiftyNineFA_2350078567957453724565959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494452 : Nat.totient 187980434572348765974306494452 = 79094151993671914328318918400 := by
  rw [← show ((([(2, 2), (11, 1), (23, 1), (31, 1), (263430948743, 1), (22745927311337, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494452 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_11, prime_oneHundredFiftyNineFA_23, prime_oneHundredFiftyNineFA_31, prime_oneHundredFiftyNineFA_263430948743, prime_oneHundredFiftyNineFA_22745927311337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494453 : Nat.totient 187980434572348765974306494453 = 179443185299698884635556665856 := by
  rw [← show ((([(37, 1), (53, 1), (31177, 1), (3074685732733041494149, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494453 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_37, prime_oneHundredFiftyNineFA_53, prime_oneHundredFiftyNineFA_31177, prime_oneHundredFiftyNineFA_3074685732733041494149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494454 : Nat.totient 187980434572348765974306494454 = 61202931131161473427965983232 := by
  rw [← show ((([(2, 1), (3, 1), (43, 1), (58002107, 1), (12561721862134067009, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494454 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_3, prime_oneHundredFiftyNineFA_43, prime_oneHundredFiftyNineFA_58002107, prime_oneHundredFiftyNineFA_12561721862134067009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494455 : Nat.totient 187980434572348765974306494455 = 150130748420681914950137528448 := by
  rw [← show ((([(5, 1), (593, 1), (63399809299274457326916187, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494455 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_5, prime_oneHundredFiftyNineFA_593, prime_oneHundredFiftyNineFA_63399809299274457326916187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494456 : Nat.totient 187980434572348765974306494456 = 89043363728745222935132835840 := by
  rw [← show ((([(2, 3), (19, 1), (5547333761, 1), (222938340944796773, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494456 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_19, prime_oneHundredFiftyNineFA_5547333761, prime_oneHundredFiftyNineFA_222938340944796773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494457 : Nat.totient 187980434572348765974306494457 = 125320289714705918336848661688 := by
  rw [← show ((([(3, 2), (648470840627, 1), (32209181421770699, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494457 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_3, prime_oneHundredFiftyNineFA_648470840627, prime_oneHundredFiftyNineFA_32209181421770699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494458 : Nat.totient 187980434572348765974306494458 = 79360609904654349247874601264 := by
  rw [← show ((([(2, 1), (7, 1), (67, 1), (886166400859, 1), (226148926853099, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494458 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_7, prime_oneHundredFiftyNineFA_67, prime_oneHundredFiftyNineFA_886166400859, prime_oneHundredFiftyNineFA_226148926853099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494459 : Nat.totient 187980434572348765974306494459 = 187976026335719721376928821104 := by
  rw [← show ((([(42643, 1), (4408236629044597377630713, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494459 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_42643, prime_oneHundredFiftyNineFA_4408236629044597377630713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494460 : Nat.totient 187980434572348765974306494460 = 49946217949141848158069597184 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (283, 1), (18743, 1), (47527, 1), (47533, 1), (261456974479, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494460 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_3, prime_oneHundredFiftyNineFA_5, prime_oneHundredFiftyNineFA_283, prime_oneHundredFiftyNineFA_18743, prime_oneHundredFiftyNineFA_47527, prime_oneHundredFiftyNineFA_47533, prime_oneHundredFiftyNineFA_261456974479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494461 : Nat.totient 187980434572348765974306494461 = 184207245967375648245221560320 := by
  rw [← show ((([(59, 1), (317, 1), (47969, 1), (631003, 1), (332054436000041, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494461 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_59, prime_oneHundredFiftyNineFA_317, prime_oneHundredFiftyNineFA_47969, prime_oneHundredFiftyNineFA_631003, prime_oneHundredFiftyNineFA_332054436000041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494462 : Nat.totient 187980434572348765974306494462 = 91990424513205931270751650008 := by
  rw [← show ((([(2, 1), (47, 1), (100446427, 1), (19909039244896649699, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494462 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_47, prime_oneHundredFiftyNineFA_100446427, prime_oneHundredFiftyNineFA_19909039244896649699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494463 : Nat.totient 187980434572348765974306494463 = 107225916332495300539958952960 := by
  rw [← show ((([(3, 1), (11, 1), (17, 1), (96753101927, 1), (3463258354190329, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494463 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_3, prime_oneHundredFiftyNineFA_11, prime_oneHundredFiftyNineFA_17, prime_oneHundredFiftyNineFA_96753101927, prime_oneHundredFiftyNineFA_3463258354190329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494464 : Nat.totient 187980434572348765974306494464 = 86760200531379556250379878400 := by
  rw [← show ((([(2, 11), (13, 1), (2143619521, 1), (3293757650744591, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494464 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_13, prime_oneHundredFiftyNineFA_2143619521, prime_oneHundredFiftyNineFA_3293757650744591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494465 : Nat.totient 187980434572348765974306494465 = 128710057498373354651677808064 := by
  rw [← show ((([(5, 1), (7, 1), (1087, 1), (1783, 1), (2771173502175542570419, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494465 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_5, prime_oneHundredFiftyNineFA_7, prime_oneHundredFiftyNineFA_1087, prime_oneHundredFiftyNineFA_1783, prime_oneHundredFiftyNineFA_2771173502175542570419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494466 : Nat.totient 187980434572348765974306494466 = 62379153657406619562841250400 := by
  rw [← show ((([(2, 1), (3, 2), (223, 1), (15581651, 1), (3005535128788957469, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494466 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_3, prime_oneHundredFiftyNineFA_223, prime_oneHundredFiftyNineFA_15581651, prime_oneHundredFiftyNineFA_3005535128788957469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494467 : Nat.totient 187980434572348765974306494467 = 187980434572348765974306494466 := by
  rw [← show ((([(187980434572348765974306494467, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494467 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_187980434572348765974306494467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494468 : Nat.totient 187980434572348765974306494468 = 93985593376237541624286716040 := by
  rw [← show ((([(2, 2), (20327, 1), (2311954968420681433245271, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494468 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_20327, prime_oneHundredFiftyNineFA_2311954968420681433245271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494469 : Nat.totient 187980434572348765974306494469 = 123265633753802335659800832000 := by
  rw [← show ((([(3, 1), (61, 1), (559841, 1), (25669421, 1), (71479381476463, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494469 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_3, prime_oneHundredFiftyNineFA_61, prime_oneHundredFiftyNineFA_559841, prime_oneHundredFiftyNineFA_25669421, prime_oneHundredFiftyNineFA_71479381476463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494470 : Nat.totient 187980434572348765974306494470 = 75192127924379751333427419040 := by
  rw [← show ((([(2, 1), (5, 1), (1638011, 1), (11476139938764072156677, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494470 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_5, prime_oneHundredFiftyNineFA_1638011, prime_oneHundredFiftyNineFA_11476139938764072156677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494471 : Nat.totient 187980434572348765974306494471 = 187949459564471721253631632128 := by
  rw [← show ((([(6829, 1), (54799, 1), (10237013, 1), (49069275802777, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494471 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_6829, prime_oneHundredFiftyNineFA_54799, prime_oneHundredFiftyNineFA_10237013, prime_oneHundredFiftyNineFA_49069275802777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494472 : Nat.totient 187980434572348765974306494472 = 53705506037203187917013472768 := by
  rw [← show ((([(2, 3), (3, 1), (7, 1), (16843, 1), (69702169, 1), (953098149107887, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494472 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_3, prime_oneHundredFiftyNineFA_7, prime_oneHundredFiftyNineFA_16843, prime_oneHundredFiftyNineFA_69702169, prime_oneHundredFiftyNineFA_953098149107887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494473 : Nat.totient 187980434572348765974306494473 = 185715036758647360044425695104 := by
  rw [← show ((([(83, 1), (348463, 1), (4603253, 1), (1411929592882729, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494473 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_83, prime_oneHundredFiftyNineFA_348463, prime_oneHundredFiftyNineFA_4603253, prime_oneHundredFiftyNineFA_1411929592882729]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494474 : Nat.totient 187980434572348765974306494474 = 85433387739015195256665708000 := by
  rw [← show ((([(2, 1), (11, 1), (6967, 1), (1226433932515291347353801, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494474 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_11, prime_oneHundredFiftyNineFA_6967, prime_oneHundredFiftyNineFA_1226433932515291347353801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494475 : Nat.totient 187980434572348765974306494475 = 90830996910508069387307520000 := by
  rw [← show ((([(3, 4), (5, 2), (19, 1), (23, 1), (10949, 1), (11731, 1), (30253, 1), (54667378301, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494475 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_3, prime_oneHundredFiftyNineFA_5, prime_oneHundredFiftyNineFA_19, prime_oneHundredFiftyNineFA_23, prime_oneHundredFiftyNineFA_10949, prime_oneHundredFiftyNineFA_11731, prime_oneHundredFiftyNineFA_30253, prime_oneHundredFiftyNineFA_54667378301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494476 : Nat.totient 187980434572348765974306494476 = 93990217286174382987153247236 := by
  rw [← show ((([(2, 2), (46995108643087191493576623619, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494476 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_46995108643087191493576623619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494477 : Nat.totient 187980434572348765974306494477 = 167521027083642198658505017344 := by
  rw [← show ((([(13, 1), (29, 1), (10529, 1), (47356998990119940549269, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494477 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_13, prime_oneHundredFiftyNineFA_29, prime_oneHundredFiftyNineFA_10529, prime_oneHundredFiftyNineFA_47356998990119940549269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494478 : Nat.totient 187980434572348765974306494478 = 62660136339818580118826446848 := by
  rw [← show ((([(2, 1), (3, 1), (7461073, 1), (525020833, 1), (7998040021757, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494478 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_3, prime_oneHundredFiftyNineFA_7461073, prime_oneHundredFiftyNineFA_525020833, prime_oneHundredFiftyNineFA_7998040021757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494479 : Nat.totient 187980434572348765974306494479 = 160859125357192625294150069760 := by
  rw [← show ((([(7, 2), (809, 1), (2731, 1), (18719, 1), (585799, 1), (158348909629, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494479 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_7, prime_oneHundredFiftyNineFA_809, prime_oneHundredFiftyNineFA_2731, prime_oneHundredFiftyNineFA_18719, prime_oneHundredFiftyNineFA_585799, prime_oneHundredFiftyNineFA_158348909629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494480 : Nat.totient 187980434572348765974306494480 = 69043029053832545321983426560 := by
  rw [← show ((([(2, 4), (5, 1), (17, 1), (41, 1), (3371241653019167252049973, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494480 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_5, prime_oneHundredFiftyNineFA_17, prime_oneHundredFiftyNineFA_41, prime_oneHundredFiftyNineFA_3371241653019167252049973]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494481 : Nat.totient 187980434572348765974306494481 = 125313130254848730793723482624 := by
  rw [← show ((([(3, 1), (19997, 1), (140407, 1), (22317101458347153313, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494481 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_3, prime_oneHundredFiftyNineFA_19997, prime_oneHundredFiftyNineFA_140407, prime_oneHundredFiftyNineFA_22317101458347153313]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494482 : Nat.totient 187980434572348765974306494482 = 93990217286174382987153247240 := by
  rw [← show ((([(2, 1), (93990217286174382987153247241, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494482 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_93990217286174382987153247241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494483 : Nat.totient 187980434572348765974306494483 = 181915520460524902834727281920 := by
  rw [← show ((([(31, 1), (176903, 1), (231754987, 1), (147906298737313, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494483 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_31, prime_oneHundredFiftyNineFA_176903, prime_oneHundredFiftyNineFA_231754987, prime_oneHundredFiftyNineFA_147906298737313]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494484 : Nat.totient 187980434572348765974306494484 = 62660144857449588658102164816 := by
  rw [← show ((([(2, 2), (3, 2), (5221678738120799054841847069, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494484 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_3, prime_oneHundredFiftyNineFA_5221678738120799054841847069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494485 : Nat.totient 187980434572348765974306494485 = 132999672669772469580659404800 := by
  rw [← show ((([(5, 1), (11, 1), (71, 1), (163, 1), (179, 1), (829, 1), (2579, 1), (524149, 1), (1472279759, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494485 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_5, prime_oneHundredFiftyNineFA_11, prime_oneHundredFiftyNineFA_71, prime_oneHundredFiftyNineFA_163, prime_oneHundredFiftyNineFA_179, prime_oneHundredFiftyNineFA_829, prime_oneHundredFiftyNineFA_2579, prime_oneHundredFiftyNineFA_524149, prime_oneHundredFiftyNineFA_1472279759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494486 : Nat.totient 187980434572348765974306494486 = 80510986286628543763813785600 := by
  rw [← show ((([(2, 1), (7, 1), (2213, 1), (5419, 1), (182179, 1), (229601, 1), (26767755673, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494486 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_7, prime_oneHundredFiftyNineFA_2213, prime_oneHundredFiftyNineFA_5419, prime_oneHundredFiftyNineFA_182179, prime_oneHundredFiftyNineFA_229601, prime_oneHundredFiftyNineFA_26767755673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494487 : Nat.totient 187980434572348765974306494487 = 124148999546306155580757208992 := by
  rw [← show ((([(3, 1), (107, 1), (1712219, 1), (342017481667622015413, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494487 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_3, prime_oneHundredFiftyNineFA_107, prime_oneHundredFiftyNineFA_1712219, prime_oneHundredFiftyNineFA_342017481667622015413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494488 : Nat.totient 187980434572348765974306494488 = 93902415832335223052587315200 := by
  rw [← show ((([(2, 3), (1103, 1), (36319, 1), (35567123, 1), (16491666006401, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494488 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_1103, prime_oneHundredFiftyNineFA_36319, prime_oneHundredFiftyNineFA_35567123, prime_oneHundredFiftyNineFA_16491666006401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494489 : Nat.totient 187980434572348765974306494489 = 187980434572162145141517990324 := by
  rw [← show ((([(1007290806703, 1), (186619825497697463, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494489 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_1007290806703, prime_oneHundredFiftyNineFA_186619825497697463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494490 : Nat.totient 187980434572348765974306494490 = 45021509485934673264532445952 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (13, 1), (37, 1), (13027057142920912402931843, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494490 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_3, prime_oneHundredFiftyNineFA_5, prime_oneHundredFiftyNineFA_13, prime_oneHundredFiftyNineFA_37, prime_oneHundredFiftyNineFA_13027057142920912402931843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494491 : Nat.totient 187980434572348765974306494491 = 187980433901525117618909975032 := by
  rw [← show ((([(280223327, 1), (670823648355116296133, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494491 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_280223327, prime_oneHundredFiftyNineFA_670823648355116296133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494492 : Nat.totient 187980434572348765974306494492 = 93989204689305962276880494400 := by
  rw [← show ((([(2, 2), (92821, 1), (273233758573, 1), (1852985661431, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494492 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_92821, prime_oneHundredFiftyNineFA_273233758573, prime_oneHundredFiftyNineFA_1852985661431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494493 : Nat.totient 187980434572348765974306494493 = 107417391184199294842460853960 := by
  rw [← show ((([(3, 2), (7, 1), (2983816421783313745623912611, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494493 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_3, prime_oneHundredFiftyNineFA_7, prime_oneHundredFiftyNineFA_2983816421783313745623912611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494494 : Nat.totient 187980434572348765974306494494 = 87045346841662945369376870400 := by
  rw [← show ((([(2, 1), (19, 1), (79, 1), (101, 1), (203393, 1), (3048207908181478079, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494494 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_2, prime_oneHundredFiftyNineFA_19, prime_oneHundredFiftyNineFA_79, prime_oneHundredFiftyNineFA_101, prime_oneHundredFiftyNineFA_203393, prime_oneHundredFiftyNineFA_3048207908181478079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyNineFA_187980434572348765974306494495 : Nat.totient 187980434572348765974306494495 = 150375273599054130094626936960 := by
  rw [← show ((([(5, 1), (16573, 1), (85485900683, 1), (26536706602061, 1)] : List FactorBlock).map factorBlockValue).prod) = 187980434572348765974306494495 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyNineFA_5, prime_oneHundredFiftyNineFA_16573, prime_oneHundredFiftyNineFA_85485900683, prime_oneHundredFiftyNineFA_26536706602061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredFiftyNineFA : certifiedKill 1 187980434572348765974306494393 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredFiftyNineFA_187980434572348765974306494394, phi_oneHundredFiftyNineFA_187980434572348765974306494395, phi_oneHundredFiftyNineFA_187980434572348765974306494396,
    phi_oneHundredFiftyNineFA_187980434572348765974306494397, phi_oneHundredFiftyNineFA_187980434572348765974306494398, phi_oneHundredFiftyNineFA_187980434572348765974306494399,
    phi_oneHundredFiftyNineFA_187980434572348765974306494400, phi_oneHundredFiftyNineFA_187980434572348765974306494401, phi_oneHundredFiftyNineFA_187980434572348765974306494402,
    phi_oneHundredFiftyNineFA_187980434572348765974306494403, phi_oneHundredFiftyNineFA_187980434572348765974306494404, phi_oneHundredFiftyNineFA_187980434572348765974306494405,
    phi_oneHundredFiftyNineFA_187980434572348765974306494406, phi_oneHundredFiftyNineFA_187980434572348765974306494407, phi_oneHundredFiftyNineFA_187980434572348765974306494408,
    phi_oneHundredFiftyNineFA_187980434572348765974306494409, phi_oneHundredFiftyNineFA_187980434572348765974306494410, phi_oneHundredFiftyNineFA_187980434572348765974306494411,
    phi_oneHundredFiftyNineFA_187980434572348765974306494412, phi_oneHundredFiftyNineFA_187980434572348765974306494413, phi_oneHundredFiftyNineFA_187980434572348765974306494414,
    phi_oneHundredFiftyNineFA_187980434572348765974306494415, phi_oneHundredFiftyNineFA_187980434572348765974306494416, phi_oneHundredFiftyNineFA_187980434572348765974306494417,
    phi_oneHundredFiftyNineFA_187980434572348765974306494418, phi_oneHundredFiftyNineFA_187980434572348765974306494419, phi_oneHundredFiftyNineFA_187980434572348765974306494420,
    phi_oneHundredFiftyNineFA_187980434572348765974306494421, phi_oneHundredFiftyNineFA_187980434572348765974306494422, phi_oneHundredFiftyNineFA_187980434572348765974306494423,
    phi_oneHundredFiftyNineFA_187980434572348765974306494424, phi_oneHundredFiftyNineFA_187980434572348765974306494425, phi_oneHundredFiftyNineFA_187980434572348765974306494426,
    phi_oneHundredFiftyNineFA_187980434572348765974306494427, phi_oneHundredFiftyNineFA_187980434572348765974306494428, phi_oneHundredFiftyNineFA_187980434572348765974306494429,
    phi_oneHundredFiftyNineFA_187980434572348765974306494430, phi_oneHundredFiftyNineFA_187980434572348765974306494431, phi_oneHundredFiftyNineFA_187980434572348765974306494432,
    phi_oneHundredFiftyNineFA_187980434572348765974306494433, phi_oneHundredFiftyNineFA_187980434572348765974306494434, phi_oneHundredFiftyNineFA_187980434572348765974306494435,
    phi_oneHundredFiftyNineFA_187980434572348765974306494436, phi_oneHundredFiftyNineFA_187980434572348765974306494437, phi_oneHundredFiftyNineFA_187980434572348765974306494438,
    phi_oneHundredFiftyNineFA_187980434572348765974306494439, phi_oneHundredFiftyNineFA_187980434572348765974306494440, phi_oneHundredFiftyNineFA_187980434572348765974306494441,
    phi_oneHundredFiftyNineFA_187980434572348765974306494442, phi_oneHundredFiftyNineFA_187980434572348765974306494443, phi_oneHundredFiftyNineFA_187980434572348765974306494444,
    phi_oneHundredFiftyNineFA_187980434572348765974306494445, phi_oneHundredFiftyNineFA_187980434572348765974306494446, phi_oneHundredFiftyNineFA_187980434572348765974306494447,
    phi_oneHundredFiftyNineFA_187980434572348765974306494448, phi_oneHundredFiftyNineFA_187980434572348765974306494449, phi_oneHundredFiftyNineFA_187980434572348765974306494450,
    phi_oneHundredFiftyNineFA_187980434572348765974306494451, phi_oneHundredFiftyNineFA_187980434572348765974306494452, phi_oneHundredFiftyNineFA_187980434572348765974306494453,
    phi_oneHundredFiftyNineFA_187980434572348765974306494454, phi_oneHundredFiftyNineFA_187980434572348765974306494455, phi_oneHundredFiftyNineFA_187980434572348765974306494456,
    phi_oneHundredFiftyNineFA_187980434572348765974306494457, phi_oneHundredFiftyNineFA_187980434572348765974306494458, phi_oneHundredFiftyNineFA_187980434572348765974306494459,
    phi_oneHundredFiftyNineFA_187980434572348765974306494460, phi_oneHundredFiftyNineFA_187980434572348765974306494461, phi_oneHundredFiftyNineFA_187980434572348765974306494462,
    phi_oneHundredFiftyNineFA_187980434572348765974306494463, phi_oneHundredFiftyNineFA_187980434572348765974306494464, phi_oneHundredFiftyNineFA_187980434572348765974306494465,
    phi_oneHundredFiftyNineFA_187980434572348765974306494466, phi_oneHundredFiftyNineFA_187980434572348765974306494467, phi_oneHundredFiftyNineFA_187980434572348765974306494468,
    phi_oneHundredFiftyNineFA_187980434572348765974306494469, phi_oneHundredFiftyNineFA_187980434572348765974306494470, phi_oneHundredFiftyNineFA_187980434572348765974306494471,
    phi_oneHundredFiftyNineFA_187980434572348765974306494472, phi_oneHundredFiftyNineFA_187980434572348765974306494473, phi_oneHundredFiftyNineFA_187980434572348765974306494474,
    phi_oneHundredFiftyNineFA_187980434572348765974306494475, phi_oneHundredFiftyNineFA_187980434572348765974306494476, phi_oneHundredFiftyNineFA_187980434572348765974306494477,
    phi_oneHundredFiftyNineFA_187980434572348765974306494478, phi_oneHundredFiftyNineFA_187980434572348765974306494479, phi_oneHundredFiftyNineFA_187980434572348765974306494480,
    phi_oneHundredFiftyNineFA_187980434572348765974306494481, phi_oneHundredFiftyNineFA_187980434572348765974306494482, phi_oneHundredFiftyNineFA_187980434572348765974306494483,
    phi_oneHundredFiftyNineFA_187980434572348765974306494484, phi_oneHundredFiftyNineFA_187980434572348765974306494485, phi_oneHundredFiftyNineFA_187980434572348765974306494486,
    phi_oneHundredFiftyNineFA_187980434572348765974306494487, phi_oneHundredFiftyNineFA_187980434572348765974306494488, phi_oneHundredFiftyNineFA_187980434572348765974306494489,
    phi_oneHundredFiftyNineFA_187980434572348765974306494490, phi_oneHundredFiftyNineFA_187980434572348765974306494491, phi_oneHundredFiftyNineFA_187980434572348765974306494492,
    phi_oneHundredFiftyNineFA_187980434572348765974306494493, phi_oneHundredFiftyNineFA_187980434572348765974306494494, phi_oneHundredFiftyNineFA_187980434572348765974306494495]

end TotientTailPeriodKiller
end Erdos249257
