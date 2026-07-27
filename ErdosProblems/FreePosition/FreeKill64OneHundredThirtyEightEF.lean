import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredThirtyEightEFFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredThirtyEightEFFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredThirtyEightEFFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredThirtyEightEFFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredThirtyEightEFFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredThirtyEightEFFastPow a n * oneHundredThirtyEightEFFastPow a n * a else oneHundredThirtyEightEFFastPow a n * oneHundredThirtyEightEFFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredThirtyEightEF_2 : Nat.Prime 2 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_3 : Nat.Prime 3 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_5 : Nat.Prime 5 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_7 : Nat.Prime 7 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_11 : Nat.Prime 11 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_13 : Nat.Prime 13 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_17 : Nat.Prime 17 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_19 : Nat.Prime 19 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_23 : Nat.Prime 23 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_29 : Nat.Prime 29 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_31 : Nat.Prime 31 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_37 : Nat.Prime 37 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_41 : Nat.Prime 41 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_43 : Nat.Prime 43 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_47 : Nat.Prime 47 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_53 : Nat.Prime 53 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_59 : Nat.Prime 59 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_61 : Nat.Prime 61 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_67 : Nat.Prime 67 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_71 : Nat.Prime 71 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_73 : Nat.Prime 73 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_79 : Nat.Prime 79 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_83 : Nat.Prime 83 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_89 : Nat.Prime 89 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_97 : Nat.Prime 97 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_101 : Nat.Prime 101 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_103 : Nat.Prime 103 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_107 : Nat.Prime 107 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_109 : Nat.Prime 109 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_113 : Nat.Prime 113 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_127 : Nat.Prime 127 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_131 : Nat.Prime 131 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_137 : Nat.Prime 137 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_139 : Nat.Prime 139 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_149 : Nat.Prime 149 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_151 : Nat.Prime 151 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_157 : Nat.Prime 157 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_163 : Nat.Prime 163 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_167 : Nat.Prime 167 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_173 : Nat.Prime 173 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_179 : Nat.Prime 179 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_181 : Nat.Prime 181 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_191 : Nat.Prime 191 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_197 : Nat.Prime 197 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_199 : Nat.Prime 199 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_211 : Nat.Prime 211 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_223 : Nat.Prime 223 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_227 : Nat.Prime 227 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_229 : Nat.Prime 229 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_233 : Nat.Prime 233 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_251 : Nat.Prime 251 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_257 : Nat.Prime 257 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_263 : Nat.Prime 263 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_269 : Nat.Prime 269 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_281 : Nat.Prime 281 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_283 : Nat.Prime 283 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_313 : Nat.Prime 313 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_317 : Nat.Prime 317 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_331 : Nat.Prime 331 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_337 : Nat.Prime 337 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_347 : Nat.Prime 347 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_349 : Nat.Prime 349 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_359 : Nat.Prime 359 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_367 : Nat.Prime 367 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_373 : Nat.Prime 373 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_379 : Nat.Prime 379 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_383 : Nat.Prime 383 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_389 : Nat.Prime 389 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_397 : Nat.Prime 397 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_401 : Nat.Prime 401 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_409 : Nat.Prime 409 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_419 : Nat.Prime 419 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_421 : Nat.Prime 421 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_433 : Nat.Prime 433 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_449 : Nat.Prime 449 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_457 : Nat.Prime 457 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_461 : Nat.Prime 461 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_463 : Nat.Prime 463 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_467 : Nat.Prime 467 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_479 : Nat.Prime 479 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_503 : Nat.Prime 503 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_521 : Nat.Prime 521 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_523 : Nat.Prime 523 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_547 : Nat.Prime 547 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_557 : Nat.Prime 557 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_577 : Nat.Prime 577 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_601 : Nat.Prime 601 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_607 : Nat.Prime 607 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_631 : Nat.Prime 631 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_641 : Nat.Prime 641 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_647 : Nat.Prime 647 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_659 : Nat.Prime 659 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_661 : Nat.Prime 661 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_673 : Nat.Prime 673 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_727 : Nat.Prime 727 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_733 : Nat.Prime 733 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_739 : Nat.Prime 739 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_769 : Nat.Prime 769 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_773 : Nat.Prime 773 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_797 : Nat.Prime 797 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_821 : Nat.Prime 821 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_863 : Nat.Prime 863 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_881 : Nat.Prime 881 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_883 : Nat.Prime 883 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_887 : Nat.Prime 887 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_937 : Nat.Prime 937 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_947 : Nat.Prime 947 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_967 : Nat.Prime 967 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_977 : Nat.Prime 977 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_997 : Nat.Prime 997 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1039 : Nat.Prime 1039 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1049 : Nat.Prime 1049 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1051 : Nat.Prime 1051 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1093 : Nat.Prime 1093 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1153 : Nat.Prime 1153 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1171 : Nat.Prime 1171 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1231 : Nat.Prime 1231 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1289 : Nat.Prime 1289 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1301 : Nat.Prime 1301 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1303 : Nat.Prime 1303 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1319 : Nat.Prime 1319 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1321 : Nat.Prime 1321 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1373 : Nat.Prime 1373 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1433 : Nat.Prime 1433 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1447 : Nat.Prime 1447 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1471 : Nat.Prime 1471 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1481 : Nat.Prime 1481 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1543 : Nat.Prime 1543 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1549 : Nat.Prime 1549 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1553 : Nat.Prime 1553 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1567 : Nat.Prime 1567 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1597 : Nat.Prime 1597 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1657 : Nat.Prime 1657 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1669 : Nat.Prime 1669 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1733 : Nat.Prime 1733 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1759 : Nat.Prime 1759 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1787 : Nat.Prime 1787 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1801 : Nat.Prime 1801 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1811 : Nat.Prime 1811 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1873 : Nat.Prime 1873 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1933 : Nat.Prime 1933 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_2039 : Nat.Prime 2039 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_2081 : Nat.Prime 2081 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_2161 : Nat.Prime 2161 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_2207 : Nat.Prime 2207 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_2251 : Nat.Prime 2251 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_2297 : Nat.Prime 2297 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_2311 : Nat.Prime 2311 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_2339 : Nat.Prime 2339 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_2393 : Nat.Prime 2393 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_2447 : Nat.Prime 2447 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_2549 : Nat.Prime 2549 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_2609 : Nat.Prime 2609 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_2633 : Nat.Prime 2633 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_2657 : Nat.Prime 2657 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_2671 : Nat.Prime 2671 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_2689 : Nat.Prime 2689 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_2719 : Nat.Prime 2719 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_2797 : Nat.Prime 2797 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_2833 : Nat.Prime 2833 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_2909 : Nat.Prime 2909 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_3037 : Nat.Prime 3037 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_3163 : Nat.Prime 3163 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_3221 : Nat.Prime 3221 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_3323 : Nat.Prime 3323 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_3371 : Nat.Prime 3371 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_3527 : Nat.Prime 3527 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_3541 : Nat.Prime 3541 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_3607 : Nat.Prime 3607 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_3739 : Nat.Prime 3739 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_3769 : Nat.Prime 3769 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_3943 : Nat.Prime 3943 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_4001 : Nat.Prime 4001 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_4093 : Nat.Prime 4093 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_4127 : Nat.Prime 4127 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_4337 : Nat.Prime 4337 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_4441 : Nat.Prime 4441 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_4481 : Nat.Prime 4481 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_4787 : Nat.Prime 4787 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_5009 : Nat.Prime 5009 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_5051 : Nat.Prime 5051 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_5237 : Nat.Prime 5237 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_5449 : Nat.Prime 5449 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_5519 : Nat.Prime 5519 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_5527 : Nat.Prime 5527 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_5573 : Nat.Prime 5573 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_5711 : Nat.Prime 5711 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_5849 : Nat.Prime 5849 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_6067 : Nat.Prime 6067 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_6397 : Nat.Prime 6397 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_6563 : Nat.Prime 6563 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_6761 : Nat.Prime 6761 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_6779 : Nat.Prime 6779 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_6863 : Nat.Prime 6863 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_7499 : Nat.Prime 7499 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_7537 : Nat.Prime 7537 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_7573 : Nat.Prime 7573 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_7793 : Nat.Prime 7793 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_7867 : Nat.Prime 7867 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_8273 : Nat.Prime 8273 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_8429 : Nat.Prime 8429 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_8521 : Nat.Prime 8521 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_8963 : Nat.Prime 8963 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_9431 : Nat.Prime 9431 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_9473 : Nat.Prime 9473 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_9619 : Nat.Prime 9619 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_9769 : Nat.Prime 9769 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_9811 : Nat.Prime 9811 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_10067 : Nat.Prime 10067 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_10093 : Nat.Prime 10093 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_10211 : Nat.Prime 10211 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_10487 : Nat.Prime 10487 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_10979 : Nat.Prime 10979 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_11047 : Nat.Prime 11047 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_11059 : Nat.Prime 11059 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_11131 : Nat.Prime 11131 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_11251 : Nat.Prime 11251 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_11383 : Nat.Prime 11383 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_11443 : Nat.Prime 11443 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_11863 : Nat.Prime 11863 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_11941 : Nat.Prime 11941 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_12487 : Nat.Prime 12487 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_12611 : Nat.Prime 12611 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_12713 : Nat.Prime 12713 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_12911 : Nat.Prime 12911 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_13063 : Nat.Prime 13063 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_13127 : Nat.Prime 13127 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_13381 : Nat.Prime 13381 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_14057 : Nat.Prime 14057 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_14303 : Nat.Prime 14303 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_15149 : Nat.Prime 15149 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_15217 : Nat.Prime 15217 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_15541 : Nat.Prime 15541 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_15643 : Nat.Prime 15643 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_16231 : Nat.Prime 16231 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_16573 : Nat.Prime 16573 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_16927 : Nat.Prime 16927 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_17203 : Nat.Prime 17203 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_17977 : Nat.Prime 17977 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_20063 : Nat.Prime 20063 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_20753 : Nat.Prime 20753 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_21617 : Nat.Prime 21617 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_23071 : Nat.Prime 23071 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_25117 : Nat.Prime 25117 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_25229 : Nat.Prime 25229 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_26777 : Nat.Prime 26777 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_28229 : Nat.Prime 28229 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_31177 : Nat.Prime 31177 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_31333 : Nat.Prime 31333 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_32119 : Nat.Prime 32119 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_34439 : Nat.Prime 34439 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_34519 : Nat.Prime 34519 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_35809 : Nat.Prime 35809 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_36011 : Nat.Prime 36011 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_36241 : Nat.Prime 36241 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_37561 : Nat.Prime 37561 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_40801 : Nat.Prime 40801 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_41387 : Nat.Prime 41387 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_41513 : Nat.Prime 41513 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_41579 : Nat.Prime 41579 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_42929 : Nat.Prime 42929 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_47513 : Nat.Prime 47513 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_47713 : Nat.Prime 47713 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_47947 : Nat.Prime 47947 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_48017 : Nat.Prime 48017 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_51047 : Nat.Prime 51047 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_56807 : Nat.Prime 56807 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_63029 : Nat.Prime 63029 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_64783 : Nat.Prime 64783 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_67043 : Nat.Prime 67043 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_69997 : Nat.Prime 69997 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_71483 : Nat.Prime 71483 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_73939 : Nat.Prime 73939 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_74531 : Nat.Prime 74531 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_75347 : Nat.Prime 75347 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_83933 : Nat.Prime 83933 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_88423 : Nat.Prime 88423 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_94463 : Nat.Prime 94463 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_95279 : Nat.Prime 95279 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_96697 : Nat.Prime 96697 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_97381 : Nat.Prime 97381 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_97729 : Nat.Prime 97729 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_100291 : Nat.Prime 100291 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_100669 : Nat.Prime 100669 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_101209 : Nat.Prime 101209 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_102317 : Nat.Prime 102317 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_102983 : Nat.Prime 102983 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_105667 : Nat.Prime 105667 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_125287 : Nat.Prime 125287 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_137443 : Nat.Prime 137443 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_137927 : Nat.Prime 137927 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_141277 : Nat.Prime 141277 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_141931 : Nat.Prime 141931 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_146389 : Nat.Prime 146389 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_148853 : Nat.Prime 148853 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_152729 : Nat.Prime 152729 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_157627 : Nat.Prime 157627 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_160967 : Nat.Prime 160967 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_162641 : Nat.Prime 162641 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_162787 : Nat.Prime 162787 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_168463 : Nat.Prime 168463 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_171401 : Nat.Prime 171401 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_174331 : Nat.Prime 174331 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_178571 : Nat.Prime 178571 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_182107 : Nat.Prime 182107 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_195469 : Nat.Prime 195469 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_196661 : Nat.Prime 196661 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_217697 : Nat.Prime 217697 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_222659 : Nat.Prime 222659 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_230341 : Nat.Prime 230341 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_245981 : Nat.Prime 245981 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_255043 : Nat.Prime 255043 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_260171 : Nat.Prime 260171 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_263489 : Nat.Prime 263489 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_263881 : Nat.Prime 263881 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_286619 : Nat.Prime 286619 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_294353 : Nat.Prime 294353 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_299731 : Nat.Prime 299731 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_316153 : Nat.Prime 316153 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_319981 : Nat.Prime 319981 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_341461 : Nat.Prime 341461 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_383909 : Nat.Prime 383909 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_393157 : Nat.Prime 393157 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_394019 : Nat.Prime 394019 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_432499 : Nat.Prime 432499 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_440831 : Nat.Prime 440831 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_458573 : Nat.Prime 458573 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_463339 : Nat.Prime 463339 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_507361 : Nat.Prime 507361 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_519119 : Nat.Prime 519119 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_531793 : Nat.Prime 531793 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_535573 : Nat.Prime 535573 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_589607 : Nat.Prime 589607 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_594397 : Nat.Prime 594397 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_601589 : Nat.Prime 601589 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_602603 : Nat.Prime 602603 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_697703 : Nat.Prime 697703 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_707827 : Nat.Prime 707827 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_732827 : Nat.Prime 732827 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_733283 : Nat.Prime 733283 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_768191 : Nat.Prime 768191 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_773767 : Nat.Prime 773767 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_778363 : Nat.Prime 778363 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_808919 : Nat.Prime 808919 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_843473 : Nat.Prime 843473 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_867037 : Nat.Prime 867037 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_930173 : Nat.Prime 930173 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_967567 : Nat.Prime 967567 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1000393 : Nat.Prime 1000393 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1033033 : Nat.Prime 1033033 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1084711 : Nat.Prime 1084711 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1188413 : Nat.Prime 1188413 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1204787 : Nat.Prime 1204787 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1236553 : Nat.Prime 1236553 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1294453 : Nat.Prime 1294453 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1317553 : Nat.Prime 1317553 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1348331 : Nat.Prime 1348331 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1357619 : Nat.Prime 1357619 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1369759 : Nat.Prime 1369759 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1453783 : Nat.Prime 1453783 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1476473 : Nat.Prime 1476473 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1510781 : Nat.Prime 1510781 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1518589 : Nat.Prime 1518589 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1547197 : Nat.Prime 1547197 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1574129 : Nat.Prime 1574129 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1651597 : Nat.Prime 1651597 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1657001 : Nat.Prime 1657001 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1723669 : Nat.Prime 1723669 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1822307 : Nat.Prime 1822307 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1948313 : Nat.Prime 1948313 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_1979491 : Nat.Prime 1979491 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_2001509 : Nat.Prime 2001509 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_2255251 : Nat.Prime 2255251 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_2282653 : Nat.Prime 2282653 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_2344333 : Nat.Prime 2344333 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_2651837 : Nat.Prime 2651837 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_2796587 : Nat.Prime 2796587 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_2927149 : Nat.Prime 2927149 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_2979359 : Nat.Prime 2979359 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_3026293 : Nat.Prime 3026293 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_3363713 : Nat.Prime 3363713 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_3388097 : Nat.Prime 3388097 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_3642377 : Nat.Prime 3642377 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_3818587 : Nat.Prime 3818587 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_4201583 : Nat.Prime 4201583 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_4209869 : Nat.Prime 4209869 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_4362427 : Nat.Prime 4362427 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_4545479 : Nat.Prime 4545479 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_4613569 : Nat.Prime 4613569 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_4667989 : Nat.Prime 4667989 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_4793587 : Nat.Prime 4793587 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_4804529 : Nat.Prime 4804529 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_4907897 : Nat.Prime 4907897 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_5004149 : Nat.Prime 5004149 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_5060051 : Nat.Prime 5060051 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_5820041 : Nat.Prime 5820041 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_5975227 : Nat.Prime 5975227 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_6016789 : Nat.Prime 6016789 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_6029851 : Nat.Prime 6029851 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_6336347 : Nat.Prime 6336347 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_6589883 : Nat.Prime 6589883 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_7502813 : Nat.Prime 7502813 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_8189161 : Nat.Prime 8189161 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_9642827 : Nat.Prime 9642827 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_9892381 : Nat.Prime 9892381 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_10080379 : Nat.Prime 10080379 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_10324637 : Nat.Prime 10324637 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_10820141 : Nat.Prime 10820141 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_11418499 : Nat.Prime 11418499 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_11861573 : Nat.Prime 11861573 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_12037637 : Nat.Prime 12037637 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_12146711 : Nat.Prime 12146711 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_13416959 : Nat.Prime 13416959 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_15019549 : Nat.Prime 15019549 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_15835373 : Nat.Prime 15835373 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_17777867 : Nat.Prime 17777867 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_18228577 : Nat.Prime 18228577 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_18641369 : Nat.Prime 18641369 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_19180019 : Nat.Prime 19180019 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_20292353 : Nat.Prime 20292353 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_21015017 : Nat.Prime 21015017 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_21527393 : Nat.Prime 21527393 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_22892927 : Nat.Prime 22892927 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_26475121 : Nat.Prime 26475121 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_26983799 : Nat.Prime 26983799 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_27073141 : Nat.Prime 27073141 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_27953789 : Nat.Prime 27953789 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_28460209 : Nat.Prime 28460209 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_28996589 : Nat.Prime 28996589 := by
  norm_num

private theorem prime_oneHundredThirtyEightEF_31120339 : Nat.Prime 31120339 := by
  apply lucas_primality 31120339 (2 : ZMod 31120339)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (73, 1), (227, 1), (313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (73, 1), (227, 1), (313, 1)] : List FactorBlock).map factorBlockValue).prod) = 31120339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_73
      · exact prime_oneHundredThirtyEightEF_227
      · exact prime_oneHundredThirtyEightEF_313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 31120339) ^ 15560169 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 31120339) ^ 10373446 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 31120339) ^ 426306 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 31120339) ^ 137094 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 31120339) ^ 99426 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_32582857 : Nat.Prime 32582857 := by
  apply lucas_primality 32582857 (11 : ZMod 32582857)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1357619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1357619, 1)] : List FactorBlock).map factorBlockValue).prod) = 32582857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_1357619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 32582857) ^ 16291428 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 32582857) ^ 10860952 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 32582857) ^ 24 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_33444289 : Nat.Prime 33444289 := by
  apply lucas_primality 33444289 (11 : ZMod 33444289)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (31, 1), (1873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (31, 1), (1873, 1)] : List FactorBlock).map factorBlockValue).prod) = 33444289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_31
      · exact prime_oneHundredThirtyEightEF_1873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 33444289) ^ 16722144 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 33444289) ^ 11148096 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 33444289) ^ 1078848 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 33444289) ^ 17856 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_39838129 : Nat.Prime 39838129 := by
  apply lucas_primality 39838129 (17 : ZMod 39838129)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (11, 1), (197, 1), (383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (11, 1), (197, 1), (383, 1)] : List FactorBlock).map factorBlockValue).prod) = 39838129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_11
      · exact prime_oneHundredThirtyEightEF_197
      · exact prime_oneHundredThirtyEightEF_383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 39838129) ^ 19919064 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (17 : ZMod 39838129) ^ 13279376 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (17 : ZMod 39838129) ^ 3621648 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (17 : ZMod 39838129) ^ 202224 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (17 : ZMod 39838129) ^ 104016 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_40174819 : Nat.Prime 40174819 := by
  apply lucas_primality 40174819 (3 : ZMod 40174819)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (79, 1), (131, 1), (647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (79, 1), (131, 1), (647, 1)] : List FactorBlock).map factorBlockValue).prod) = 40174819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_79
      · exact prime_oneHundredThirtyEightEF_131
      · exact prime_oneHundredThirtyEightEF_647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 40174819) ^ 20087409 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 40174819) ^ 13391606 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 40174819) ^ 508542 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 40174819) ^ 306678 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 40174819) ^ 62094 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_40331411 : Nat.Prime 40331411 := by
  apply lucas_primality 40331411 (6 : ZMod 40331411)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (53, 1), (1553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (53, 1), (1553, 1)] : List FactorBlock).map factorBlockValue).prod) = 40331411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_53
      · exact prime_oneHundredThirtyEightEF_1553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 40331411) ^ 20165705 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 40331411) ^ 8066282 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 40331411) ^ 5761630 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 40331411) ^ 760970 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 40331411) ^ 25970 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_41092771 : Nat.Prime 41092771 := by
  apply lucas_primality 41092771 (2 : ZMod 41092771)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1369759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1369759, 1)] : List FactorBlock).map factorBlockValue).prod) = 41092771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_1369759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 41092771) ^ 20546385 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 41092771) ^ 13697590 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 41092771) ^ 8218554 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 41092771) ^ 30 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_42233063 : Nat.Prime 42233063 := by
  apply lucas_primality 42233063 (5 : ZMod 42233063)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1301, 1), (16231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1301, 1), (16231, 1)] : List FactorBlock).map factorBlockValue).prod) = 42233063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_1301
      · exact prime_oneHundredThirtyEightEF_16231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 42233063) ^ 21116531 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 42233063) ^ 32462 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 42233063) ^ 2602 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_43054787 : Nat.Prime 43054787 := by
  apply lucas_primality 43054787 (2 : ZMod 43054787)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (21527393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (21527393, 1)] : List FactorBlock).map factorBlockValue).prod) = 43054787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_21527393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 43054787) ^ 21527393 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 43054787) ^ 2 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_44625793 : Nat.Prime 44625793 := by
  apply lucas_primality 44625793 (19 : ZMod 44625793)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (251, 1), (463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (251, 1), (463, 1)] : List FactorBlock).map factorBlockValue).prod) = 44625793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_251
      · exact prime_oneHundredThirtyEightEF_463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 44625793) ^ 22312896 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (19 : ZMod 44625793) ^ 14875264 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (19 : ZMod 44625793) ^ 177792 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (19 : ZMod 44625793) ^ 96384 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_45673997 : Nat.Prime 45673997 := by
  apply lucas_primality 45673997 (2 : ZMod 45673997)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11418499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11418499, 1)] : List FactorBlock).map factorBlockValue).prod) = 45673997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_11418499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 45673997) ^ 22836998 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 45673997) ^ 4 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_58233839 : Nat.Prime 58233839 := by
  apply lucas_primality 58233839 (11 : ZMod 58233839)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (23, 1), (97381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (23, 1), (97381, 1)] : List FactorBlock).map factorBlockValue).prod) = 58233839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_13
      · exact prime_oneHundredThirtyEightEF_23
      · exact prime_oneHundredThirtyEightEF_97381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 58233839) ^ 29116919 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 58233839) ^ 4479526 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 58233839) ^ 2531906 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 58233839) ^ 598 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_59929613 : Nat.Prime 59929613 := by
  apply lucas_primality 59929613 (2 : ZMod 59929613)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) = 59929613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_1811
      · exact prime_oneHundredThirtyEightEF_8273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59929613) ^ 29964806 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 33092 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 7244 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_60022561 : Nat.Prime 60022561 := by
  apply lucas_primality 60022561 (53 : ZMod 60022561)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (13, 1), (9619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (13, 1), (9619, 1)] : List FactorBlock).map factorBlockValue).prod) = 60022561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_13
      · exact prime_oneHundredThirtyEightEF_9619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (53 : ZMod 60022561) ^ 30011280 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (53 : ZMod 60022561) ^ 20007520 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (53 : ZMod 60022561) ^ 12004512 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (53 : ZMod 60022561) ^ 4617120 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (53 : ZMod 60022561) ^ 6240 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_68947763 : Nat.Prime 68947763 := by
  apply lucas_primality 68947763 (2 : ZMod 68947763)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (2651837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (2651837, 1)] : List FactorBlock).map factorBlockValue).prod) = 68947763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_13
      · exact prime_oneHundredThirtyEightEF_2651837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 68947763) ^ 34473881 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 68947763) ^ 5303674 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 68947763) ^ 26 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_71235979 : Nat.Prime 71235979 := by
  apply lucas_primality 71235979 (2 : ZMod 71235979)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (19, 1), (56807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (19, 1), (56807, 1)] : List FactorBlock).map factorBlockValue).prod) = 71235979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_11
      · exact prime_oneHundredThirtyEightEF_19
      · exact prime_oneHundredThirtyEightEF_56807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 71235979) ^ 35617989 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 71235979) ^ 23745326 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 71235979) ^ 6475998 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 71235979) ^ 3749262 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 71235979) ^ 1254 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_74701801 : Nat.Prime 74701801 := by
  apply lucas_primality 74701801 (21 : ZMod 74701801)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 2), (47, 1), (883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 2), (47, 1), (883, 1)] : List FactorBlock).map factorBlockValue).prod) = 74701801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_47
      · exact prime_oneHundredThirtyEightEF_883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (21 : ZMod 74701801) ^ 37350900 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (21 : ZMod 74701801) ^ 24900600 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (21 : ZMod 74701801) ^ 14940360 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (21 : ZMod 74701801) ^ 1589400 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (21 : ZMod 74701801) ^ 84600 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_80662823 : Nat.Prime 80662823 := by
  apply lucas_primality 80662823 (5 : ZMod 80662823)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (40331411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (40331411, 1)] : List FactorBlock).map factorBlockValue).prod) = 80662823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_40331411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 80662823) ^ 40331411 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 80662823) ^ 2 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_82782577 : Nat.Prime 82782577 := by
  apply lucas_primality 82782577 (7 : ZMod 82782577)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (173, 1), (3323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (173, 1), (3323, 1)] : List FactorBlock).map factorBlockValue).prod) = 82782577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_173
      · exact prime_oneHundredThirtyEightEF_3323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 82782577) ^ 41391288 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 82782577) ^ 27594192 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 82782577) ^ 478512 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 82782577) ^ 24912 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_84466127 : Nat.Prime 84466127 := by
  apply lucas_primality 84466127 (5 : ZMod 84466127)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (42233063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (42233063, 1)] : List FactorBlock).map factorBlockValue).prod) = 84466127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_42233063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 84466127) ^ 42233063 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 84466127) ^ 2 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_100515631 : Nat.Prime 100515631 := by
  apply lucas_primality 100515631 (13 : ZMod 100515631)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (167, 1), (20063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (167, 1), (20063, 1)] : List FactorBlock).map factorBlockValue).prod) = 100515631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_167
      · exact prime_oneHundredThirtyEightEF_20063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 100515631) ^ 50257815 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (13 : ZMod 100515631) ^ 33505210 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (13 : ZMod 100515631) ^ 20103126 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (13 : ZMod 100515631) ^ 601890 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (13 : ZMod 100515631) ^ 5010 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_102211363 : Nat.Prime 102211363 := by
  apply lucas_primality 102211363 (3 : ZMod 102211363)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 2), (15643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 2), (15643, 1)] : List FactorBlock).map factorBlockValue).prod) = 102211363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_11
      · exact prime_oneHundredThirtyEightEF_15643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 102211363) ^ 51105681 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 102211363) ^ 34070454 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 102211363) ^ 9291942 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 102211363) ^ 6534 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_126090103 : Nat.Prime 126090103 := by
  apply lucas_primality 126090103 (3 : ZMod 126090103)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (21015017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (21015017, 1)] : List FactorBlock).map factorBlockValue).prod) = 126090103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_21015017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 126090103) ^ 63045051 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 126090103) ^ 42030034 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 126090103) ^ 6 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_128368939 : Nat.Prime 128368939 := by
  apply lucas_primality 128368939 (3 : ZMod 128368939)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (47, 1), (26777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (47, 1), (26777, 1)] : List FactorBlock).map factorBlockValue).prod) = 128368939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_17
      · exact prime_oneHundredThirtyEightEF_47
      · exact prime_oneHundredThirtyEightEF_26777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 128368939) ^ 64184469 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 128368939) ^ 42789646 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 128368939) ^ 7551114 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 128368939) ^ 2731254 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 128368939) ^ 4794 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_134499857 : Nat.Prime 134499857 := by
  apply lucas_primality 134499857 (3 : ZMod 134499857)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (107, 1), (251, 1), (313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (107, 1), (251, 1), (313, 1)] : List FactorBlock).map factorBlockValue).prod) = 134499857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_107
      · exact prime_oneHundredThirtyEightEF_251
      · exact prime_oneHundredThirtyEightEF_313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 134499857) ^ 67249928 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 134499857) ^ 1257008 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 134499857) ^ 535856 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 134499857) ^ 429712 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_135352271 : Nat.Prime 135352271 := by
  apply lucas_primality 135352271 (13 : ZMod 135352271)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (71, 1), (379, 1), (503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (71, 1), (379, 1), (503, 1)] : List FactorBlock).map factorBlockValue).prod) = 135352271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_71
      · exact prime_oneHundredThirtyEightEF_379
      · exact prime_oneHundredThirtyEightEF_503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 135352271) ^ 67676135 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (13 : ZMod 135352271) ^ 27070454 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (13 : ZMod 135352271) ^ 1906370 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (13 : ZMod 135352271) ^ 357130 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (13 : ZMod 135352271) ^ 269090 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_141596309 : Nat.Prime 141596309 := by
  apply lucas_primality 141596309 (3 : ZMod 141596309)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (401, 1), (12611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (401, 1), (12611, 1)] : List FactorBlock).map factorBlockValue).prod) = 141596309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_401
      · exact prime_oneHundredThirtyEightEF_12611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 141596309) ^ 70798154 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 141596309) ^ 20228044 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 141596309) ^ 353108 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 141596309) ^ 11228 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_146280997 : Nat.Prime 146280997 := by
  apply lucas_primality 146280997 (2 : ZMod 146280997)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (601, 1), (6761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (601, 1), (6761, 1)] : List FactorBlock).map factorBlockValue).prod) = 146280997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_601
      · exact prime_oneHundredThirtyEightEF_6761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 146280997) ^ 73140498 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 146280997) ^ 48760332 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 146280997) ^ 243396 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 146280997) ^ 21636 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_157274357 : Nat.Prime 157274357 := by
  apply lucas_primality 157274357 (2 : ZMod 157274357)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (109, 1), (137, 1), (2633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (109, 1), (137, 1), (2633, 1)] : List FactorBlock).map factorBlockValue).prod) = 157274357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_109
      · exact prime_oneHundredThirtyEightEF_137
      · exact prime_oneHundredThirtyEightEF_2633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 157274357) ^ 78637178 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 157274357) ^ 1442884 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 157274357) ^ 1147988 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 157274357) ^ 59732 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_160699277 : Nat.Prime 160699277 := by
  apply lucas_primality 160699277 (2 : ZMod 160699277)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (40174819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (40174819, 1)] : List FactorBlock).map factorBlockValue).prod) = 160699277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_40174819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 160699277) ^ 80349638 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 160699277) ^ 4 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_173481629 : Nat.Prime 173481629 := by
  apply lucas_primality 173481629 (2 : ZMod 173481629)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (2282653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (2282653, 1)] : List FactorBlock).map factorBlockValue).prod) = 173481629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_19
      · exact prime_oneHundredThirtyEightEF_2282653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 173481629) ^ 86740814 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 173481629) ^ 9130612 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 173481629) ^ 76 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_174523673 : Nat.Prime 174523673 := by
  apply lucas_primality 174523673 (3 : ZMod 174523673)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (37, 1), (589607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (37, 1), (589607, 1)] : List FactorBlock).map factorBlockValue).prod) = 174523673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_37
      · exact prime_oneHundredThirtyEightEF_589607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 174523673) ^ 87261836 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 174523673) ^ 4716856 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 174523673) ^ 296 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_178503173 : Nat.Prime 178503173 := by
  apply lucas_primality 178503173 (2 : ZMod 178503173)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (44625793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (44625793, 1)] : List FactorBlock).map factorBlockValue).prod) = 178503173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_44625793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 178503173) ^ 89251586 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 178503173) ^ 4 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_190157663 : Nat.Prime 190157663 := by
  apply lucas_primality 190157663 (5 : ZMod 190157663)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (5004149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (5004149, 1)] : List FactorBlock).map factorBlockValue).prod) = 190157663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_19
      · exact prime_oneHundredThirtyEightEF_5004149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 190157663) ^ 95078831 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 190157663) ^ 10008298 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 190157663) ^ 38 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_192649333 : Nat.Prime 192649333 := by
  apply lucas_primality 192649333 (5 : ZMod 192649333)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1669, 1), (9619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1669, 1), (9619, 1)] : List FactorBlock).map factorBlockValue).prod) = 192649333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_1669
      · exact prime_oneHundredThirtyEightEF_9619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 192649333) ^ 96324666 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 192649333) ^ 64216444 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 192649333) ^ 115428 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 192649333) ^ 20028 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_195940831 : Nat.Prime 195940831 := by
  apply lucas_primality 195940831 (6 : ZMod 195940831)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (67, 1), (71, 1), (1373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (67, 1), (71, 1), (1373, 1)] : List FactorBlock).map factorBlockValue).prod) = 195940831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_67
      · exact prime_oneHundredThirtyEightEF_71
      · exact prime_oneHundredThirtyEightEF_1373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 195940831) ^ 97970415 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 195940831) ^ 65313610 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 195940831) ^ 39188166 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 195940831) ^ 2924490 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 195940831) ^ 2759730 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 195940831) ^ 142710 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_204234839 : Nat.Prime 204234839 := by
  apply lucas_primality 204234839 (7 : ZMod 204234839)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (19, 1), (316153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (19, 1), (316153, 1)] : List FactorBlock).map factorBlockValue).prod) = 204234839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_17
      · exact prime_oneHundredThirtyEightEF_19
      · exact prime_oneHundredThirtyEightEF_316153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 204234839) ^ 102117419 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 204234839) ^ 12013814 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 204234839) ^ 10749202 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 204234839) ^ 646 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_237231461 : Nat.Prime 237231461 := by
  apply lucas_primality 237231461 (3 : ZMod 237231461)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11861573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11861573, 1)] : List FactorBlock).map factorBlockValue).prod) = 237231461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_11861573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 237231461) ^ 118615730 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 237231461) ^ 47446292 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 237231461) ^ 20 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_254695223 : Nat.Prime 254695223 := by
  apply lucas_primality 254695223 (5 : ZMod 254695223)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (251, 1), (507361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (251, 1), (507361, 1)] : List FactorBlock).map factorBlockValue).prod) = 254695223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_251
      · exact prime_oneHundredThirtyEightEF_507361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 254695223) ^ 127347611 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 254695223) ^ 1014722 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 254695223) ^ 502 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_254909047 : Nat.Prime 254909047 := by
  apply lucas_primality 254909047 (3 : ZMod 254909047)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (23, 1), (263881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (23, 1), (263881, 1)] : List FactorBlock).map factorBlockValue).prod) = 254909047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_23
      · exact prime_oneHundredThirtyEightEF_263881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 254909047) ^ 127454523 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 254909047) ^ 84969682 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 254909047) ^ 36415578 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 254909047) ^ 11083002 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 254909047) ^ 966 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_262621867 : Nat.Prime 262621867 := by
  apply lucas_primality 262621867 (5 : ZMod 262621867)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (23, 1), (146389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (23, 1), (146389, 1)] : List FactorBlock).map factorBlockValue).prod) = 262621867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_13
      · exact prime_oneHundredThirtyEightEF_23
      · exact prime_oneHundredThirtyEightEF_146389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 262621867) ^ 131310933 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 262621867) ^ 87540622 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 262621867) ^ 20201682 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 262621867) ^ 11418342 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 262621867) ^ 1794 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_290212613 : Nat.Prime 290212613 := by
  apply lucas_primality 290212613 (2 : ZMod 290212613)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (3818587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (3818587, 1)] : List FactorBlock).map factorBlockValue).prod) = 290212613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_19
      · exact prime_oneHundredThirtyEightEF_3818587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 290212613) ^ 145106306 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 290212613) ^ 15274348 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 290212613) ^ 76 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_299134639 : Nat.Prime 299134639 := by
  apply lucas_primality 299134639 (3 : ZMod 299134639)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (1510781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (1510781, 1)] : List FactorBlock).map factorBlockValue).prod) = 299134639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_11
      · exact prime_oneHundredThirtyEightEF_1510781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 299134639) ^ 149567319 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 299134639) ^ 99711546 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 299134639) ^ 27194058 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 299134639) ^ 198 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_318098309 : Nat.Prime 318098309 := by
  apply lucas_primality 318098309 (2 : ZMod 318098309)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (97, 1), (74531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (97, 1), (74531, 1)] : List FactorBlock).map factorBlockValue).prod) = 318098309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_11
      · exact prime_oneHundredThirtyEightEF_97
      · exact prime_oneHundredThirtyEightEF_74531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 318098309) ^ 159049154 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 318098309) ^ 28918028 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 318098309) ^ 3279364 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 318098309) ^ 4268 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_352648193 : Nat.Prime 352648193 := by
  apply lucas_primality 352648193 (3 : ZMod 352648193)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (13, 1), (59, 1), (449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (13, 1), (59, 1), (449, 1)] : List FactorBlock).map factorBlockValue).prod) = 352648193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_13
      · exact prime_oneHundredThirtyEightEF_59
      · exact prime_oneHundredThirtyEightEF_449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 352648193) ^ 176324096 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 352648193) ^ 27126784 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 352648193) ^ 5977088 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 352648193) ^ 785408 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_354994973 : Nat.Prime 354994973 := by
  apply lucas_primality 354994973 (2 : ZMod 354994973)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 2), (127, 1), (1321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 2), (127, 1), (1321, 1)] : List FactorBlock).map factorBlockValue).prod) = 354994973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_23
      · exact prime_oneHundredThirtyEightEF_127
      · exact prime_oneHundredThirtyEightEF_1321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 354994973) ^ 177497486 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 354994973) ^ 15434564 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 354994973) ^ 2795236 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 354994973) ^ 268732 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_361424183 : Nat.Prime 361424183 := by
  apply lucas_primality 361424183 (5 : ZMod 361424183)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 1), (1518589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 1), (1518589, 1)] : List FactorBlock).map factorBlockValue).prod) = 361424183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_17
      · exact prime_oneHundredThirtyEightEF_1518589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 361424183) ^ 180712091 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 361424183) ^ 51632026 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 361424183) ^ 21260246 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 361424183) ^ 238 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_374753263 : Nat.Prime 374753263 := by
  apply lucas_primality 374753263 (5 : ZMod 374753263)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (4804529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (4804529, 1)] : List FactorBlock).map factorBlockValue).prod) = 374753263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_13
      · exact prime_oneHundredThirtyEightEF_4804529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 374753263) ^ 187376631 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 374753263) ^ 124917754 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 374753263) ^ 28827174 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 374753263) ^ 78 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_386652991 : Nat.Prime 386652991 := by
  apply lucas_primality 386652991 (7 : ZMod 386652991)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (43, 1), (299731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (43, 1), (299731, 1)] : List FactorBlock).map factorBlockValue).prod) = 386652991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_43
      · exact prime_oneHundredThirtyEightEF_299731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 386652991) ^ 193326495 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 386652991) ^ 128884330 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 386652991) ^ 77330598 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 386652991) ^ 8991930 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 386652991) ^ 1290 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_481519921 : Nat.Prime 481519921 := by
  apply lucas_primality 481519921 (31 : ZMod 481519921)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (7, 1), (286619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (7, 1), (286619, 1)] : List FactorBlock).map factorBlockValue).prod) = 481519921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_286619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 481519921) ^ 240759960 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (31 : ZMod 481519921) ^ 160506640 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (31 : ZMod 481519921) ^ 96303984 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (31 : ZMod 481519921) ^ 68788560 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (31 : ZMod 481519921) ^ 1680 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_509390447 : Nat.Prime 509390447 := by
  apply lucas_primality 509390447 (5 : ZMod 509390447)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (254695223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (254695223, 1)] : List FactorBlock).map factorBlockValue).prod) = 509390447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_254695223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 509390447) ^ 254695223 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 509390447) ^ 2 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_561270557 : Nat.Prime 561270557 := by
  apply lucas_primality 561270557 (2 : ZMod 561270557)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (1822307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (1822307, 1)] : List FactorBlock).map factorBlockValue).prod) = 561270557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_11
      · exact prime_oneHundredThirtyEightEF_1822307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 561270557) ^ 280635278 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 561270557) ^ 80181508 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 561270557) ^ 51024596 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 561270557) ^ 308 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_597733831 : Nat.Prime 597733831 := by
  apply lucas_primality 597733831 (3 : ZMod 597733831)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (5, 1), (245981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (5, 1), (245981, 1)] : List FactorBlock).map factorBlockValue).prod) = 597733831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_245981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 597733831) ^ 298866915 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 597733831) ^ 199244610 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 597733831) ^ 119546766 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 597733831) ^ 2430 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_598445707 : Nat.Prime 598445707 := by
  apply lucas_primality 598445707 (2 : ZMod 598445707)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (1051, 1), (2207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (1051, 1), (2207, 1)] : List FactorBlock).map factorBlockValue).prod) = 598445707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_43
      · exact prime_oneHundredThirtyEightEF_1051
      · exact prime_oneHundredThirtyEightEF_2207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 598445707) ^ 299222853 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 598445707) ^ 199481902 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 598445707) ^ 13917342 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 598445707) ^ 569406 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 598445707) ^ 271158 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_620405717 : Nat.Prime 620405717 := by
  apply lucas_primality 620405717 (3 : ZMod 620405717)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (2339, 1), (9473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (2339, 1), (9473, 1)] : List FactorBlock).map factorBlockValue).prod) = 620405717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_2339
      · exact prime_oneHundredThirtyEightEF_9473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 620405717) ^ 310202858 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 620405717) ^ 88629388 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 620405717) ^ 265244 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 620405717) ^ 65492 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_640433267 : Nat.Prime 640433267 := by
  apply lucas_primality 640433267 (2 : ZMod 640433267)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) = 640433267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_11
      · exact prime_oneHundredThirtyEightEF_19
      · exact prime_oneHundredThirtyEightEF_61
      · exact prime_oneHundredThirtyEightEF_25117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 640433267) ^ 320216633 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 58221206 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 33707014 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 10498906 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 25498 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_653627833 : Nat.Prime 653627833 := by
  apply lucas_primality 653627833 (5 : ZMod 653627833)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (13, 1), (17, 2), (659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (13, 1), (17, 2), (659, 1)] : List FactorBlock).map factorBlockValue).prod) = 653627833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_11
      · exact prime_oneHundredThirtyEightEF_13
      · exact prime_oneHundredThirtyEightEF_17
      · exact prime_oneHundredThirtyEightEF_659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 653627833) ^ 326813916 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 653627833) ^ 217875944 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 653627833) ^ 59420712 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 653627833) ^ 50279064 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 653627833) ^ 38448696 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 653627833) ^ 991848 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_657846197 : Nat.Prime 657846197 := by
  apply lucas_primality 657846197 (2 : ZMod 657846197)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (19, 1), (1236553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (19, 1), (1236553, 1)] : List FactorBlock).map factorBlockValue).prod) = 657846197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_19
      · exact prime_oneHundredThirtyEightEF_1236553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 657846197) ^ 328923098 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 657846197) ^ 93978028 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 657846197) ^ 34623484 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 657846197) ^ 532 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_689092889 : Nat.Prime 689092889 := by
  apply lucas_primality 689092889 (3 : ZMod 689092889)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (43, 1), (182107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (43, 1), (182107, 1)] : List FactorBlock).map factorBlockValue).prod) = 689092889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_11
      · exact prime_oneHundredThirtyEightEF_43
      · exact prime_oneHundredThirtyEightEF_182107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 689092889) ^ 344546444 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 689092889) ^ 62644808 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 689092889) ^ 16025416 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 689092889) ^ 3784 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_709989947 : Nat.Prime 709989947 := by
  apply lucas_primality 709989947 (2 : ZMod 709989947)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (354994973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (354994973, 1)] : List FactorBlock).map factorBlockValue).prod) = 709989947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_354994973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 709989947) ^ 354994973 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 709989947) ^ 2 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_17203
      · exact prime_oneHundredThirtyEightEF_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_722848367 : Nat.Prime 722848367 := by
  apply lucas_primality 722848367 (5 : ZMod 722848367)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (361424183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (361424183, 1)] : List FactorBlock).map factorBlockValue).prod) = 722848367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_361424183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 722848367) ^ 361424183 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 722848367) ^ 2 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_759266029 : Nat.Prime 759266029 := by
  apply lucas_primality 759266029 (2 : ZMod 759266029)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (1231, 1), (5711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (1231, 1), (5711, 1)] : List FactorBlock).map factorBlockValue).prod) = 759266029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_1231
      · exact prime_oneHundredThirtyEightEF_5711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 759266029) ^ 379633014 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 759266029) ^ 253088676 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 759266029) ^ 616788 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 759266029) ^ 132948 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_885489461 : Nat.Prime 885489461 := by
  apply lucas_primality 885489461 (2 : ZMod 885489461)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (419, 1), (105667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (419, 1), (105667, 1)] : List FactorBlock).map factorBlockValue).prod) = 885489461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_419
      · exact prime_oneHundredThirtyEightEF_105667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 885489461) ^ 442744730 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 885489461) ^ 177097892 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 885489461) ^ 2113340 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 885489461) ^ 8380 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_960360977 : Nat.Prime 960360977 := by
  apply lucas_primality 960360977 (3 : ZMod 960360977)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (60022561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (60022561, 1)] : List FactorBlock).map factorBlockValue).prod) = 960360977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_60022561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 960360977) ^ 480180488 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 960360977) ^ 16 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_967881323 : Nat.Prime 967881323 := by
  apply lucas_primality 967881323 (2 : ZMod 967881323)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (409, 1), (40801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (409, 1), (40801, 1)] : List FactorBlock).map factorBlockValue).prod) = 967881323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_29
      · exact prime_oneHundredThirtyEightEF_409
      · exact prime_oneHundredThirtyEightEF_40801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 967881323) ^ 483940661 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 967881323) ^ 33375218 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 967881323) ^ 2366458 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 967881323) ^ 23722 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_977485711 : Nat.Prime 977485711 := by
  apply lucas_primality 977485711 (6 : ZMod 977485711)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (32582857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (32582857, 1)] : List FactorBlock).map factorBlockValue).prod) = 977485711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_32582857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 977485711) ^ 488742855 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 977485711) ^ 325828570 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 977485711) ^ 195497142 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 977485711) ^ 30 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_1157924129 : Nat.Prime 1157924129 := by
  apply lucas_primality 1157924129 (3 : ZMod 1157924129)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (17, 1), (1447, 1), (1471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (17, 1), (1447, 1), (1471, 1)] : List FactorBlock).map factorBlockValue).prod) = 1157924129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_17
      · exact prime_oneHundredThirtyEightEF_1447
      · exact prime_oneHundredThirtyEightEF_1471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1157924129) ^ 578962064 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1157924129) ^ 68113184 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1157924129) ^ 800224 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1157924129) ^ 787168 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_1174099891 : Nat.Prime 1174099891 := by
  apply lucas_primality 1174099891 (2 : ZMod 1174099891)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (31, 1), (881, 1), (1433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (31, 1), (881, 1), (1433, 1)] : List FactorBlock).map factorBlockValue).prod) = 1174099891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_31
      · exact prime_oneHundredThirtyEightEF_881
      · exact prime_oneHundredThirtyEightEF_1433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1174099891) ^ 587049945 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1174099891) ^ 391366630 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1174099891) ^ 234819978 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1174099891) ^ 37874190 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1174099891) ^ 1332690 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1174099891) ^ 819330 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_1383251491 : Nat.Prime 1383251491 := by
  apply lucas_primality 1383251491 (2 : ZMod 1383251491)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (19, 1), (808919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (19, 1), (808919, 1)] : List FactorBlock).map factorBlockValue).prod) = 1383251491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_19
      · exact prime_oneHundredThirtyEightEF_808919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1383251491) ^ 691625745 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1383251491) ^ 461083830 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1383251491) ^ 276650298 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1383251491) ^ 72802710 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1383251491) ^ 1710 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_1427244191 : Nat.Prime 1427244191 := by
  apply lucas_primality 1427244191 (7 : ZMod 1427244191)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (641, 1), (222659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (641, 1), (222659, 1)] : List FactorBlock).map factorBlockValue).prod) = 1427244191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_641
      · exact prime_oneHundredThirtyEightEF_222659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1427244191) ^ 713622095 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1427244191) ^ 285448838 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1427244191) ^ 2226590 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1427244191) ^ 6410 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_1650268649 : Nat.Prime 1650268649 := by
  apply lucas_primality 1650268649 (3 : ZMod 1650268649)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (4209869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (4209869, 1)] : List FactorBlock).map factorBlockValue).prod) = 1650268649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_4209869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1650268649) ^ 825134324 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1650268649) ^ 235752664 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1650268649) ^ 392 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_1704302833 : Nat.Prime 1704302833 := by
  apply lucas_primality 1704302833 (5 : ZMod 1704302833)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (3527, 1), (10067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (3527, 1), (10067, 1)] : List FactorBlock).map factorBlockValue).prod) = 1704302833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_3527
      · exact prime_oneHundredThirtyEightEF_10067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1704302833) ^ 852151416 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1704302833) ^ 568100944 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1704302833) ^ 483216 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1704302833) ^ 169296 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_2043987233 : Nat.Prime 2043987233 := by
  apply lucas_primality 2043987233 (6 : ZMod 2043987233)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (31, 1), (294353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (31, 1), (294353, 1)] : List FactorBlock).map factorBlockValue).prod) = 2043987233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_31
      · exact prime_oneHundredThirtyEightEF_294353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 2043987233) ^ 1021993616 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 2043987233) ^ 291998176 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 2043987233) ^ 65935072 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 2043987233) ^ 6944 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_2266639117 : Nat.Prime 2266639117 := by
  apply lucas_primality 2266639117 (2 : ZMod 2266639117)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (26983799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (26983799, 1)] : List FactorBlock).map factorBlockValue).prod) = 2266639117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_26983799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2266639117) ^ 1133319558 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2266639117) ^ 755546372 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2266639117) ^ 323805588 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2266639117) ^ 84 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_2871859811 : Nat.Prime 2871859811 := by
  apply lucas_primality 2871859811 (2 : ZMod 2871859811)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (23, 1), (59, 2), (211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (23, 1), (59, 2), (211, 1)] : List FactorBlock).map factorBlockValue).prod) = 2871859811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_17
      · exact prime_oneHundredThirtyEightEF_23
      · exact prime_oneHundredThirtyEightEF_59
      · exact prime_oneHundredThirtyEightEF_211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2871859811) ^ 1435929905 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2871859811) ^ 574371962 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2871859811) ^ 168932930 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2871859811) ^ 124863470 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2871859811) ^ 48675590 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2871859811) ^ 13610710 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_3150604199 : Nat.Prime 3150604199 := by
  apply lucas_primality 3150604199 (7 : ZMod 3150604199)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (977, 1), (230341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (977, 1), (230341, 1)] : List FactorBlock).map factorBlockValue).prod) = 3150604199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_977
      · exact prime_oneHundredThirtyEightEF_230341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 3150604199) ^ 1575302099 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 3150604199) ^ 450086314 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 3150604199) ^ 3224774 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 3150604199) ^ 13678 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_3306201893 : Nat.Prime 3306201893 := by
  apply lucas_primality 3306201893 (2 : ZMod 3306201893)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (3221, 1), (5237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (3221, 1), (5237, 1)] : List FactorBlock).map factorBlockValue).prod) = 3306201893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_3221
      · exact prime_oneHundredThirtyEightEF_5237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3306201893) ^ 1653100946 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3306201893) ^ 472314556 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3306201893) ^ 1026452 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3306201893) ^ 631316 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_3865283993 : Nat.Prime 3865283993 := by
  apply lucas_primality 3865283993 (3 : ZMod 3865283993)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (59, 1), (8189161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (59, 1), (8189161, 1)] : List FactorBlock).map factorBlockValue).prod) = 3865283993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_59
      · exact prime_oneHundredThirtyEightEF_8189161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3865283993) ^ 1932641996 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3865283993) ^ 65513288 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3865283993) ^ 472 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_4484229943 : Nat.Prime 4484229943 := by
  apply lucas_primality 4484229943 (3 : ZMod 4484229943)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (18228577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (18228577, 1)] : List FactorBlock).map factorBlockValue).prod) = 4484229943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_41
      · exact prime_oneHundredThirtyEightEF_18228577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4484229943) ^ 2242114971 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 4484229943) ^ 1494743314 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 4484229943) ^ 109371462 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 4484229943) ^ 246 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_4786848419 : Nat.Prime 4786848419 := by
  apply lucas_primality 4786848419 (6 : ZMod 4786848419)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (73, 1), (547, 1), (5449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (73, 1), (547, 1), (5449, 1)] : List FactorBlock).map factorBlockValue).prod) = 4786848419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_11
      · exact prime_oneHundredThirtyEightEF_73
      · exact prime_oneHundredThirtyEightEF_547
      · exact prime_oneHundredThirtyEightEF_5449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 4786848419) ^ 2393424209 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 4786848419) ^ 435168038 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 4786848419) ^ 65573266 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 4786848419) ^ 8751094 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 4786848419) ^ 878482 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_5711277277 : Nat.Prime 5711277277 := by
  apply lucas_primality 5711277277 (2 : ZMod 5711277277)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (3163, 1), (5573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (3163, 1), (5573, 1)] : List FactorBlock).map factorBlockValue).prod) = 5711277277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_3163
      · exact prime_oneHundredThirtyEightEF_5573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5711277277) ^ 2855638638 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5711277277) ^ 1903759092 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5711277277) ^ 1805652 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5711277277) ^ 1024812 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_31
      · exact prime_oneHundredThirtyEightEF_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_6066709541 : Nat.Prime 6066709541 := by
  apply lucas_primality 6066709541 (3 : ZMod 6066709541)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (23, 3), (107, 1), (233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (23, 3), (107, 1), (233, 1)] : List FactorBlock).map factorBlockValue).prod) = 6066709541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_23
      · exact prime_oneHundredThirtyEightEF_107
      · exact prime_oneHundredThirtyEightEF_233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6066709541) ^ 3033354770 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 6066709541) ^ 1213341908 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 6066709541) ^ 263769980 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 6066709541) ^ 56698220 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 6066709541) ^ 26037380 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_6186447857 : Nat.Prime 6186447857 := by
  apply lucas_primality 6186447857 (3 : ZMod 6186447857)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (386652991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (386652991, 1)] : List FactorBlock).map factorBlockValue).prod) = 6186447857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_386652991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 6186447857) ^ 3093223928 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 6186447857) ^ 16 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_6358573219 : Nat.Prime 6358573219 := by
  apply lucas_primality 6358573219 (10 : ZMod 6358573219)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2311, 1), (458573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2311, 1), (458573, 1)] : List FactorBlock).map factorBlockValue).prod) = 6358573219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_2311
      · exact prime_oneHundredThirtyEightEF_458573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 6358573219) ^ 3179286609 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (10 : ZMod 6358573219) ^ 2119524406 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (10 : ZMod 6358573219) ^ 2751438 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (10 : ZMod 6358573219) ^ 13866 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_6437285321 : Nat.Prime 6437285321 := by
  apply lucas_primality 6437285321 (3 : ZMod 6437285321)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (631, 1), (255043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (631, 1), (255043, 1)] : List FactorBlock).map factorBlockValue).prod) = 6437285321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_631
      · exact prime_oneHundredThirtyEightEF_255043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6437285321) ^ 3218642660 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 6437285321) ^ 1287457064 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 6437285321) ^ 10201720 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 6437285321) ^ 25240 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_7003805749 : Nat.Prime 7003805749 := by
  apply lucas_primality 7003805749 (2 : ZMod 7003805749)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (59, 1), (9892381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (59, 1), (9892381, 1)] : List FactorBlock).map factorBlockValue).prod) = 7003805749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_59
      · exact prime_oneHundredThirtyEightEF_9892381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7003805749) ^ 3501902874 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 7003805749) ^ 2334601916 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 7003805749) ^ 118708572 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 7003805749) ^ 708 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_7730567987 : Nat.Prime 7730567987 := by
  apply lucas_primality 7730567987 (2 : ZMod 7730567987)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3865283993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3865283993, 1)] : List FactorBlock).map factorBlockValue).prod) = 7730567987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3865283993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 7730567987) ^ 3865283993 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 7730567987) ^ 2 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_8445692797 : Nat.Prime 8445692797 := by
  apply lucas_primality 8445692797 (2 : ZMod 8445692797)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (16927, 1), (41579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (16927, 1), (41579, 1)] : List FactorBlock).map factorBlockValue).prod) = 8445692797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_16927
      · exact prime_oneHundredThirtyEightEF_41579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8445692797) ^ 4222846398 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 8445692797) ^ 2815230932 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 8445692797) ^ 498948 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 8445692797) ^ 203124 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_8725427747 : Nat.Prime 8725427747 := by
  apply lucas_primality 8725427747 (2 : ZMod 8725427747)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (89, 1), (1000393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (89, 1), (1000393, 1)] : List FactorBlock).map factorBlockValue).prod) = 8725427747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_89
      · exact prime_oneHundredThirtyEightEF_1000393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8725427747) ^ 4362713873 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 8725427747) ^ 1246489678 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 8725427747) ^ 98038514 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 8725427747) ^ 8722 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_8770128203 : Nat.Prime 8770128203 := by
  apply lucas_primality 8770128203 (2 : ZMod 8770128203)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (113, 1), (227, 1), (15541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (113, 1), (227, 1), (15541, 1)] : List FactorBlock).map factorBlockValue).prod) = 8770128203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_11
      · exact prime_oneHundredThirtyEightEF_113
      · exact prime_oneHundredThirtyEightEF_227
      · exact prime_oneHundredThirtyEightEF_15541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8770128203) ^ 4385064101 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 8770128203) ^ 797284382 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 8770128203) ^ 77611754 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 8770128203) ^ 38634926 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 8770128203) ^ 564322 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_9568988021 : Nat.Prime 9568988021 := by
  apply lucas_primality 9568988021 (2 : ZMod 9568988021)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (3371, 1), (141931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (3371, 1), (141931, 1)] : List FactorBlock).map factorBlockValue).prod) = 9568988021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_3371
      · exact prime_oneHundredThirtyEightEF_141931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9568988021) ^ 4784494010 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 9568988021) ^ 1913797604 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 9568988021) ^ 2838620 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 9568988021) ^ 67420 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_13832514911 : Nat.Prime 13832514911 := by
  apply lucas_primality 13832514911 (13 : ZMod 13832514911)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1383251491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1383251491, 1)] : List FactorBlock).map factorBlockValue).prod) = 13832514911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_1383251491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 13832514911) ^ 6916257455 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (13 : ZMod 13832514911) ^ 2766502982 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (13 : ZMod 13832514911) ^ 10 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_14850902257 : Nat.Prime 14850902257 := by
  apply lucas_primality 14850902257 (5 : ZMod 14850902257)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (8963, 1), (34519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (8963, 1), (34519, 1)] : List FactorBlock).map factorBlockValue).prod) = 14850902257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_8963
      · exact prime_oneHundredThirtyEightEF_34519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 14850902257) ^ 7425451128 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 14850902257) ^ 4950300752 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 14850902257) ^ 1656912 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 14850902257) ^ 430224 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_20267579677 : Nat.Prime 20267579677 := by
  apply lucas_primality 20267579677 (5 : ZMod 20267579677)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (577, 1), (2927149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (577, 1), (2927149, 1)] : List FactorBlock).map factorBlockValue).prod) = 20267579677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_577
      · exact prime_oneHundredThirtyEightEF_2927149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 20267579677) ^ 10133789838 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 20267579677) ^ 6755859892 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 20267579677) ^ 35125788 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 20267579677) ^ 6924 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_20623198313 : Nat.Prime 20623198313 := by
  apply lucas_primality 20623198313 (3 : ZMod 20623198313)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (4337, 1), (594397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (4337, 1), (594397, 1)] : List FactorBlock).map factorBlockValue).prod) = 20623198313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_4337
      · exact prime_oneHundredThirtyEightEF_594397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 20623198313) ^ 10311599156 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 20623198313) ^ 4755176 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 20623198313) ^ 34696 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_22963759909 : Nat.Prime 22963759909 := by
  apply lucas_primality 22963759909 (2 : ZMod 22963759909)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (421, 1), (4545479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (421, 1), (4545479, 1)] : List FactorBlock).map factorBlockValue).prod) = 22963759909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_421
      · exact prime_oneHundredThirtyEightEF_4545479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 22963759909) ^ 11481879954 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 22963759909) ^ 7654586636 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 22963759909) ^ 54545748 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 22963759909) ^ 5052 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_25189640029 : Nat.Prime 25189640029 := by
  apply lucas_primality 25189640029 (2 : ZMod 25189640029)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (3541, 1), (28229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (3541, 1), (28229, 1)] : List FactorBlock).map factorBlockValue).prod) = 25189640029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_3541
      · exact prime_oneHundredThirtyEightEF_28229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 25189640029) ^ 12594820014 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 25189640029) ^ 8396546676 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 25189640029) ^ 3598520004 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 25189640029) ^ 7113708 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 25189640029) ^ 892332 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_27790179097 : Nat.Prime 27790179097 := by
  apply lucas_primality 27790179097 (10 : ZMod 27790179097)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1157924129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1157924129, 1)] : List FactorBlock).map factorBlockValue).prod) = 27790179097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_1157924129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 27790179097) ^ 13895089548 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (10 : ZMod 27790179097) ^ 9263393032 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (10 : ZMod 27790179097) ^ 24 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_28447597163 : Nat.Prime 28447597163 := by
  apply lucas_primality 28447597163 (2 : ZMod 28447597163)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1171, 1), (12146711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1171, 1), (12146711, 1)] : List FactorBlock).map factorBlockValue).prod) = 28447597163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_1171
      · exact prime_oneHundredThirtyEightEF_12146711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 28447597163) ^ 14223798581 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 28447597163) ^ 24293422 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 28447597163) ^ 2342 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_28718245007 : Nat.Prime 28718245007 := by
  apply lucas_primality 28718245007 (5 : ZMod 28718245007)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (157, 1), (739, 1), (11251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (157, 1), (739, 1), (11251, 1)] : List FactorBlock).map factorBlockValue).prod) = 28718245007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_11
      · exact prime_oneHundredThirtyEightEF_157
      · exact prime_oneHundredThirtyEightEF_739
      · exact prime_oneHundredThirtyEightEF_11251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 28718245007) ^ 14359122503 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 28718245007) ^ 2610749546 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 28718245007) ^ 182918758 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 28718245007) ^ 38860954 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 28718245007) ^ 2552506 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_29887239047 : Nat.Prime 29887239047 := by
  apply lucas_primality 29887239047 (5 : ZMod 29887239047)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (397, 1), (768191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (397, 1), (768191, 1)] : List FactorBlock).map factorBlockValue).prod) = 29887239047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_397
      · exact prime_oneHundredThirtyEightEF_768191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 29887239047) ^ 14943619523 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 29887239047) ^ 4269605578 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 29887239047) ^ 75282718 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 29887239047) ^ 38906 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_35965462487 : Nat.Prime 35965462487 := by
  apply lucas_primality 35965462487 (5 : ZMod 35965462487)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (127, 1), (141596309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (127, 1), (141596309, 1)] : List FactorBlock).map factorBlockValue).prod) = 35965462487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_127
      · exact prime_oneHundredThirtyEightEF_141596309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 35965462487) ^ 17982731243 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 35965462487) ^ 283192618 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 35965462487) ^ 254 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_37842672677 : Nat.Prime 37842672677 := by
  apply lucas_primality 37842672677 (2 : ZMod 37842672677)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (53, 1), (178503173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (53, 1), (178503173, 1)] : List FactorBlock).map factorBlockValue).prod) = 37842672677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_53
      · exact prime_oneHundredThirtyEightEF_178503173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 37842672677) ^ 18921336338 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 37842672677) ^ 714012692 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 37842672677) ^ 212 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_40299879761 : Nat.Prime 40299879761 := by
  apply lucas_primality 40299879761 (3 : ZMod 40299879761)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (7, 1), (83, 1), (867037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (7, 1), (83, 1), (867037, 1)] : List FactorBlock).map factorBlockValue).prod) = 40299879761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_83
      · exact prime_oneHundredThirtyEightEF_867037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 40299879761) ^ 20149939880 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 40299879761) ^ 8059975952 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 40299879761) ^ 5757125680 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 40299879761) ^ 485540720 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 40299879761) ^ 46480 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_41246396627 : Nat.Prime 41246396627 := by
  apply lucas_primality 41246396627 (2 : ZMod 41246396627)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (20623198313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (20623198313, 1)] : List FactorBlock).map factorBlockValue).prod) = 41246396627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_20623198313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 41246396627) ^ 20623198313 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 41246396627) ^ 2 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_41956621481 : Nat.Prime 41956621481 := by
  apply lucas_primality 41956621481 (3 : ZMod 41956621481)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (967, 1), (1084711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (967, 1), (1084711, 1)] : List FactorBlock).map factorBlockValue).prod) = 41956621481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_967
      · exact prime_oneHundredThirtyEightEF_1084711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 41956621481) ^ 20978310740 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 41956621481) ^ 8391324296 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 41956621481) ^ 43388440 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 41956621481) ^ 38680 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_45103926401 : Nat.Prime 45103926401 := by
  apply lucas_primality 45103926401 (3 : ZMod 45103926401)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 2), (13, 1), (83, 1), (13063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 2), (13, 1), (83, 1), (13063, 1)] : List FactorBlock).map factorBlockValue).prod) = 45103926401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_13
      · exact prime_oneHundredThirtyEightEF_83
      · exact prime_oneHundredThirtyEightEF_13063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 45103926401) ^ 22551963200 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 45103926401) ^ 9020785280 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 45103926401) ^ 3469532800 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 45103926401) ^ 543420800 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 45103926401) ^ 3452800 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_51312003367 : Nat.Prime 51312003367 := by
  apply lucas_primality 51312003367 (3 : ZMod 51312003367)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (657846197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (657846197, 1)] : List FactorBlock).map factorBlockValue).prod) = 51312003367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_13
      · exact prime_oneHundredThirtyEightEF_657846197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 51312003367) ^ 25656001683 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 51312003367) ^ 17104001122 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 51312003367) ^ 3947077182 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 51312003367) ^ 78 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_54490803541 : Nat.Prime 54490803541 := by
  apply lucas_primality 54490803541 (6 : ZMod 54490803541)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (37, 1), (4441, 1), (5527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (37, 1), (4441, 1), (5527, 1)] : List FactorBlock).map factorBlockValue).prod) = 54490803541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_37
      · exact prime_oneHundredThirtyEightEF_4441
      · exact prime_oneHundredThirtyEightEF_5527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 54490803541) ^ 27245401770 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 54490803541) ^ 18163601180 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 54490803541) ^ 10898160708 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 54490803541) ^ 1472724420 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 54490803541) ^ 12269940 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 54490803541) ^ 9859020 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_61059135443 : Nat.Prime 61059135443 := by
  apply lucas_primality 61059135443 (2 : ZMod 61059135443)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (709989947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (709989947, 1)] : List FactorBlock).map factorBlockValue).prod) = 61059135443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_43
      · exact prime_oneHundredThirtyEightEF_709989947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 61059135443) ^ 30529567721 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 61059135443) ^ 1419979894 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 61059135443) ^ 86 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_62258942191 : Nat.Prime 62258942191 := by
  apply lucas_primality 62258942191 (3 : ZMod 62258942191)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (23, 1), (229, 1), (394019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (23, 1), (229, 1), (394019, 1)] : List FactorBlock).map factorBlockValue).prod) = 62258942191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_23
      · exact prime_oneHundredThirtyEightEF_229
      · exact prime_oneHundredThirtyEightEF_394019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 62258942191) ^ 31129471095 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 62258942191) ^ 20752980730 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 62258942191) ^ 12451788438 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 62258942191) ^ 2706910530 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 62258942191) ^ 271873110 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 62258942191) ^ 158010 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_67452687761 : Nat.Prime 67452687761 := by
  apply lucas_primality 67452687761 (3 : ZMod 67452687761)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (283, 1), (2979359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (283, 1), (2979359, 1)] : List FactorBlock).map factorBlockValue).prod) = 67452687761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_283
      · exact prime_oneHundredThirtyEightEF_2979359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 67452687761) ^ 33726343880 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 67452687761) ^ 13490537552 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 67452687761) ^ 238348720 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 67452687761) ^ 22640 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_76904317697 : Nat.Prime 76904317697 := by
  apply lucas_primality 76904317697 (3 : ZMod 76904317697)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (29, 1), (449, 1), (23071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (29, 1), (449, 1), (23071, 1)] : List FactorBlock).map factorBlockValue).prod) = 76904317697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_29
      · exact prime_oneHundredThirtyEightEF_449
      · exact prime_oneHundredThirtyEightEF_23071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 76904317697) ^ 38452158848 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 76904317697) ^ 2651873024 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 76904317697) ^ 171279104 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 76904317697) ^ 3333376 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_91607156309 : Nat.Prime 91607156309 := by
  apply lucas_primality 91607156309 (2 : ZMod 91607156309)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (9769, 1), (2344333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (9769, 1), (2344333, 1)] : List FactorBlock).map factorBlockValue).prod) = 91607156309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_9769
      · exact prime_oneHundredThirtyEightEF_2344333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 91607156309) ^ 45803578154 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 91607156309) ^ 9377332 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 91607156309) ^ 39076 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_102802990987 : Nat.Prime 102802990987 := by
  apply lucas_primality 102802990987 (3 : ZMod 102802990987)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5711277277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5711277277, 1)] : List FactorBlock).map factorBlockValue).prod) = 102802990987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_5711277277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 102802990987) ^ 51401495493 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 102802990987) ^ 34267663662 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 102802990987) ^ 18 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_111259625221 : Nat.Prime 111259625221 := by
  apply lucas_primality 111259625221 (2 : ZMod 111259625221)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 5), (5, 1), (22892927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 5), (5, 1), (22892927, 1)] : List FactorBlock).map factorBlockValue).prod) = 111259625221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_22892927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 111259625221) ^ 55629812610 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 111259625221) ^ 37086541740 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 111259625221) ^ 22251925044 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 111259625221) ^ 4860 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_117068261411 : Nat.Prime 117068261411 := by
  apply lucas_primality 117068261411 (2 : ZMod 117068261411)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (5849, 1), (2001509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (5849, 1), (2001509, 1)] : List FactorBlock).map factorBlockValue).prod) = 117068261411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_5849
      · exact prime_oneHundredThirtyEightEF_2001509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 117068261411) ^ 58534130705 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 117068261411) ^ 23413652282 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 117068261411) ^ 20015090 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 117068261411) ^ 58490 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_121904674741 : Nat.Prime 121904674741 := by
  apply lucas_primality 121904674741 (7 : ZMod 121904674741)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (17, 1), (39838129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (17, 1), (39838129, 1)] : List FactorBlock).map factorBlockValue).prod) = 121904674741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_17
      · exact prime_oneHundredThirtyEightEF_39838129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 121904674741) ^ 60952337370 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 121904674741) ^ 40634891580 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 121904674741) ^ 24380934948 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 121904674741) ^ 7170863220 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 121904674741) ^ 3060 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_132155884583 : Nat.Prime 132155884583 := by
  apply lucas_primality 132155884583 (5 : ZMod 132155884583)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (51047, 1), (1294453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (51047, 1), (1294453, 1)] : List FactorBlock).map factorBlockValue).prod) = 132155884583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_51047
      · exact prime_oneHundredThirtyEightEF_1294453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 132155884583) ^ 66077942291 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 132155884583) ^ 2588906 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 132155884583) ^ 102094 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_143905252993 : Nat.Prime 143905252993 := by
  apply lucas_primality 143905252993 (7 : ZMod 143905252993)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (374753263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (374753263, 1)] : List FactorBlock).map factorBlockValue).prod) = 143905252993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_374753263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 143905252993) ^ 71952626496 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 143905252993) ^ 47968417664 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 143905252993) ^ 384 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_186937560239 : Nat.Prime 186937560239 := by
  apply lucas_primality 186937560239 (11 : ZMod 186937560239)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (13, 1), (653627833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (13, 1), (653627833, 1)] : List FactorBlock).map factorBlockValue).prod) = 186937560239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_11
      · exact prime_oneHundredThirtyEightEF_13
      · exact prime_oneHundredThirtyEightEF_653627833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 186937560239) ^ 93468780119 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 186937560239) ^ 16994323658 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 186937560239) ^ 14379812326 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 186937560239) ^ 286 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_190117865719 : Nat.Prime 190117865719 := by
  apply lucas_primality 190117865719 (11 : ZMod 190117865719)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (31, 1), (10324637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (31, 1), (10324637, 1)] : List FactorBlock).map factorBlockValue).prod) = 190117865719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_11
      · exact prime_oneHundredThirtyEightEF_31
      · exact prime_oneHundredThirtyEightEF_10324637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 190117865719) ^ 95058932859 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 190117865719) ^ 63372621906 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 190117865719) ^ 17283442338 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 190117865719) ^ 6132834378 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 190117865719) ^ 18414 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_202696627129 : Nat.Prime 202696627129 := by
  apply lucas_primality 202696627129 (7 : ZMod 202696627129)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (8445692797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (8445692797, 1)] : List FactorBlock).map factorBlockValue).prod) = 202696627129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_8445692797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 202696627129) ^ 101348313564 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 202696627129) ^ 67565542376 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 202696627129) ^ 24 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_230676166141 : Nat.Prime 230676166141 := by
  apply lucas_primality 230676166141 (6 : ZMod 230676166141)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 2), (107, 1), (733283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 2), (107, 1), (733283, 1)] : List FactorBlock).map factorBlockValue).prod) = 230676166141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_107
      · exact prime_oneHundredThirtyEightEF_733283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 230676166141) ^ 115338083070 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 230676166141) ^ 76892055380 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 230676166141) ^ 46135233228 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 230676166141) ^ 32953738020 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 230676166141) ^ 2155852020 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 230676166141) ^ 314580 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_232692650431 : Nat.Prime 232692650431 := by
  apply lucas_primality 232692650431 (3 : ZMod 232692650431)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (31, 1), (151, 1), (1657001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (31, 1), (151, 1), (1657001, 1)] : List FactorBlock).map factorBlockValue).prod) = 232692650431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_31
      · exact prime_oneHundredThirtyEightEF_151
      · exact prime_oneHundredThirtyEightEF_1657001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 232692650431) ^ 116346325215 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 232692650431) ^ 77564216810 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 232692650431) ^ 46538530086 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 232692650431) ^ 7506214530 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 232692650431) ^ 1541010930 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 232692650431) ^ 140430 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_237006365467 : Nat.Prime 237006365467 := by
  apply lucas_primality 237006365467 (3 : ZMod 237006365467)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (163, 1), (18641369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (163, 1), (18641369, 1)] : List FactorBlock).map factorBlockValue).prod) = 237006365467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_13
      · exact prime_oneHundredThirtyEightEF_163
      · exact prime_oneHundredThirtyEightEF_18641369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 237006365467) ^ 118503182733 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 237006365467) ^ 79002121822 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 237006365467) ^ 18231258882 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 237006365467) ^ 1454026782 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 237006365467) ^ 12714 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_243364641461 : Nat.Prime 243364641461 := by
  apply lucas_primality 243364641461 (2 : ZMod 243364641461)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) = 243364641461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_19
      · exact prime_oneHundredThirtyEightEF_640433267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 243364641461) ^ 121682320730 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 48672928292 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 12808665340 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 380 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_264496151441 : Nat.Prime 264496151441 := by
  apply lucas_primality 264496151441 (3 : ZMod 264496151441)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (3306201893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (3306201893, 1)] : List FactorBlock).map factorBlockValue).prod) = 264496151441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_3306201893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 264496151441) ^ 132248075720 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 264496151441) ^ 52899230288 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 264496151441) ^ 80 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_273736581179 : Nat.Prime 273736581179 := by
  apply lucas_primality 273736581179 (2 : ZMod 273736581179)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 2), (23, 1), (2719, 1), (7573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 2), (23, 1), (2719, 1), (7573, 1)] : List FactorBlock).map factorBlockValue).prod) = 273736581179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_17
      · exact prime_oneHundredThirtyEightEF_23
      · exact prime_oneHundredThirtyEightEF_2719
      · exact prime_oneHundredThirtyEightEF_7573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 273736581179) ^ 136868290589 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 273736581179) ^ 16102151834 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 273736581179) ^ 11901590486 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 273736581179) ^ 100675462 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 273736581179) ^ 36146386 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_302275680349 : Nat.Prime 302275680349 := by
  apply lucas_primality 302275680349 (2 : ZMod 302275680349)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (25189640029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (25189640029, 1)] : List FactorBlock).map factorBlockValue).prod) = 302275680349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_25189640029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 302275680349) ^ 151137840174 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 302275680349) ^ 100758560116 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 302275680349) ^ 12 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_309185255989 : Nat.Prime 309185255989 := by
  apply lucas_primality 309185255989 (6 : ZMod 309185255989)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (7537, 1), (162787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (7537, 1), (162787, 1)] : List FactorBlock).map factorBlockValue).prod) = 309185255989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_7537
      · exact prime_oneHundredThirtyEightEF_162787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 309185255989) ^ 154592627994 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 309185255989) ^ 103061751996 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 309185255989) ^ 44169322284 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 309185255989) ^ 41022324 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 309185255989) ^ 1899324 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_316138937033 : Nat.Prime 316138937033 := by
  apply lucas_primality 316138937033 (3 : ZMod 316138937033)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (89, 1), (337, 1), (1317553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (89, 1), (337, 1), (1317553, 1)] : List FactorBlock).map factorBlockValue).prod) = 316138937033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_89
      · exact prime_oneHundredThirtyEightEF_337
      · exact prime_oneHundredThirtyEightEF_1317553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 316138937033) ^ 158069468516 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 316138937033) ^ 3552122888 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 316138937033) ^ 938097736 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 316138937033) ^ 239944 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_381374519111 : Nat.Prime 381374519111 := by
  apply lucas_primality 381374519111 (11 : ZMod 381374519111)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (3769, 1), (778363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (3769, 1), (778363, 1)] : List FactorBlock).map factorBlockValue).prod) = 381374519111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_13
      · exact prime_oneHundredThirtyEightEF_3769
      · exact prime_oneHundredThirtyEightEF_778363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 381374519111) ^ 190687259555 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 381374519111) ^ 76274903822 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 381374519111) ^ 29336501470 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 381374519111) ^ 101187190 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 381374519111) ^ 489970 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_411211963949 : Nat.Prime 411211963949 := by
  apply lucas_primality 411211963949 (2 : ZMod 411211963949)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (102802990987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (102802990987, 1)] : List FactorBlock).map factorBlockValue).prod) = 411211963949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_102802990987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 411211963949) ^ 205605981974 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 411211963949) ^ 4 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_674716820003 : Nat.Prime 674716820003 := by
  apply lucas_primality 674716820003 (2 : ZMod 674716820003)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (733, 1), (27073141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (733, 1), (27073141, 1)] : List FactorBlock).map factorBlockValue).prod) = 674716820003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_17
      · exact prime_oneHundredThirtyEightEF_733
      · exact prime_oneHundredThirtyEightEF_27073141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 674716820003) ^ 337358410001 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 674716820003) ^ 39689224706 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 674716820003) ^ 920486794 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 674716820003) ^ 24922 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_714928392707 : Nat.Prime 714928392707 := by
  apply lucas_primality 714928392707 (2 : ZMod 714928392707)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (47, 1), (1801, 1), (383909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (47, 1), (1801, 1), (383909, 1)] : List FactorBlock).map factorBlockValue).prod) = 714928392707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_11
      · exact prime_oneHundredThirtyEightEF_47
      · exact prime_oneHundredThirtyEightEF_1801
      · exact prime_oneHundredThirtyEightEF_383909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 714928392707) ^ 357464196353 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 714928392707) ^ 64993490246 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 714928392707) ^ 15211242398 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 714928392707) ^ 396961906 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 714928392707) ^ 1862234 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_839521192987 : Nat.Prime 839521192987 := by
  apply lucas_primality 839521192987 (3 : ZMod 839521192987)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (31, 1), (5009, 1), (14303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (31, 1), (5009, 1), (14303, 1)] : List FactorBlock).map factorBlockValue).prod) = 839521192987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_31
      · exact prime_oneHundredThirtyEightEF_5009
      · exact prime_oneHundredThirtyEightEF_14303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 839521192987) ^ 419760596493 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 839521192987) ^ 279840397662 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 839521192987) ^ 119931598998 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 839521192987) ^ 27081328806 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 839521192987) ^ 167602554 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 839521192987) ^ 58695462 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_1001751151411 : Nat.Prime 1001751151411 := by
  apply lucas_primality 1001751151411 (10 : ZMod 1001751151411)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (149, 1), (74701801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (149, 1), (74701801, 1)] : List FactorBlock).map factorBlockValue).prod) = 1001751151411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_149
      · exact prime_oneHundredThirtyEightEF_74701801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1001751151411) ^ 500875575705 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (10 : ZMod 1001751151411) ^ 333917050470 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (10 : ZMod 1001751151411) ^ 200350230282 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (10 : ZMod 1001751151411) ^ 6723162090 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (10 : ZMod 1001751151411) ^ 13410 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_1110841405433 : Nat.Prime 1110841405433 := by
  apply lucas_primality 1110841405433 (3 : ZMod 1110841405433)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (19, 1), (457, 1), (1453783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (19, 1), (457, 1), (1453783, 1)] : List FactorBlock).map factorBlockValue).prod) = 1110841405433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_11
      · exact prime_oneHundredThirtyEightEF_19
      · exact prime_oneHundredThirtyEightEF_457
      · exact prime_oneHundredThirtyEightEF_1453783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1110841405433) ^ 555420702716 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1110841405433) ^ 100985582312 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1110841405433) ^ 58465337128 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1110841405433) ^ 2430725176 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1110841405433) ^ 764104 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_1290953195339 : Nat.Prime 1290953195339 := by
  apply lucas_primality 1290953195339 (2 : ZMod 1290953195339)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (107, 1), (35809, 1), (168463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (107, 1), (35809, 1), (168463, 1)] : List FactorBlock).map factorBlockValue).prod) = 1290953195339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_107
      · exact prime_oneHundredThirtyEightEF_35809
      · exact prime_oneHundredThirtyEightEF_168463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1290953195339) ^ 645476597669 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1290953195339) ^ 12064983134 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1290953195339) ^ 36051082 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1290953195339) ^ 7663126 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_1404819136933 : Nat.Prime 1404819136933 := by
  apply lucas_primality 1404819136933 (5 : ZMod 1404819136933)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (117068261411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (117068261411, 1)] : List FactorBlock).map factorBlockValue).prod) = 1404819136933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_117068261411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1404819136933) ^ 702409568466 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1404819136933) ^ 468273045644 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1404819136933) ^ 12 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_1459366549967 : Nat.Prime 1459366549967 := by
  apply lucas_primality 1459366549967 (5 : ZMod 1459366549967)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (67, 1), (179, 1), (409, 1), (11443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (67, 1), (179, 1), (409, 1), (11443, 1)] : List FactorBlock).map factorBlockValue).prod) = 1459366549967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_13
      · exact prime_oneHundredThirtyEightEF_67
      · exact prime_oneHundredThirtyEightEF_179
      · exact prime_oneHundredThirtyEightEF_409
      · exact prime_oneHundredThirtyEightEF_11443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1459366549967) ^ 729683274983 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1459366549967) ^ 112258965382 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1459366549967) ^ 21781590298 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1459366549967) ^ 8152885754 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1459366549967) ^ 3568133374 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1459366549967) ^ 127533562 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_1514516462477 : Nat.Prime 1514516462477 := by
  apply lucas_primality 1514516462477 (2 : ZMod 1514516462477)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37561, 1), (10080379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37561, 1), (10080379, 1)] : List FactorBlock).map factorBlockValue).prod) = 1514516462477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_37561
      · exact prime_oneHundredThirtyEightEF_10080379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1514516462477) ^ 757258231238 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1514516462477) ^ 40321516 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1514516462477) ^ 150244 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_1790439553367 : Nat.Prime 1790439553367 := by
  apply lucas_primality 1790439553367 (5 : ZMod 1790439553367)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (107, 1), (2297, 1), (3642377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (107, 1), (2297, 1), (3642377, 1)] : List FactorBlock).map factorBlockValue).prod) = 1790439553367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_107
      · exact prime_oneHundredThirtyEightEF_2297
      · exact prime_oneHundredThirtyEightEF_3642377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1790439553367) ^ 895219776683 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1790439553367) ^ 16733079938 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1790439553367) ^ 779468678 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1790439553367) ^ 491558 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_1905823651793 : Nat.Prime 1905823651793 := by
  apply lucas_primality 1905823651793 (3 : ZMod 1905823651793)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (23, 1), (379, 1), (1303, 1), (10487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (23, 1), (379, 1), (1303, 1), (10487, 1)] : List FactorBlock).map factorBlockValue).prod) = 1905823651793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_23
      · exact prime_oneHundredThirtyEightEF_379
      · exact prime_oneHundredThirtyEightEF_1303
      · exact prime_oneHundredThirtyEightEF_10487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1905823651793) ^ 952911825896 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1905823651793) ^ 82861897904 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1905823651793) ^ 5028558448 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1905823651793) ^ 1462642864 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1905823651793) ^ 181732016 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_2011890101909 : Nat.Prime 2011890101909 := by
  apply lucas_primality 2011890101909 (2 : ZMod 2011890101909)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (947, 1), (27953789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (947, 1), (27953789, 1)] : List FactorBlock).map factorBlockValue).prod) = 2011890101909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_19
      · exact prime_oneHundredThirtyEightEF_947
      · exact prime_oneHundredThirtyEightEF_27953789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2011890101909) ^ 1005945050954 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2011890101909) ^ 105888952732 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2011890101909) ^ 2124487964 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2011890101909) ^ 71972 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_2228379320971 : Nat.Prime 2228379320971 := by
  apply lucas_primality 2228379320971 (2 : ZMod 2228379320971)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (11, 1), (2909, 1), (773767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (11, 1), (2909, 1), (773767, 1)] : List FactorBlock).map factorBlockValue).prod) = 2228379320971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_11
      · exact prime_oneHundredThirtyEightEF_2909
      · exact prime_oneHundredThirtyEightEF_773767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2228379320971) ^ 1114189660485 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2228379320971) ^ 742793106990 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2228379320971) ^ 445675864194 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2228379320971) ^ 202579938270 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2228379320971) ^ 766029330 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2228379320971) ^ 2879910 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_2577668428667 : Nat.Prime 2577668428667 := by
  apply lucas_primality 2577668428667 (2 : ZMod 2577668428667)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4441, 1), (290212613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4441, 1), (290212613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2577668428667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_4441
      · exact prime_oneHundredThirtyEightEF_290212613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2577668428667) ^ 1288834214333 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2577668428667) ^ 580425226 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2577668428667) ^ 8882 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_2774343778169 : Nat.Prime 2774343778169 := by
  apply lucas_primality 2774343778169 (3 : ZMod 2774343778169)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (523, 1), (7499, 1), (88423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (523, 1), (7499, 1), (88423, 1)] : List FactorBlock).map factorBlockValue).prod) = 2774343778169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_523
      · exact prime_oneHundredThirtyEightEF_7499
      · exact prime_oneHundredThirtyEightEF_88423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2774343778169) ^ 1387171889084 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2774343778169) ^ 5304672616 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2774343778169) ^ 369961832 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2774343778169) ^ 31375816 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_2914397100929 : Nat.Prime 2914397100929 := by
  apply lucas_primality 2914397100929 (3 : ZMod 2914397100929)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (17, 1), (14057, 1), (95279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (17, 1), (14057, 1), (95279, 1)] : List FactorBlock).map factorBlockValue).prod) = 2914397100929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_17
      · exact prime_oneHundredThirtyEightEF_14057
      · exact prime_oneHundredThirtyEightEF_95279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2914397100929) ^ 1457198550464 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2914397100929) ^ 171435123584 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2914397100929) ^ 207327104 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2914397100929) ^ 30588032 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_3389662691873 : Nat.Prime 3389662691873 := by
  apply lucas_primality 3389662691873 (3 : ZMod 3389662691873)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (4001, 1), (26475121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (4001, 1), (26475121, 1)] : List FactorBlock).map factorBlockValue).prod) = 3389662691873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_4001
      · exact prime_oneHundredThirtyEightEF_26475121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3389662691873) ^ 1694831345936 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3389662691873) ^ 847203872 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3389662691873) ^ 128032 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_3777350514617 : Nat.Prime 3777350514617 := by
  apply lucas_primality 3777350514617 (3 : ZMod 3777350514617)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (67452687761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (67452687761, 1)] : List FactorBlock).map factorBlockValue).prod) = 3777350514617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_67452687761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3777350514617) ^ 1888675257308 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3777350514617) ^ 539621502088 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3777350514617) ^ 56 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_4119456777493 : Nat.Prime 4119456777493 := by
  apply lucas_primality 4119456777493 (2 : ZMod 4119456777493)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (281, 1), (174523673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (281, 1), (174523673, 1)] : List FactorBlock).map factorBlockValue).prod) = 4119456777493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_281
      · exact prime_oneHundredThirtyEightEF_174523673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4119456777493) ^ 2059728388746 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4119456777493) ^ 1373152259164 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4119456777493) ^ 588493825356 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4119456777493) ^ 14659988532 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4119456777493) ^ 23604 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_4148415406349 : Nat.Prime 4148415406349 := by
  apply lucas_primality 4148415406349 (2 : ZMod 4148415406349)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (397, 1), (16573, 1), (157627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (397, 1), (16573, 1), (157627, 1)] : List FactorBlock).map factorBlockValue).prod) = 4148415406349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_397
      · exact prime_oneHundredThirtyEightEF_16573
      · exact prime_oneHundredThirtyEightEF_157627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4148415406349) ^ 2074207703174 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4148415406349) ^ 10449409084 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4148415406349) ^ 250311676 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4148415406349) ^ 26317924 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_5131200336701 : Nat.Prime 5131200336701 := by
  apply lucas_primality 5131200336701 (2 : ZMod 5131200336701)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (51312003367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (51312003367, 1)] : List FactorBlock).map factorBlockValue).prod) = 5131200336701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_51312003367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5131200336701) ^ 2565600168350 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5131200336701) ^ 1026240067340 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5131200336701) ^ 100 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_5897138680963 : Nat.Prime 5897138680963 := by
  apply lucas_primality 5897138680963 (2 : ZMod 5897138680963)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (96697, 1), (3388097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (96697, 1), (3388097, 1)] : List FactorBlock).map factorBlockValue).prod) = 5897138680963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_96697
      · exact prime_oneHundredThirtyEightEF_3388097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5897138680963) ^ 2948569340481 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5897138680963) ^ 1965712893654 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5897138680963) ^ 60985746 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5897138680963) ^ 1740546 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_7578033636209 : Nat.Prime 7578033636209 := by
  apply lucas_primality 7578033636209 (3 : ZMod 7578033636209)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (41, 1), (1650268649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (41, 1), (1650268649, 1)] : List FactorBlock).map factorBlockValue).prod) = 7578033636209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_41
      · exact prime_oneHundredThirtyEightEF_1650268649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7578033636209) ^ 3789016818104 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 7578033636209) ^ 1082576233744 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 7578033636209) ^ 184830088688 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 7578033636209) ^ 4592 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_8467377278837 : Nat.Prime 8467377278837 := by
  apply lucas_primality 8467377278837 (2 : ZMod 8467377278837)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (64783, 1), (4667989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (64783, 1), (4667989, 1)] : List FactorBlock).map factorBlockValue).prod) = 8467377278837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_64783
      · exact prime_oneHundredThirtyEightEF_4667989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8467377278837) ^ 4233688639418 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 8467377278837) ^ 1209625325548 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 8467377278837) ^ 130703692 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 8467377278837) ^ 1813924 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_9570046137121 : Nat.Prime 9570046137121 := by
  apply lucas_primality 9570046137121 (11 : ZMod 9570046137121)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (7, 1), (9431, 1), (100669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (7, 1), (9431, 1), (100669, 1)] : List FactorBlock).map factorBlockValue).prod) = 9570046137121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_9431
      · exact prime_oneHundredThirtyEightEF_100669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 9570046137121) ^ 4785023068560 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 9570046137121) ^ 3190015379040 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 9570046137121) ^ 1914009227424 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 9570046137121) ^ 1367149448160 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 9570046137121) ^ 1014743520 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 9570046137121) ^ 95064480 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_9774554023907 : Nat.Prime 9774554023907 := by
  apply lucas_primality 9774554023907 (5 : ZMod 9774554023907)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (727, 1), (960360977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (727, 1), (960360977, 1)] : List FactorBlock).map factorBlockValue).prod) = 9774554023907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_727
      · exact prime_oneHundredThirtyEightEF_960360977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9774554023907) ^ 4887277011953 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 9774554023907) ^ 1396364860558 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 9774554023907) ^ 13445053678 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 9774554023907) ^ 10178 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_10382993943589 : Nat.Prime 10382993943589 := by
  apply lucas_primality 10382993943589 (13 : ZMod 10382993943589)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (19, 1), (722848367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (19, 1), (722848367, 1)] : List FactorBlock).map factorBlockValue).prod) = 10382993943589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_19
      · exact prime_oneHundredThirtyEightEF_722848367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 10382993943589) ^ 5191496971794 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (13 : ZMod 10382993943589) ^ 3460997981196 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (13 : ZMod 10382993943589) ^ 1483284849084 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (13 : ZMod 10382993943589) ^ 546473365452 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (13 : ZMod 10382993943589) ^ 14364 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_11091238618643 : Nat.Prime 11091238618643 := by
  apply lucas_primality 11091238618643 (5 : ZMod 11091238618643)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (12713, 1), (4793587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (12713, 1), (4793587, 1)] : List FactorBlock).map factorBlockValue).prod) = 11091238618643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_13
      · exact prime_oneHundredThirtyEightEF_12713
      · exact prime_oneHundredThirtyEightEF_4793587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 11091238618643) ^ 5545619309321 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 11091238618643) ^ 1584462659806 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 11091238618643) ^ 853172201434 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 11091238618643) ^ 872432834 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 11091238618643) ^ 2313766 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_11727020864261 : Nat.Prime 11727020864261 := by
  apply lucas_primality 11727020864261 (2 : ZMod 11727020864261)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (45103926401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (45103926401, 1)] : List FactorBlock).map factorBlockValue).prod) = 11727020864261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_13
      · exact prime_oneHundredThirtyEightEF_45103926401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11727020864261) ^ 5863510432130 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 11727020864261) ^ 2345404172852 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 11727020864261) ^ 902078528020 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 11727020864261) ^ 260 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_12185014335457 : Nat.Prime 12185014335457 := by
  apply lucas_primality 12185014335457 (7 : ZMod 12185014335457)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (83, 1), (673, 1), (863, 1), (2633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (83, 1), (673, 1), (863, 1), (2633, 1)] : List FactorBlock).map factorBlockValue).prod) = 12185014335457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_83
      · exact prime_oneHundredThirtyEightEF_673
      · exact prime_oneHundredThirtyEightEF_863
      · exact prime_oneHundredThirtyEightEF_2633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 12185014335457) ^ 6092507167728 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 12185014335457) ^ 4061671445152 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 12185014335457) ^ 146807401632 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 12185014335457) ^ 18105519072 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 12185014335457) ^ 14119367712 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 12185014335457) ^ 4627806432 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_13971226936099 : Nat.Prime 13971226936099 := by
  apply lucas_primality 13971226936099 (2 : ZMod 13971226936099)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (21617, 1), (6336347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (21617, 1), (6336347, 1)] : List FactorBlock).map factorBlockValue).prod) = 13971226936099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_17
      · exact prime_oneHundredThirtyEightEF_21617
      · exact prime_oneHundredThirtyEightEF_6336347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13971226936099) ^ 6985613468049 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 4657075645366 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 821836878594 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 646307394 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 2204934 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_16711559040419 : Nat.Prime 16711559040419 := by
  apply lucas_primality 16711559040419 (2 : ZMod 16711559040419)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (3943, 1), (192649333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (3943, 1), (192649333, 1)] : List FactorBlock).map factorBlockValue).prod) = 16711559040419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_11
      · exact prime_oneHundredThirtyEightEF_3943
      · exact prime_oneHundredThirtyEightEF_192649333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 16711559040419) ^ 8355779520209 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 16711559040419) ^ 1519232640038 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 16711559040419) ^ 4238285326 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 16711559040419) ^ 86746 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_19175562518401 : Nat.Prime 19175562518401 := by
  apply lucas_primality 19175562518401 (38 : ZMod 19175562518401)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 2), (479, 1), (463339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 2), (479, 1), (463339, 1)] : List FactorBlock).map factorBlockValue).prod) = 19175562518401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_479
      · exact prime_oneHundredThirtyEightEF_463339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (38 : ZMod 19175562518401) ^ 9587781259200 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (38 : ZMod 19175562518401) ^ 6391854172800 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (38 : ZMod 19175562518401) ^ 3835112503680 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (38 : ZMod 19175562518401) ^ 40032489600 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (38 : ZMod 19175562518401) ^ 41385600 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_20004379395641 : Nat.Prime 20004379395641 := by
  apply lucas_primality 20004379395641 (3 : ZMod 20004379395641)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (43, 1), (1933, 1), (6016789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (43, 1), (1933, 1), (6016789, 1)] : List FactorBlock).map factorBlockValue).prod) = 20004379395641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_43
      · exact prime_oneHundredThirtyEightEF_1933
      · exact prime_oneHundredThirtyEightEF_6016789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 20004379395641) ^ 10002189697820 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 20004379395641) ^ 4000875879128 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 20004379395641) ^ 465218125480 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 20004379395641) ^ 10348877080 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 20004379395641) ^ 3324760 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_25728013822523 : Nat.Prime 25728013822523 := by
  apply lucas_primality 25728013822523 (5 : ZMod 25728013822523)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (61, 1), (73, 1), (262621867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (61, 1), (73, 1), (262621867, 1)] : List FactorBlock).map factorBlockValue).prod) = 25728013822523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_11
      · exact prime_oneHundredThirtyEightEF_61
      · exact prime_oneHundredThirtyEightEF_73
      · exact prime_oneHundredThirtyEightEF_262621867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 25728013822523) ^ 12864006911261 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 25728013822523) ^ 2338910347502 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 25728013822523) ^ 421770718402 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 25728013822523) ^ 352438545514 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 25728013822523) ^ 97966 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_33763383185377 : Nat.Prime 33763383185377 := by
  apply lucas_primality 33763383185377 (11 : ZMod 33763383185377)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (13, 1), (47, 1), (137, 1), (4201583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (13, 1), (47, 1), (137, 1), (4201583, 1)] : List FactorBlock).map factorBlockValue).prod) = 33763383185377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_13
      · exact prime_oneHundredThirtyEightEF_47
      · exact prime_oneHundredThirtyEightEF_137
      · exact prime_oneHundredThirtyEightEF_4201583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 33763383185377) ^ 16881691592688 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 33763383185377) ^ 11254461061792 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 33763383185377) ^ 2597183321952 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 33763383185377) ^ 718369855008 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 33763383185377) ^ 246448052448 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 33763383185377) ^ 8035872 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_45752552594669 : Nat.Prime 45752552594669 := by
  apply lucas_primality 45752552594669 (2 : ZMod 45752552594669)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) = 45752552594669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_47
      · exact prime_oneHundredThirtyEightEF_243364641461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 45752552594669) ^ 22876276297334 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 973458565844 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 188 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_48692229193247 : Nat.Prime 48692229193247 := by
  apply lucas_primality 48692229193247 (5 : ZMod 48692229193247)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (839521192987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (839521192987, 1)] : List FactorBlock).map factorBlockValue).prod) = 48692229193247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_29
      · exact prime_oneHundredThirtyEightEF_839521192987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 48692229193247) ^ 24346114596623 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 48692229193247) ^ 1679042385974 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 48692229193247) ^ 58 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_68036703027947 : Nat.Prime 68036703027947 := by
  apply lucas_primality 68036703027947 (2 : ZMod 68036703027947)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (1790439553367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (1790439553367, 1)] : List FactorBlock).map factorBlockValue).prod) = 68036703027947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_19
      · exact prime_oneHundredThirtyEightEF_1790439553367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 68036703027947) ^ 34018351513973 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 68036703027947) ^ 3580879106734 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 68036703027947) ^ 38 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_87431913027871 : Nat.Prime 87431913027871 := by
  apply lucas_primality 87431913027871 (3 : ZMod 87431913027871)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (2914397100929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (2914397100929, 1)] : List FactorBlock).map factorBlockValue).prod) = 87431913027871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_2914397100929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 87431913027871) ^ 43715956513935 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 87431913027871) ^ 29143971009290 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 87431913027871) ^ 17486382605574 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 87431913027871) ^ 30 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_109924509718349 : Nat.Prime 109924509718349 := by
  apply lucas_primality 109924509718349 (2 : ZMod 109924509718349)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (19, 1), (111259625221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (19, 1), (111259625221, 1)] : List FactorBlock).map factorBlockValue).prod) = 109924509718349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_13
      · exact prime_oneHundredThirtyEightEF_19
      · exact prime_oneHundredThirtyEightEF_111259625221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 109924509718349) ^ 54962254859174 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 109924509718349) ^ 8455731516796 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 109924509718349) ^ 5785500511492 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 109924509718349) ^ 988 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_128299044275099 : Nat.Prime 128299044275099 := by
  apply lucas_primality 128299044275099 (2 : ZMod 128299044275099)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (113, 1), (2393, 1), (237231461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (113, 1), (2393, 1), (237231461, 1)] : List FactorBlock).map factorBlockValue).prod) = 128299044275099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_113
      · exact prime_oneHundredThirtyEightEF_2393
      · exact prime_oneHundredThirtyEightEF_237231461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 128299044275099) ^ 64149522137549 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 128299044275099) ^ 1135389772346 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 128299044275099) ^ 53614310186 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 128299044275099) ^ 540818 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_366020420757353 : Nat.Prime 366020420757353 := by
  apply lucas_primality 366020420757353 (3 : ZMod 366020420757353)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) = 366020420757353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_45752552594669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 366020420757353) ^ 183010210378676 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 366020420757353) ^ 8 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_430314183184889 : Nat.Prime 430314183184889 := by
  apply lucas_primality 430314183184889 (3 : ZMod 430314183184889)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1873, 1), (28718245007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1873, 1), (28718245007, 1)] : List FactorBlock).map factorBlockValue).prod) = 430314183184889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_1873
      · exact prime_oneHundredThirtyEightEF_28718245007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 430314183184889) ^ 215157091592444 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 430314183184889) ^ 229745960056 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 430314183184889) ^ 14984 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_509945605110661 : Nat.Prime 509945605110661 := by
  apply lucas_primality 509945605110661 (6 : ZMod 509945605110661)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (229, 1), (521, 1), (71235979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (229, 1), (521, 1), (71235979, 1)] : List FactorBlock).map factorBlockValue).prod) = 509945605110661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_229
      · exact prime_oneHundredThirtyEightEF_521
      · exact prime_oneHundredThirtyEightEF_71235979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 509945605110661) ^ 254972802555330 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 509945605110661) ^ 169981868370220 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 509945605110661) ^ 101989121022132 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 509945605110661) ^ 2226836703540 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 509945605110661) ^ 978782351460 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 509945605110661) ^ 7158540 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_717656839221107 : Nat.Prime 717656839221107 := by
  apply lucas_primality 717656839221107 (2 : ZMod 717656839221107)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (42929, 1), (47947, 1), (174331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (42929, 1), (47947, 1), (174331, 1)] : List FactorBlock).map factorBlockValue).prod) = 717656839221107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_42929
      · exact prime_oneHundredThirtyEightEF_47947
      · exact prime_oneHundredThirtyEightEF_174331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 717656839221107) ^ 358828419610553 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 717656839221107) ^ 16717296914 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 717656839221107) ^ 14967710998 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 717656839221107) ^ 4116633526 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_740293615282103 : Nat.Prime 740293615282103 := by
  apply lucas_primality 740293615282103 (5 : ZMod 740293615282103)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2609, 1), (20267579677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2609, 1), (20267579677, 1)] : List FactorBlock).map factorBlockValue).prod) = 740293615282103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_2609
      · exact prime_oneHundredThirtyEightEF_20267579677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 740293615282103) ^ 370146807641051 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 740293615282103) ^ 105756230754586 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 740293615282103) ^ 283746115478 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 740293615282103) ^ 36526 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_784410342216857 : Nat.Prime 784410342216857 := by
  apply lucas_primality 784410342216857 (3 : ZMod 784410342216857)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (347, 1), (6563, 1), (43054787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (347, 1), (6563, 1), (43054787, 1)] : List FactorBlock).map factorBlockValue).prod) = 784410342216857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_347
      · exact prime_oneHundredThirtyEightEF_6563
      · exact prime_oneHundredThirtyEightEF_43054787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 784410342216857) ^ 392205171108428 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 784410342216857) ^ 2260548536648 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 784410342216857) ^ 119520088712 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 784410342216857) ^ 18218888 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_805373625772843 : Nat.Prime 805373625772843 := by
  apply lucas_primality 805373625772843 (2 : ZMod 805373625772843)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (19175562518401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (19175562518401, 1)] : List FactorBlock).map factorBlockValue).prod) = 805373625772843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_19175562518401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 805373625772843) ^ 402686812886421 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 805373625772843) ^ 268457875257614 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 805373625772843) ^ 115053375110406 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 805373625772843) ^ 42 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_1035497806932613 : Nat.Prime 1035497806932613 := by
  apply lucas_primality 1035497806932613 (2 : ZMod 1035497806932613)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1759, 1), (8429, 1), (5820041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1759, 1), (8429, 1), (5820041, 1)] : List FactorBlock).map factorBlockValue).prod) = 1035497806932613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_1759
      · exact prime_oneHundredThirtyEightEF_8429
      · exact prime_oneHundredThirtyEightEF_5820041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1035497806932613) ^ 517748903466306 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1035497806932613) ^ 345165935644204 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1035497806932613) ^ 588685507068 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1035497806932613) ^ 122849425428 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1035497806932613) ^ 177919332 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_1285039985930447 : Nat.Prime 1285039985930447 := by
  apply lucas_primality 1285039985930447 (5 : ZMod 1285039985930447)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (257, 1), (160967, 1), (535573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (257, 1), (160967, 1), (535573, 1)] : List FactorBlock).map factorBlockValue).prod) = 1285039985930447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_29
      · exact prime_oneHundredThirtyEightEF_257
      · exact prime_oneHundredThirtyEightEF_160967
      · exact prime_oneHundredThirtyEightEF_535573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1285039985930447) ^ 642519992965223 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1285039985930447) ^ 44311723652774 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1285039985930447) ^ 5000155587278 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1285039985930447) ^ 7983251138 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1285039985930447) ^ 2399374102 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_1752920250956893 : Nat.Prime 1752920250956893 := by
  apply lucas_primality 1752920250956893 (2 : ZMod 1752920250956893)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (48692229193247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (48692229193247, 1)] : List FactorBlock).map factorBlockValue).prod) = 1752920250956893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_48692229193247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1752920250956893) ^ 876460125478446 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1752920250956893) ^ 584306750318964 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1752920250956893) ^ 36 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_1976670307595807 : Nat.Prime 1976670307595807 := by
  apply lucas_primality 1976670307595807 (5 : ZMod 1976670307595807)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7867, 1), (41513, 1), (3026293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7867, 1), (41513, 1), (3026293, 1)] : List FactorBlock).map factorBlockValue).prod) = 1976670307595807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_7867
      · exact prime_oneHundredThirtyEightEF_41513
      · exact prime_oneHundredThirtyEightEF_3026293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1976670307595807) ^ 988335153797903 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1976670307595807) ^ 251261002618 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1976670307595807) ^ 47615694062 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1976670307595807) ^ 653165542 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_4667591109479797 : Nat.Prime 4667591109479797 := by
  apply lucas_primality 4667591109479797 (6 : ZMod 4667591109479797)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 8), (47, 1), (83, 1), (233, 1), (419, 1), (467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 8), (47, 1), (83, 1), (233, 1), (419, 1), (467, 1)] : List FactorBlock).map factorBlockValue).prod) = 4667591109479797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_47
      · exact prime_oneHundredThirtyEightEF_83
      · exact prime_oneHundredThirtyEightEF_233
      · exact prime_oneHundredThirtyEightEF_419
      · exact prime_oneHundredThirtyEightEF_467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 4667591109479797) ^ 2333795554739898 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 4667591109479797) ^ 1555863703159932 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 4667591109479797) ^ 99310449137868 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 4667591109479797) ^ 56236037463612 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 4667591109479797) ^ 20032579869012 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 4667591109479797) ^ 11139835583484 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 4667591109479797) ^ 9994841776188 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_5034716024068079 : Nat.Prime 5034716024068079 := by
  apply lucas_primality 5034716024068079 (13 : ZMod 5034716024068079)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (68036703027947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (68036703027947, 1)] : List FactorBlock).map factorBlockValue).prod) = 5034716024068079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_37
      · exact prime_oneHundredThirtyEightEF_68036703027947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 5034716024068079) ^ 2517358012034039 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (13 : ZMod 5034716024068079) ^ 136073406055894 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (13 : ZMod 5034716024068079) ^ 74 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_12594975251394721 : Nat.Prime 12594975251394721 := by
  apply lucas_primality 12594975251394721 (7 : ZMod 12594975251394721)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (83, 1), (316138937033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (83, 1), (316138937033, 1)] : List FactorBlock).map factorBlockValue).prod) = 12594975251394721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_83
      · exact prime_oneHundredThirtyEightEF_316138937033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 12594975251394721) ^ 6297487625697360 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 12594975251394721) ^ 4198325083798240 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 12594975251394721) ^ 2518995050278944 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 12594975251394721) ^ 151746689775840 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 12594975251394721) ^ 39840 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_15389431360568861 : Nat.Prime 15389431360568861 := by
  apply lucas_primality 15389431360568861 (11 : ZMod 15389431360568861)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (109924509718349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (109924509718349, 1)] : List FactorBlock).map factorBlockValue).prod) = 15389431360568861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_109924509718349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 15389431360568861) ^ 7694715680284430 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 15389431360568861) ^ 3077886272113772 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 15389431360568861) ^ 2198490194366980 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 15389431360568861) ^ 140 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_15965845164193937 : Nat.Prime 15965845164193937 := by
  apply lucas_primality 15965845164193937 (3 : ZMod 15965845164193937)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (2251, 1), (40299879761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (2251, 1), (40299879761, 1)] : List FactorBlock).map factorBlockValue).prod) = 15965845164193937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_11
      · exact prime_oneHundredThirtyEightEF_2251
      · exact prime_oneHundredThirtyEightEF_40299879761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 15965845164193937) ^ 7982922582096968 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 15965845164193937) ^ 1451440469472176 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 15965845164193937) ^ 7092778837936 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 15965845164193937) ^ 396176 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_16643128656708293 : Nat.Prime 16643128656708293 := by
  apply lucas_primality 16643128656708293 (2 : ZMod 16643128656708293)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (263489, 1), (509390447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (263489, 1), (509390447, 1)] : List FactorBlock).map factorBlockValue).prod) = 16643128656708293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_31
      · exact prime_oneHundredThirtyEightEF_263489
      · exact prime_oneHundredThirtyEightEF_509390447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 16643128656708293) ^ 8321564328354146 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 16643128656708293) ^ 536875117958332 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 16643128656708293) ^ 63164415428 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 16643128656708293) ^ 32672636 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_17437701477413197 : Nat.Prime 17437701477413197 := by
  apply lucas_primality 17437701477413197 (2 : ZMod 17437701477413197)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (17, 1), (1787, 1), (759266029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (17, 1), (1787, 1), (759266029, 1)] : List FactorBlock).map factorBlockValue).prod) = 17437701477413197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_17
      · exact prime_oneHundredThirtyEightEF_1787
      · exact prime_oneHundredThirtyEightEF_759266029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17437701477413197) ^ 8718850738706598 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 17437701477413197) ^ 5812567159137732 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 17437701477413197) ^ 2491100211059028 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 17437701477413197) ^ 1025747145730188 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 17437701477413197) ^ 9758087004708 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 17437701477413197) ^ 22966524 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_30410512338222187 : Nat.Prime 30410512338222187 := by
  apply lucas_primality 30410512338222187 (3 : ZMod 30410512338222187)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (197, 1), (25728013822523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (197, 1), (25728013822523, 1)] : List FactorBlock).map factorBlockValue).prod) = 30410512338222187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_197
      · exact prime_oneHundredThirtyEightEF_25728013822523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 30410512338222187) ^ 15205256169111093 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 30410512338222187) ^ 10136837446074062 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 30410512338222187) ^ 154368082935138 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 30410512338222187) ^ 1182 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_57903523208519959 : Nat.Prime 57903523208519959 := by
  apply lucas_primality 57903523208519959 (6 : ZMod 57903523208519959)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (433, 1), (1301, 1), (1543, 1), (217697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (433, 1), (1301, 1), (1543, 1), (217697, 1)] : List FactorBlock).map factorBlockValue).prod) = 57903523208519959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_17
      · exact prime_oneHundredThirtyEightEF_433
      · exact prime_oneHundredThirtyEightEF_1301
      · exact prime_oneHundredThirtyEightEF_1543
      · exact prime_oneHundredThirtyEightEF_217697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 57903523208519959) ^ 28951761604259979 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 57903523208519959) ^ 19301174402839986 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 57903523208519959) ^ 3406089600501174 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 57903523208519959) ^ 133726381543926 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 57903523208519959) ^ 44506935594558 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 57903523208519959) ^ 37526586654906 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 57903523208519959) ^ 265982182614 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_103881444870472429 : Nat.Prime 103881444870472429 := by
  apply lucas_primality 103881444870472429 (2 : ZMod 103881444870472429)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7793, 1), (1110841405433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7793, 1), (1110841405433, 1)] : List FactorBlock).map factorBlockValue).prod) = 103881444870472429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_7793
      · exact prime_oneHundredThirtyEightEF_1110841405433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 103881444870472429) ^ 51940722435236214 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 103881444870472429) ^ 34627148290157476 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 103881444870472429) ^ 13330096865196 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 103881444870472429) ^ 93516 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_114969019264351177 : Nat.Prime 114969019264351177 := by
  apply lucas_primality 114969019264351177 (10 : ZMod 114969019264351177)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (41, 1), (195469, 1), (597733831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (41, 1), (195469, 1), (597733831, 1)] : List FactorBlock).map factorBlockValue).prod) = 114969019264351177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_41
      · exact prime_oneHundredThirtyEightEF_195469
      · exact prime_oneHundredThirtyEightEF_597733831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 114969019264351177) ^ 57484509632175588 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (10 : ZMod 114969019264351177) ^ 38323006421450392 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (10 : ZMod 114969019264351177) ^ 2804122421081736 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (10 : ZMod 114969019264351177) ^ 588170089704 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (10 : ZMod 114969019264351177) ^ 192341496 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_124788216886380263 : Nat.Prime 124788216886380263 := by
  apply lucas_primality 124788216886380263 (5 : ZMod 124788216886380263)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (367, 1), (1348331, 1), (126090103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (367, 1), (1348331, 1), (126090103, 1)] : List FactorBlock).map factorBlockValue).prod) = 124788216886380263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_367
      · exact prime_oneHundredThirtyEightEF_1348331
      · exact prime_oneHundredThirtyEightEF_126090103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 124788216886380263) ^ 62394108443190131 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 124788216886380263) ^ 340022389336186 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 124788216886380263) ^ 92550135602 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 124788216886380263) ^ 989674954 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_135985957393556749 : Nat.Prime 135985957393556749 := by
  apply lucas_primality 135985957393556749 (2 : ZMod 135985957393556749)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (37, 1), (223, 1), (2447, 1), (561270557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (37, 1), (223, 1), (2447, 1), (561270557, 1)] : List FactorBlock).map factorBlockValue).prod) = 135985957393556749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_37
      · exact prime_oneHundredThirtyEightEF_223
      · exact prime_oneHundredThirtyEightEF_2447
      · exact prime_oneHundredThirtyEightEF_561270557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 135985957393556749) ^ 67992978696778374 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 135985957393556749) ^ 45328652464518916 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 135985957393556749) ^ 3675296145771804 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 135985957393556749) ^ 609802499522676 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 135985957393556749) ^ 55572520389684 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 135985957393556749) ^ 242282364 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_202878326750686661 : Nat.Prime 202878326750686661 := by
  apply lucas_primality 202878326750686661 (2 : ZMod 202878326750686661)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (607, 1), (16711559040419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (607, 1), (16711559040419, 1)] : List FactorBlock).map factorBlockValue).prod) = 202878326750686661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_607
      · exact prime_oneHundredThirtyEightEF_16711559040419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 202878326750686661) ^ 101439163375343330 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 202878326750686661) ^ 40575665350137332 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 202878326750686661) ^ 334231180808380 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 202878326750686661) ^ 12140 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_261318517715367989 : Nat.Prime 261318517715367989 := by
  apply lucas_primality 261318517715367989 (2 : ZMod 261318517715367989)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (997, 1), (1481, 1), (1427244191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (997, 1), (1481, 1), (1427244191, 1)] : List FactorBlock).map factorBlockValue).prod) = 261318517715367989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_31
      · exact prime_oneHundredThirtyEightEF_997
      · exact prime_oneHundredThirtyEightEF_1481
      · exact prime_oneHundredThirtyEightEF_1427244191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 261318517715367989) ^ 130659258857683994 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 261318517715367989) ^ 8429629603721548 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 261318517715367989) ^ 262104832212004 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 261318517715367989) ^ 176447344844948 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 261318517715367989) ^ 183093068 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_290922148546281647 : Nat.Prime 290922148546281647 := by
  apply lucas_primality 290922148546281647 (5 : ZMod 290922148546281647)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (419, 1), (8467377278837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (419, 1), (8467377278837, 1)] : List FactorBlock).map factorBlockValue).prod) = 290922148546281647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_41
      · exact prime_oneHundredThirtyEightEF_419
      · exact prime_oneHundredThirtyEightEF_8467377278837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 290922148546281647) ^ 145461074273140823 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 290922148546281647) ^ 7095662159665406 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 290922148546281647) ^ 694324936864634 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 290922148546281647) ^ 34358 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_305185311208195361 : Nat.Prime 305185311208195361 := by
  apply lucas_primality 305185311208195361 (3 : ZMod 305185311208195361)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (71, 1), (141277, 1), (190157663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (71, 1), (141277, 1), (190157663, 1)] : List FactorBlock).map factorBlockValue).prod) = 305185311208195361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_71
      · exact prime_oneHundredThirtyEightEF_141277
      · exact prime_oneHundredThirtyEightEF_190157663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 305185311208195361) ^ 152592655604097680 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 305185311208195361) ^ 61037062241639072 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 305185311208195361) ^ 4298384664904160 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 305185311208195361) ^ 2160191051680 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 305185311208195361) ^ 1604906720 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_357415490990239999 : Nat.Prime 357415490990239999 := by
  apply lucas_primality 357415490990239999 (3 : ZMod 357415490990239999)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1574129, 1), (37842672677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1574129, 1), (37842672677, 1)] : List FactorBlock).map factorBlockValue).prod) = 357415490990239999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_1574129
      · exact prime_oneHundredThirtyEightEF_37842672677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 357415490990239999) ^ 178707745495119999 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 357415490990239999) ^ 119138496996746666 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 357415490990239999) ^ 227056036062 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 357415490990239999) ^ 9444774 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_436456482815239553 : Nat.Prime 436456482815239553 := by
  apply lucas_primality 436456482815239553 (3 : ZMod 436456482815239553)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (29, 1), (107, 1), (269, 1), (6779, 1), (602603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (29, 1), (107, 1), (269, 1), (6779, 1), (602603, 1)] : List FactorBlock).map factorBlockValue).prod) = 436456482815239553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_29
      · exact prime_oneHundredThirtyEightEF_107
      · exact prime_oneHundredThirtyEightEF_269
      · exact prime_oneHundredThirtyEightEF_6779
      · exact prime_oneHundredThirtyEightEF_602603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 436456482815239553) ^ 218228241407619776 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 436456482815239553) ^ 15050223545353088 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 436456482815239553) ^ 4079032549675136 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 436456482815239553) ^ 1622514806004608 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 436456482815239553) ^ 64383608617088 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 436456482815239553) ^ 724285280384 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_489073724074015939 : Nat.Prime 489073724074015939 := by
  apply lucas_primality 489073724074015939 (2 : ZMod 489073724074015939)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (13, 1), (557, 1), (73939, 1), (4613569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (13, 1), (557, 1), (73939, 1), (4613569, 1)] : List FactorBlock).map factorBlockValue).prod) = 489073724074015939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_11
      · exact prime_oneHundredThirtyEightEF_13
      · exact prime_oneHundredThirtyEightEF_557
      · exact prime_oneHundredThirtyEightEF_73939
      · exact prime_oneHundredThirtyEightEF_4613569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 489073724074015939) ^ 244536862037007969 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 489073724074015939) ^ 163024574691338646 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 489073724074015939) ^ 44461247643092358 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 489073724074015939) ^ 37621055698001226 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 489073724074015939) ^ 878049773921034 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 489073724074015939) ^ 6614556919542 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 489073724074015939) ^ 106007675202 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_574186982349158909 : Nat.Prime 574186982349158909 := by
  apply lucas_primality 574186982349158909 (2 : ZMod 574186982349158909)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (419, 1), (12037637, 1), (28460209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (419, 1), (12037637, 1), (28460209, 1)] : List FactorBlock).map factorBlockValue).prod) = 574186982349158909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_419
      · exact prime_oneHundredThirtyEightEF_12037637
      · exact prime_oneHundredThirtyEightEF_28460209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 574186982349158909) ^ 287093491174579454 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 574186982349158909) ^ 1370374659544532 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 574186982349158909) ^ 47699310284 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 574186982349158909) ^ 20175079612 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_991985446212325951 : Nat.Prime 991985446212325951 := by
  apply lucas_primality 991985446212325951 (6 : ZMod 991985446212325951)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (7, 1), (11, 1), (661, 1), (4481, 1), (28996589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (7, 1), (11, 1), (661, 1), (4481, 1), (28996589, 1)] : List FactorBlock).map factorBlockValue).prod) = 991985446212325951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_11
      · exact prime_oneHundredThirtyEightEF_661
      · exact prime_oneHundredThirtyEightEF_4481
      · exact prime_oneHundredThirtyEightEF_28996589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 991985446212325951) ^ 495992723106162975 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 991985446212325951) ^ 330661815404108650 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 991985446212325951) ^ 198397089242465190 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 991985446212325951) ^ 141712206601760850 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 991985446212325951) ^ 90180495110211450 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 991985446212325951) ^ 1500734411818950 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 991985446212325951) ^ 221375908549950 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 991985446212325951) ^ 34210418550 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_1217269960504119967 : Nat.Prime 1217269960504119967 := by
  apply lucas_primality 1217269960504119967 (5 : ZMod 1217269960504119967)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (202878326750686661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (202878326750686661, 1)] : List FactorBlock).map factorBlockValue).prod) = 1217269960504119967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_202878326750686661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1217269960504119967) ^ 608634980252059983 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1217269960504119967) ^ 405756653501373322 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1217269960504119967) ^ 6 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_1371465244669327121 : Nat.Prime 1371465244669327121 := by
  apply lucas_primality 1371465244669327121 (6 : ZMod 1371465244669327121)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (8521, 1), (2011890101909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (8521, 1), (2011890101909, 1)] : List FactorBlock).map factorBlockValue).prod) = 1371465244669327121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_8521
      · exact prime_oneHundredThirtyEightEF_2011890101909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1371465244669327121) ^ 685732622334663560 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1371465244669327121) ^ 274293048933865424 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1371465244669327121) ^ 160951208152720 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1371465244669327121) ^ 681680 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_1409118863239069111 : Nat.Prime 1409118863239069111 := by
  apply lucas_primality 1409118863239069111 (6 : ZMod 1409118863239069111)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (17, 1), (101, 1), (661, 1), (2039, 1), (2255251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (17, 1), (101, 1), (661, 1), (2039, 1), (2255251, 1)] : List FactorBlock).map factorBlockValue).prod) = 1409118863239069111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_17
      · exact prime_oneHundredThirtyEightEF_101
      · exact prime_oneHundredThirtyEightEF_661
      · exact prime_oneHundredThirtyEightEF_2039
      · exact prime_oneHundredThirtyEightEF_2255251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1409118863239069111) ^ 704559431619534555 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1409118863239069111) ^ 469706287746356370 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1409118863239069111) ^ 281823772647813822 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1409118863239069111) ^ 82889344896415830 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1409118863239069111) ^ 13951671913258110 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1409118863239069111) ^ 2131798582812510 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1409118863239069111) ^ 691083307130490 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1409118863239069111) ^ 624816866610 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_1708338346069605703 : Nat.Prime 1708338346069605703 := by
  apply lucas_primality 1708338346069605703 (3 : ZMod 1708338346069605703)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61, 1), (4667591109479797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61, 1), (4667591109479797, 1)] : List FactorBlock).map factorBlockValue).prod) = 1708338346069605703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_61
      · exact prime_oneHundredThirtyEightEF_4667591109479797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1708338346069605703) ^ 854169173034802851 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1708338346069605703) ^ 569446115356535234 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1708338346069605703) ^ 28005546656878782 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1708338346069605703) ^ 366 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_2220502305087140441 : Nat.Prime 2220502305087140441 := by
  apply lucas_primality 2220502305087140441 (3 : ZMod 2220502305087140441)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2220502305087140441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_101
      · exact prime_oneHundredThirtyEightEF_191
      · exact prime_oneHundredThirtyEightEF_48017
      · exact prime_oneHundredThirtyEightEF_59929613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2220502305087140441) ^ 1110251152543570220 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 444100461017428088 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 21985171337496440 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 11625666518780840 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 46244086575320 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 37051837880 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_3027868235407889213 : Nat.Prime 3027868235407889213 := by
  apply lucas_primality 3027868235407889213 (2 : ZMod 3027868235407889213)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (73, 1), (1188413, 1), (8725427747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (73, 1), (1188413, 1), (8725427747, 1)] : List FactorBlock).map factorBlockValue).prod) = 3027868235407889213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_73
      · exact prime_oneHundredThirtyEightEF_1188413
      · exact prime_oneHundredThirtyEightEF_8725427747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3027868235407889213) ^ 1513934117703944606 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3027868235407889213) ^ 41477647060382044 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3027868235407889213) ^ 2547824902124 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3027868235407889213) ^ 347016596 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_3367844712889765153 : Nat.Prime 3367844712889765153 := by
  apply lucas_primality 3367844712889765153 (7 : ZMod 3367844712889765153)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (11, 1), (19, 1), (967567, 1), (173481629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (11, 1), (19, 1), (967567, 1), (173481629, 1)] : List FactorBlock).map factorBlockValue).prod) = 3367844712889765153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_11
      · exact prime_oneHundredThirtyEightEF_19
      · exact prime_oneHundredThirtyEightEF_967567
      · exact prime_oneHundredThirtyEightEF_173481629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3367844712889765153) ^ 1683922356444882576 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 3367844712889765153) ^ 1122614904296588384 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 3367844712889765153) ^ 306167701171796832 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 3367844712889765153) ^ 177254984888935008 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 3367844712889765153) ^ 3480735404256 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 3367844712889765153) ^ 19413264288 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_3525236034297377371 : Nat.Prime 3525236034297377371 := by
  apply lucas_primality 3525236034297377371 (2 : ZMod 3525236034297377371)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (68947763, 1), (1704302833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (68947763, 1), (1704302833, 1)] : List FactorBlock).map factorBlockValue).prod) = 3525236034297377371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_68947763
      · exact prime_oneHundredThirtyEightEF_1704302833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3525236034297377371) ^ 1762618017148688685 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3525236034297377371) ^ 1175078678099125790 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3525236034297377371) ^ 705047206859475474 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3525236034297377371) ^ 51129084990 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3525236034297377371) ^ 2068432890 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_15602017149911940271 : Nat.Prime 15602017149911940271 := by
  apply lucas_primality 15602017149911940271 (3 : ZMod 15602017149911940271)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (61, 1), (13416959, 1), (33444289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (61, 1), (13416959, 1), (33444289, 1)] : List FactorBlock).map factorBlockValue).prod) = 15602017149911940271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_19
      · exact prime_oneHundredThirtyEightEF_61
      · exact prime_oneHundredThirtyEightEF_13416959
      · exact prime_oneHundredThirtyEightEF_33444289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 15602017149911940271) ^ 7801008574955970135 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 15602017149911940271) ^ 5200672383303980090 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 15602017149911940271) ^ 3120403429982388054 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 15602017149911940271) ^ 821158797363786330 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 15602017149911940271) ^ 255770772949376070 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 15602017149911940271) ^ 1162857928530 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 15602017149911940271) ^ 466507664430 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_17660765089967180327 : Nat.Prime 17660765089967180327 := by
  apply lucas_primality 17660765089967180327 (5 : ZMod 17660765089967180327)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2797, 1), (10211, 1), (309185255989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2797, 1), (10211, 1), (309185255989, 1)] : List FactorBlock).map factorBlockValue).prod) = 17660765089967180327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_2797
      · exact prime_oneHundredThirtyEightEF_10211
      · exact prime_oneHundredThirtyEightEF_309185255989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 17660765089967180327) ^ 8830382544983590163 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 17660765089967180327) ^ 6314181297807358 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 17660765089967180327) ^ 1729582322002466 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 17660765089967180327) ^ 57120334 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_21104895562726197779 : Nat.Prime 21104895562726197779 := by
  apply lucas_primality 21104895562726197779 (2 : ZMod 21104895562726197779)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (347, 1), (30410512338222187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (347, 1), (30410512338222187, 1)] : List FactorBlock).map factorBlockValue).prod) = 21104895562726197779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_347
      · exact prime_oneHundredThirtyEightEF_30410512338222187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 21104895562726197779) ^ 10552447781363098889 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 21104895562726197779) ^ 60821024676444374 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 21104895562726197779) ^ 694 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_22930626232945946497 : Nat.Prime 22930626232945946497 := by
  apply lucas_primality 22930626232945946497 (5 : ZMod 22930626232945946497)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (31333, 1), (1905823651793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (31333, 1), (1905823651793, 1)] : List FactorBlock).map factorBlockValue).prod) = 22930626232945946497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_31333
      · exact prime_oneHundredThirtyEightEF_1905823651793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 22930626232945946497) ^ 11465313116472973248 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 22930626232945946497) ^ 7643542077648648832 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 22930626232945946497) ^ 731836282288512 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 22930626232945946497) ^ 12031872 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_69479961311992616051 : Nat.Prime 69479961311992616051 := by
  apply lucas_primality 69479961311992616051 (7 : ZMod 69479961311992616051)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (19, 1), (37, 1), (1976670307595807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (19, 1), (37, 1), (1976670307595807, 1)] : List FactorBlock).map factorBlockValue).prod) = 69479961311992616051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_19
      · exact prime_oneHundredThirtyEightEF_37
      · exact prime_oneHundredThirtyEightEF_1976670307595807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 69479961311992616051) ^ 34739980655996308025 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 69479961311992616051) ^ 13895992262398523210 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 69479961311992616051) ^ 3656840069052242950 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 69479961311992616051) ^ 1877836792216016650 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 69479961311992616051) ^ 35150 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_73779945007300088027 : Nat.Prime 73779945007300088027 := by
  apply lucas_primality 73779945007300088027 (2 : ZMod 73779945007300088027)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 2), (71, 1), (697703, 1), (885489461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 2), (71, 1), (697703, 1), (885489461, 1)] : List FactorBlock).map factorBlockValue).prod) = 73779945007300088027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_29
      · exact prime_oneHundredThirtyEightEF_71
      · exact prime_oneHundredThirtyEightEF_697703
      · exact prime_oneHundredThirtyEightEF_885489461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 73779945007300088027) ^ 36889972503650044013 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 73779945007300088027) ^ 2544136034734485794 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 73779945007300088027) ^ 1039154155032395606 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 73779945007300088027) ^ 105746922411542 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 73779945007300088027) ^ 83321087666 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_256223811061086791179 : Nat.Prime 256223811061086791179 := by
  apply lucas_primality 256223811061086791179 (2 : ZMod 256223811061086791179)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) = 256223811061086791179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_17
      · exact prime_oneHundredThirtyEightEF_6863
      · exact prime_oneHundredThirtyEightEF_366020420757353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 256223811061086791179) ^ 128111905530543395589 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 85407937020362263726 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 15071988885946281834 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 37334082917250006 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 700026 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_1205269042013298899237 : Nat.Prime 1205269042013298899237 := by
  apply lucas_primality 1205269042013298899237 (2 : ZMod 1205269042013298899237)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (1549, 1), (47713, 1), (341461, 1), (519119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (1549, 1), (47713, 1), (341461, 1), (519119, 1)] : List FactorBlock).map factorBlockValue).prod) = 1205269042013298899237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_23
      · exact prime_oneHundredThirtyEightEF_1549
      · exact prime_oneHundredThirtyEightEF_47713
      · exact prime_oneHundredThirtyEightEF_341461
      · exact prime_oneHundredThirtyEightEF_519119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1205269042013298899237) ^ 602634521006649449618 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 52403001826665169532 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 778094927058294964 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 25260810303550372 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 3529741440496276 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 2321758675782044 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_1222241588345846515283 : Nat.Prime 1222241588345846515283 := by
  apply lucas_primality 1222241588345846515283 (5 : ZMod 1222241588345846515283)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 2), (401, 1), (12594975251394721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 2), (401, 1), (12594975251394721, 1)] : List FactorBlock).map factorBlockValue).prod) = 1222241588345846515283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_11
      · exact prime_oneHundredThirtyEightEF_401
      · exact prime_oneHundredThirtyEightEF_12594975251394721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1222241588345846515283) ^ 611120794172923257641 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1222241588345846515283) ^ 111112871667804228662 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1222241588345846515283) ^ 3047984010837522482 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1222241588345846515283) ^ 97042 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_2444483176691693030567 : Nat.Prime 2444483176691693030567 := by
  apply lucas_primality 2444483176691693030567 (5 : ZMod 2444483176691693030567)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1222241588345846515283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1222241588345846515283, 1)] : List FactorBlock).map factorBlockValue).prod) = 2444483176691693030567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_1222241588345846515283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 2444483176691693030567) ^ 1222241588345846515283 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 2444483176691693030567) ^ 2 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_3074685732733041494149 : Nat.Prime 3074685732733041494149 := by
  apply lucas_primality 3074685732733041494149 (2 : ZMod 3074685732733041494149)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) = 3074685732733041494149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_256223811061086791179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3074685732733041494149) ^ 1537342866366520747074 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 1024895244244347164716 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 12 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_3887587502410238495879 : Nat.Prime 3887587502410238495879 := by
  apply lucas_primality 3887587502410238495879 (29 : ZMod 3887587502410238495879)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (211, 1), (577, 1), (15965845164193937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (211, 1), (577, 1), (15965845164193937, 1)] : List FactorBlock).map factorBlockValue).prod) = 3887587502410238495879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_211
      · exact prime_oneHundredThirtyEightEF_577
      · exact prime_oneHundredThirtyEightEF_15965845164193937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (29 : ZMod 3887587502410238495879) ^ 1943793751205119247939 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (29 : ZMod 3887587502410238495879) ^ 18424585319479803298 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (29 : ZMod 3887587502410238495879) ^ 6737586659289841414 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (29 : ZMod 3887587502410238495879) ^ 243494 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_5221502938062639826289 : Nat.Prime 5221502938062639826289 := by
  apply lucas_primality 5221502938062639826289 (6 : ZMod 5221502938062639826289)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (883, 1), (2796587, 1), (132155884583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (883, 1), (2796587, 1), (132155884583, 1)] : List FactorBlock).map factorBlockValue).prod) = 5221502938062639826289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_883
      · exact prime_oneHundredThirtyEightEF_2796587
      · exact prime_oneHundredThirtyEightEF_132155884583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 5221502938062639826289) ^ 2610751469031319913144 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 5221502938062639826289) ^ 5913366860773091536 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 5221502938062639826289) ^ 1867098337388624 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 5221502938062639826289) ^ 39510181136 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_5851523790925058935517 : Nat.Prime 5851523790925058935517 := by
  apply lucas_primality 5851523790925058935517 (2 : ZMod 5851523790925058935517)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (127, 1), (347, 1), (373, 1), (821, 1), (17977, 1), (6029851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (127, 1), (347, 1), (373, 1), (821, 1), (17977, 1), (6029851, 1)] : List FactorBlock).map factorBlockValue).prod) = 5851523790925058935517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_127
      · exact prime_oneHundredThirtyEightEF_347
      · exact prime_oneHundredThirtyEightEF_373
      · exact prime_oneHundredThirtyEightEF_821
      · exact prime_oneHundredThirtyEightEF_17977
      · exact prime_oneHundredThirtyEightEF_6029851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5851523790925058935517) ^ 2925761895462529467758 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5851523790925058935517) ^ 46074990479724873508 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5851523790925058935517) ^ 16863180953674521428 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5851523790925058935517) ^ 15687731342962624492 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5851523790925058935517) ^ 7127312778227842796 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5851523790925058935517) ^ 325500572449522108 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5851523790925058935517) ^ 970425934392916 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_12087652072375107603173 : Nat.Prime 12087652072375107603173 := by
  apply lucas_primality 12087652072375107603173 (2 : ZMod 12087652072375107603173)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (23, 1), (80662823, 1), (232692650431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (23, 1), (80662823, 1), (232692650431, 1)] : List FactorBlock).map factorBlockValue).prod) = 12087652072375107603173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_23
      · exact prime_oneHundredThirtyEightEF_80662823
      · exact prime_oneHundredThirtyEightEF_232692650431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12087652072375107603173) ^ 6043826036187553801586 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 12087652072375107603173) ^ 1726807438910729657596 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 12087652072375107603173) ^ 525550090103265547964 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 12087652072375107603173) ^ 149854066877564 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 12087652072375107603173) ^ 51946858012 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_13652437807483255029187 : Nat.Prime 13652437807483255029187 := by
  apply lucas_primality 13652437807483255029187 (7 : ZMod 13652437807483255029187)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (83933, 1), (430314183184889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (83933, 1), (430314183184889, 1)] : List FactorBlock).map factorBlockValue).prod) = 13652437807483255029187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_83933
      · exact prime_oneHundredThirtyEightEF_430314183184889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 13652437807483255029187) ^ 6826218903741627514593 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 13652437807483255029187) ^ 4550812602494418343062 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 13652437807483255029187) ^ 1950348258211893575598 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 13652437807483255029187) ^ 162658761243888042 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 13652437807483255029187) ^ 31726674 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_19686195541427289576629 : Nat.Prime 19686195541427289576629 := by
  apply lucas_primality 19686195541427289576629 (2 : ZMod 19686195541427289576629)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (347, 1), (489073724074015939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (347, 1), (489073724074015939, 1)] : List FactorBlock).map factorBlockValue).prod) = 19686195541427289576629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_29
      · exact prime_oneHundredThirtyEightEF_347
      · exact prime_oneHundredThirtyEightEF_489073724074015939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 19686195541427289576629) ^ 9843097770713644788314 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 19686195541427289576629) ^ 678834329014734123332 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 19686195541427289576629) ^ 56732551992585848924 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 19686195541427289576629) ^ 40252 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_21500316536914473447941 : Nat.Prime 21500316536914473447941 := by
  apply lucas_primality 21500316536914473447941 (2 : ZMod 21500316536914473447941)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (59, 1), (281, 1), (707827, 1), (91607156309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (59, 1), (281, 1), (707827, 1), (91607156309, 1)] : List FactorBlock).map factorBlockValue).prod) = 21500316536914473447941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_59
      · exact prime_oneHundredThirtyEightEF_281
      · exact prime_oneHundredThirtyEightEF_707827
      · exact prime_oneHundredThirtyEightEF_91607156309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 21500316536914473447941) ^ 10750158268457236723970 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 21500316536914473447941) ^ 4300063307382894689588 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 21500316536914473447941) ^ 364412144693465651660 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 21500316536914473447941) ^ 76513581981902040740 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 21500316536914473447941) ^ 30375100888938220 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 21500316536914473447941) ^ 234701276660 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_29594351287506900995791 : Nat.Prime 29594351287506900995791 := by
  apply lucas_primality 29594351287506900995791 (3 : ZMod 29594351287506900995791)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (31, 1), (79, 1), (389, 1), (1035497806932613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (31, 1), (79, 1), (389, 1), (1035497806932613, 1)] : List FactorBlock).map factorBlockValue).prod) = 29594351287506900995791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_31
      · exact prime_oneHundredThirtyEightEF_79
      · exact prime_oneHundredThirtyEightEF_389
      · exact prime_oneHundredThirtyEightEF_1035497806932613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 29594351287506900995791) ^ 14797175643753450497895 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 29594351287506900995791) ^ 9864783762502300331930 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 29594351287506900995791) ^ 5918870257501380199158 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 29594351287506900995791) ^ 954656493145383903090 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 29594351287506900995791) ^ 374612041614011405010 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 29594351287506900995791) ^ 76078023875339077110 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 29594351287506900995791) ^ 28579830 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_97167007031868614497297 : Nat.Prime 97167007031868614497297 := by
  apply lucas_primality 97167007031868614497297 (10 : ZMod 97167007031868614497297)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (31, 1), (53, 1), (113, 1), (178571, 1), (61059135443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (31, 1), (53, 1), (113, 1), (178571, 1), (61059135443, 1)] : List FactorBlock).map factorBlockValue).prod) = 97167007031868614497297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_31
      · exact prime_oneHundredThirtyEightEF_53
      · exact prime_oneHundredThirtyEightEF_113
      · exact prime_oneHundredThirtyEightEF_178571
      · exact prime_oneHundredThirtyEightEF_61059135443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 97167007031868614497297) ^ 48583503515934307248648 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (10 : ZMod 97167007031868614497297) ^ 32389002343956204832432 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (10 : ZMod 97167007031868614497297) ^ 3134419581673181112816 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (10 : ZMod 97167007031868614497297) ^ 1833339755318275745232 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (10 : ZMod 97167007031868614497297) ^ 859885017981138181392 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (10 : ZMod 97167007031868614497297) ^ 544136545306172976 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (10 : ZMod 97167007031868614497297) ^ 1591359037872 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_125116145497384220682623 : Nat.Prime 125116145497384220682623 := by
  apply lucas_primality 125116145497384220682623 (7 : ZMod 125116145497384220682623)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (41, 1), (79, 1), (137927, 1), (20004379395641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (41, 1), (79, 1), (137927, 1), (20004379395641, 1)] : List FactorBlock).map factorBlockValue).prod) = 125116145497384220682623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_41
      · exact prime_oneHundredThirtyEightEF_79
      · exact prime_oneHundredThirtyEightEF_137927
      · exact prime_oneHundredThirtyEightEF_20004379395641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 125116145497384220682623) ^ 62558072748692110341311 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 125116145497384220682623) ^ 17873735071054888668946 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 125116145497384220682623) ^ 3051613304814249284942 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 125116145497384220682623) ^ 1583748677182078742818 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 125116145497384220682623) ^ 907118588074736786 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (7 : ZMod 125116145497384220682623) ^ 6254437742 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_348870611140977408793927 : Nat.Prime 348870611140977408793927 := by
  apply lucas_primality 348870611140977408793927 (5 : ZMod 348870611140977408793927)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (41, 1), (34439, 1), (36011, 1), (14850902257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (41, 1), (34439, 1), (36011, 1), (14850902257, 1)] : List FactorBlock).map factorBlockValue).prod) = 348870611140977408793927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_11
      · exact prime_oneHundredThirtyEightEF_41
      · exact prime_oneHundredThirtyEightEF_34439
      · exact prime_oneHundredThirtyEightEF_36011
      · exact prime_oneHundredThirtyEightEF_14850902257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 348870611140977408793927) ^ 174435305570488704396963 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 348870611140977408793927) ^ 116290203713659136264642 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 348870611140977408793927) ^ 49838658734425344113418 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 348870611140977408793927) ^ 31715510103725218981266 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 348870611140977408793927) ^ 8509039296121400214486 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 348870611140977408793927) ^ 10130102823571457034 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 348870611140977408793927) ^ 9687890120823565266 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 348870611140977408793927) ^ 23491543146918 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_495799769064908666838569 : Nat.Prime 495799769064908666838569 := by
  apply lucas_primality 495799769064908666838569 (3 : ZMod 495799769064908666838569)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 2), (19, 1), (557, 1), (4127, 1), (11727020864261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 2), (19, 1), (557, 1), (4127, 1), (11727020864261, 1)] : List FactorBlock).map factorBlockValue).prod) = 495799769064908666838569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_11
      · exact prime_oneHundredThirtyEightEF_19
      · exact prime_oneHundredThirtyEightEF_557
      · exact prime_oneHundredThirtyEightEF_4127
      · exact prime_oneHundredThirtyEightEF_11727020864261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 495799769064908666838569) ^ 247899884532454333419284 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 495799769064908666838569) ^ 45072706278628060621688 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 495799769064908666838569) ^ 26094724687626771938872 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 495799769064908666838569) ^ 890125258644360263624 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 495799769064908666838569) ^ 120135635828666989784 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 495799769064908666838569) ^ 42278407688 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_556480437421132229589197 : Nat.Prime 556480437421132229589197 := by
  apply lucas_primality 556480437421132229589197 (2 : ZMod 556480437421132229589197)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (6067, 1), (22930626232945946497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (6067, 1), (22930626232945946497, 1)] : List FactorBlock).map factorBlockValue).prod) = 556480437421132229589197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_6067
      · exact prime_oneHundredThirtyEightEF_22930626232945946497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 556480437421132229589197) ^ 278240218710566114794598 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 556480437421132229589197) ^ 91722504931783785988 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 556480437421132229589197) ^ 24268 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_677435257604414131417951 : Nat.Prime 677435257604414131417951 := by
  apply lucas_primality 677435257604414131417951 (3 : ZMod 677435257604414131417951)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (37, 1), (89, 1), (1371465244669327121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (37, 1), (89, 1), (1371465244669327121, 1)] : List FactorBlock).map factorBlockValue).prod) = 677435257604414131417951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_37
      · exact prime_oneHundredThirtyEightEF_89
      · exact prime_oneHundredThirtyEightEF_1371465244669327121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 677435257604414131417951) ^ 338717628802207065708975 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 677435257604414131417951) ^ 225811752534804710472650 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 677435257604414131417951) ^ 135487051520882826283590 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 677435257604414131417951) ^ 18309061016335517065350 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 677435257604414131417951) ^ 7611632107914765521550 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 677435257604414131417951) ^ 493950 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_878899926231809511221431 : Nat.Prime 878899926231809511221431 := by
  apply lucas_primality 878899926231809511221431 (6 : ZMod 878899926231809511221431)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (797, 1), (125287, 1), (13971226936099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (797, 1), (125287, 1), (13971226936099, 1)] : List FactorBlock).map factorBlockValue).prod) = 878899926231809511221431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_797
      · exact prime_oneHundredThirtyEightEF_125287
      · exact prime_oneHundredThirtyEightEF_13971226936099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 878899926231809511221431) ^ 439449963115904755610715 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 292966642077269837073810 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 175779985246361902244286 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 125557132318829930174490 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 1102760258760112310190 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 7015092756884668890 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 62907855570 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_1199300426390690201386121 : Nat.Prime 1199300426390690201386121 := by
  apply lucas_primality 1199300426390690201386121 (3 : ZMod 1199300426390690201386121)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 2), (101209, 1), (1752920250956893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 2), (101209, 1), (1752920250956893, 1)] : List FactorBlock).map factorBlockValue).prod) = 1199300426390690201386121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_13
      · exact prime_oneHundredThirtyEightEF_101209
      · exact prime_oneHundredThirtyEightEF_1752920250956893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1199300426390690201386121) ^ 599650213195345100693060 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1199300426390690201386121) ^ 239860085278138040277224 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1199300426390690201386121) ^ 92253878953130015491240 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1199300426390690201386121) ^ 11849740896468596680 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1199300426390690201386121) ^ 684172840 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_1306581484793701409438359 : Nat.Prime 1306581484793701409438359 := by
  apply lucas_primality 1306581484793701409438359 (3 : ZMod 1306581484793701409438359)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (167, 1), (191, 1), (5051, 1), (47513, 1), (28447597163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (167, 1), (191, 1), (5051, 1), (47513, 1), (28447597163, 1)] : List FactorBlock).map factorBlockValue).prod) = 1306581484793701409438359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_167
      · exact prime_oneHundredThirtyEightEF_191
      · exact prime_oneHundredThirtyEightEF_5051
      · exact prime_oneHundredThirtyEightEF_47513
      · exact prime_oneHundredThirtyEightEF_28447597163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1306581484793701409438359) ^ 653290742396850704719179 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1306581484793701409438359) ^ 435527161597900469812786 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1306581484793701409438359) ^ 7823841226309589278074 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1306581484793701409438359) ^ 6840740758082206332138 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1306581484793701409438359) ^ 258677783566363375458 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1306581484793701409438359) ^ 27499452461299042566 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1306581484793701409438359) ^ 45929414611266 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_1626794328565768563446051 : Nat.Prime 1626794328565768563446051 := by
  apply lucas_primality 1626794328565768563446051 (11 : ZMod 1626794328565768563446051)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (13, 1), (4907897, 1), (509945605110661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (13, 1), (4907897, 1), (509945605110661, 1)] : List FactorBlock).map factorBlockValue).prod) = 1626794328565768563446051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_13
      · exact prime_oneHundredThirtyEightEF_4907897
      · exact prime_oneHundredThirtyEightEF_509945605110661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1626794328565768563446051) ^ 813397164282884281723025 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 1626794328565768563446051) ^ 325358865713153712689210 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 1626794328565768563446051) ^ 125138025274289889495850 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 1626794328565768563446051) ^ 331464643321929650 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 1626794328565768563446051) ^ 3190133050 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_6715213615664697686720773 : Nat.Prime 6715213615664697686720773 := by
  apply lucas_primality 6715213615664697686720773 (2 : ZMod 6715213615664697686720773)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (23, 1), (101, 1), (25229, 1), (1979491, 1), (689092889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (23, 1), (101, 1), (25229, 1), (1979491, 1), (689092889, 1)] : List FactorBlock).map factorBlockValue).prod) = 6715213615664697686720773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_23
      · exact prime_oneHundredThirtyEightEF_101
      · exact prime_oneHundredThirtyEightEF_25229
      · exact prime_oneHundredThirtyEightEF_1979491
      · exact prime_oneHundredThirtyEightEF_689092889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6715213615664697686720773) ^ 3357606807832348843360386 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 6715213615664697686720773) ^ 2238404538554899228906924 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 6715213615664697686720773) ^ 959316230809242526674396 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 6715213615664697686720773) ^ 291965809376725986379164 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 6715213615664697686720773) ^ 66487263521432650363572 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 6715213615664697686720773) ^ 266170423546898318868 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 6715213615664697686720773) ^ 3392394113266843692 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 6715213615664697686720773) ^ 9745004951958948 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_7020345525223300128940099 : Nat.Prime 7020345525223300128940099 := by
  apply lucas_primality 7020345525223300128940099 (2 : ZMod 7020345525223300128940099)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2689, 1), (128368939, 1), (3389662691873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2689, 1), (128368939, 1), (3389662691873, 1)] : List FactorBlock).map factorBlockValue).prod) = 7020345525223300128940099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_2689
      · exact prime_oneHundredThirtyEightEF_128368939
      · exact prime_oneHundredThirtyEightEF_3389662691873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7020345525223300128940099) ^ 3510172762611650064470049 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 7020345525223300128940099) ^ 2340115175074433376313366 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 7020345525223300128940099) ^ 2610764419941725596482 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 7020345525223300128940099) ^ 54688817870678982 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 7020345525223300128940099) ^ 2071104461826 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_13065814847937014094383591 : Nat.Prime 13065814847937014094383591 := by
  apply lucas_primality 13065814847937014094383591 (23 : ZMod 13065814847937014094383591)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1306581484793701409438359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1306581484793701409438359, 1)] : List FactorBlock).map factorBlockValue).prod) = 13065814847937014094383591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_1306581484793701409438359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (23 : ZMod 13065814847937014094383591) ^ 6532907423968507047191795 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (23 : ZMod 13065814847937014094383591) ^ 2613162969587402818876718 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (23 : ZMod 13065814847937014094383591) ^ 10 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_18439515145364997174114817 : Nat.Prime 18439515145364997174114817 := by
  apply lucas_primality 18439515145364997174114817 (5 : ZMod 18439515145364997174114817)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 2), (23, 1), (139, 1), (173, 1), (1033033, 1), (7003805749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 2), (23, 1), (139, 1), (173, 1), (1033033, 1), (7003805749, 1)] : List FactorBlock).map factorBlockValue).prod) = 18439515145364997174114817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_23
      · exact prime_oneHundredThirtyEightEF_139
      · exact prime_oneHundredThirtyEightEF_173
      · exact prime_oneHundredThirtyEightEF_1033033
      · exact prime_oneHundredThirtyEightEF_7003805749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 18439515145364997174114817) ^ 9219757572682498587057408 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 18439515145364997174114817) ^ 6146505048454999058038272 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 18439515145364997174114817) ^ 801718049798478138004992 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 18439515145364997174114817) ^ 132658382340755375353344 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 18439515145364997174114817) ^ 106586792747774550139392 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 18439515145364997174114817) ^ 17849880057427978752 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 18439515145364997174114817) ^ 2632785060893184 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_38406975048538016712939713 : Nat.Prime 38406975048538016712939713 := by
  apply lucas_primality 38406975048538016712939713 (3 : ZMod 38406975048538016712939713)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (411211963949, 1), (1459366549967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (411211963949, 1), (1459366549967, 1)] : List FactorBlock).map factorBlockValue).prod) = 38406975048538016712939713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_411211963949
      · exact prime_oneHundredThirtyEightEF_1459366549967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 38406975048538016712939713) ^ 19203487524269008356469856 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 38406975048538016712939713) ^ 93399459197888 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 38406975048538016712939713) ^ 26317565692736 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_87622357683238182060455371 : Nat.Prime 87622357683238182060455371 := by
  apply lucas_primality 87622357683238182060455371 (3 : ZMod 87622357683238182060455371)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (367, 1), (137443, 1), (57903523208519959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (367, 1), (137443, 1), (57903523208519959, 1)] : List FactorBlock).map factorBlockValue).prod) = 87622357683238182060455371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_367
      · exact prime_oneHundredThirtyEightEF_137443
      · exact prime_oneHundredThirtyEightEF_57903523208519959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 87622357683238182060455371) ^ 43811178841619091030227685 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 87622357683238182060455371) ^ 29207452561079394020151790 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 87622357683238182060455371) ^ 17524471536647636412091074 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 87622357683238182060455371) ^ 238753018210458261745110 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 87622357683238182060455371) ^ 637517790525804748590 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 87622357683238182060455371) ^ 1513247430 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_976963053929278413153101203 : Nat.Prime 976963053929278413153101203 := by
  apply lucas_primality 976963053929278413153101203 (2 : ZMod 976963053929278413153101203)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (977, 1), (1049, 1), (1708338346069605703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (977, 1), (1049, 1), (1708338346069605703, 1)] : List FactorBlock).map factorBlockValue).prod) = 976963053929278413153101203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_31
      · exact prime_oneHundredThirtyEightEF_977
      · exact prime_oneHundredThirtyEightEF_1049
      · exact prime_oneHundredThirtyEightEF_1708338346069605703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 976963053929278413153101203) ^ 488481526964639206576550601 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 976963053929278413153101203) ^ 325654351309759471051033734 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 976963053929278413153101203) ^ 31514937223525110101712942 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 976963053929278413153101203) ^ 999962184165075141405426 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 976963053929278413153101203) ^ 931327982773382662681698 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 976963053929278413153101203) ^ 571879134 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_1754331505442897795662020439 : Nat.Prime 1754331505442897795662020439 := by
  apply lucas_primality 1754331505442897795662020439 (3 : ZMod 1754331505442897795662020439)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (167, 1), (977, 1), (1049, 1), (1708338346069605703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (167, 1), (977, 1), (1049, 1), (1708338346069605703, 1)] : List FactorBlock).map factorBlockValue).prod) = 1754331505442897795662020439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_167
      · exact prime_oneHundredThirtyEightEF_977
      · exact prime_oneHundredThirtyEightEF_1049
      · exact prime_oneHundredThirtyEightEF_1708338346069605703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1754331505442897795662020439) ^ 877165752721448897831010219 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1754331505442897795662020439) ^ 584777168480965931887340146 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1754331505442897795662020439) ^ 10504979074508370033904314 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1754331505442897795662020439) ^ 1795631018877070415211894 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1754331505442897795662020439) ^ 1672384657238224781374662 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1754331505442897795662020439) ^ 1026922746 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_1919445058896346999959622363 : Nat.Prime 1919445058896346999959622363 := by
  apply lucas_primality 1919445058896346999959622363 (2 : ZMod 1919445058896346999959622363)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (17, 1), (11047, 1), (135352271, 1), (381374519111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (17, 1), (11047, 1), (135352271, 1), (381374519111, 1)] : List FactorBlock).map factorBlockValue).prod) = 1919445058896346999959622363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_11
      · exact prime_oneHundredThirtyEightEF_17
      · exact prime_oneHundredThirtyEightEF_11047
      · exact prime_oneHundredThirtyEightEF_135352271
      · exact prime_oneHundredThirtyEightEF_381374519111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1919445058896346999959622363) ^ 959722529448173499979811181 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1919445058896346999959622363) ^ 639815019632115666653207454 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1919445058896346999959622363) ^ 174495005354213363632692942 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1919445058896346999959622363) ^ 112908532876255705879977786 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1919445058896346999959622363) ^ 173752607847953924138646 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1919445058896346999959622363) ^ 14181107156276284422 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1919445058896346999959622363) ^ 5032966186022742 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_1965696747062524036103227721 : Nat.Prime 1965696747062524036103227721 := by
  apply lucas_primality 1965696747062524036103227721 (3 : ZMod 1965696747062524036103227721)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (7020345525223300128940099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (7020345525223300128940099, 1)] : List FactorBlock).map factorBlockValue).prod) = 1965696747062524036103227721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_7
      · exact prime_oneHundredThirtyEightEF_7020345525223300128940099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1965696747062524036103227721) ^ 982848373531262018051613860 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1965696747062524036103227721) ^ 393139349412504807220645544 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1965696747062524036103227721) ^ 280813821008932005157603960 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1965696747062524036103227721) ^ 280 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_12550217692783807307428300063 : Nat.Prime 12550217692783807307428300063 := by
  apply lucas_primality 12550217692783807307428300063 (5 : ZMod 12550217692783807307428300063)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (41, 1), (421, 1), (863, 1), (15602017149911940271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (41, 1), (421, 1), (863, 1), (15602017149911940271, 1)] : List FactorBlock).map factorBlockValue).prod) = 12550217692783807307428300063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_41
      · exact prime_oneHundredThirtyEightEF_421
      · exact prime_oneHundredThirtyEightEF_863
      · exact prime_oneHundredThirtyEightEF_15602017149911940271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 12550217692783807307428300063) ^ 6275108846391903653714150031 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 12550217692783807307428300063) ^ 4183405897594602435809433354 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 12550217692783807307428300063) ^ 306102870555702617254348782 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 12550217692783807307428300063) ^ 29810493332028045860874822 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 12550217692783807307428300063) ^ 14542546573330020054957474 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (5 : ZMod 12550217692783807307428300063) ^ 804397122 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_16315283000618949499656790081 : Nat.Prime 16315283000618949499656790081 := by
  apply lucas_primality 16315283000618949499656790081 (14 : ZMod 16315283000618949499656790081)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (23, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (23, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 16315283000618949499656790081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_23
      · exact prime_oneHundredThirtyEightEF_171401
      · exact prime_oneHundredThirtyEightEF_714027719
      · exact prime_oneHundredThirtyEightEF_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 16315283000618949499656790081) ^ 8157641500309474749828395040 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (14 : ZMod 16315283000618949499656790081) ^ 5438427666872983166552263360 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (14 : ZMod 16315283000618949499656790081) ^ 3263056600123789899931358016 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (14 : ZMod 16315283000618949499656790081) ^ 709360130461693456506816960 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (14 : ZMod 16315283000618949499656790081) ^ 95187793540404953878080 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (14 : ZMod 16315283000618949499656790081) ^ 22849649343401680320 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (14 : ZMod 16315283000618949499656790081) ^ 2702262236620163520 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_23307547143741356428081128691 : Nat.Prime 23307547143741356428081128691 := by
  apply lucas_primality 23307547143741356428081128691 (2 : ZMod 23307547143741356428081128691)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1567, 1), (495799769064908666838569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1567, 1), (495799769064908666838569, 1)] : List FactorBlock).map factorBlockValue).prod) = 23307547143741356428081128691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_5
      · exact prime_oneHundredThirtyEightEF_1567
      · exact prime_oneHundredThirtyEightEF_495799769064908666838569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 23307547143741356428081128691) ^ 11653773571870678214040564345 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 23307547143741356428081128691) ^ 7769182381247118809360376230 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 23307547143741356428081128691) ^ 4661509428748271285616225738 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 23307547143741356428081128691) ^ 14873993071947260005157070 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 23307547143741356428081128691) ^ 47010 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_27192138334364915832761316803 : Nat.Prime 27192138334364915832761316803 := by
  apply lucas_primality 27192138334364915832761316803 (2 : ZMod 27192138334364915832761316803)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (10979, 1), (15149, 1), (63029, 1), (9642827, 1), (134499857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (10979, 1), (15149, 1), (63029, 1), (9642827, 1), (134499857, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364915832761316803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_10979
      · exact prime_oneHundredThirtyEightEF_15149
      · exact prime_oneHundredThirtyEightEF_63029
      · exact prime_oneHundredThirtyEightEF_9642827
      · exact prime_oneHundredThirtyEightEF_134499857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 27192138334364915832761316803) ^ 13596069167182457916380658401 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 27192138334364915832761316803) ^ 2476740899386548486452438 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 27192138334364915832761316803) ^ 1794979096598119732837898 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 27192138334364915832761316803) ^ 431422652023115007897338 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 27192138334364915832761316803) ^ 2819934271802752017926 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 27192138334364915832761316803) ^ 202172247174693396386 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_54384276668729831665522633627 : Nat.Prime 54384276668729831665522633627 := by
  apply lucas_primality 54384276668729831665522633627 (11 : ZMod 54384276668729831665522633627)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (937, 1), (1948313, 1), (261318517715367989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (937, 1), (1948313, 1), (261318517715367989, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729831665522633627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_19
      · exact prime_oneHundredThirtyEightEF_937
      · exact prime_oneHundredThirtyEightEF_1948313
      · exact prime_oneHundredThirtyEightEF_261318517715367989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 54384276668729831665522633627) ^ 27192138334364915832761316813 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 54384276668729831665522633627) ^ 18128092222909943888507544542 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 54384276668729831665522633627) ^ 2862330350985780613974875454 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 54384276668729831665522633627) ^ 58040850233436319813791498 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 54384276668729831665522633627) ^ 27913521425320177849002 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (11 : ZMod 54384276668729831665522633627) ^ 208114898034 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_81576415003094747498283950413 : Nat.Prime 81576415003094747498283950413 := by
  apply lucas_primality 81576415003094747498283950413 (2 : ZMod 81576415003094747498283950413)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (59, 1), (38406975048538016712939713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (59, 1), (38406975048538016712939713, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094747498283950413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_59
      · exact prime_oneHundredThirtyEightEF_38406975048538016712939713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 81576415003094747498283950413) ^ 40788207501547373749141975206 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 81576415003094747498283950413) ^ 27192138334364915832761316804 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 81576415003094747498283950413) ^ 1382651101747368601665829668 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 81576415003094747498283950413) ^ 2124 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyEightEF_163152830006189494996567900813 : Nat.Prime 163152830006189494996567900813 := by
  apply lucas_primality 163152830006189494996567900813 (2 : ZMod 163152830006189494996567900813)
  · rw [← oneHundredThirtyEightEFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (10979, 1), (15149, 1), (63029, 1), (9642827, 1), (134499857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (10979, 1), (15149, 1), (63029, 1), (9642827, 1), (134499857, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyEightEF_2
      · exact prime_oneHundredThirtyEightEF_3
      · exact prime_oneHundredThirtyEightEF_10979
      · exact prime_oneHundredThirtyEightEF_15149
      · exact prime_oneHundredThirtyEightEF_63029
      · exact prime_oneHundredThirtyEightEF_9642827
      · exact prime_oneHundredThirtyEightEF_134499857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 163152830006189494996567900813) ^ 81576415003094747498283950406 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 163152830006189494996567900813) ^ 54384276668729831665522633604 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 163152830006189494996567900813) ^ 14860445396319290918714628 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 163152830006189494996567900813) ^ 10769874579588718397027388 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 163152830006189494996567900813) ^ 2588535912138690047384028 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 163152830006189494996567900813) ^ 16919605630816512107556 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide
    · change (2 : ZMod 163152830006189494996567900813) ^ 1213033483048160378316 ≠ 1
      rw [← oneHundredThirtyEightEFFastPow_eq_pow]
      decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900800 : Nat.totient 163152830006189494996567900800 = 41615551457393649286459392000 := by
  rw [← show ((([(2, 7), (3, 1), (5, 2), (23, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900800 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_3, prime_oneHundredThirtyEightEF_5, prime_oneHundredThirtyEightEF_23, prime_oneHundredThirtyEightEF_171401, prime_oneHundredThirtyEightEF_714027719, prime_oneHundredThirtyEightEF_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900801 : Nat.totient 163152830006189494996567900801 = 162659908046033004508987021200 := by
  rw [← show ((([(331, 1), (17777867, 1), (41092771, 1), (674716820003, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900801 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_331, prime_oneHundredThirtyEightEF_17777867, prime_oneHundredThirtyEightEF_41092771, prime_oneHundredThirtyEightEF_674716820003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900802 : Nat.totient 163152830006189494996567900802 = 66242502408528065637704259720 := by
  rw [← show ((([(2, 1), (7, 2), (19, 1), (87622357683238182060455371, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900802 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_7, prime_oneHundredThirtyEightEF_19, prime_oneHundredThirtyEightEF_87622357683238182060455371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900803 : Nat.totient 163152830006189494996567900803 = 98880000193715084566656470400 := by
  rw [← show ((([(3, 1), (11, 1), (196661, 1), (2266639117, 1), (11091238618643, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900803 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_3, prime_oneHundredThirtyEightEF_11, prime_oneHundredThirtyEightEF_196661, prime_oneHundredThirtyEightEF_2266639117, prime_oneHundredThirtyEightEF_11091238618643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900804 : Nat.totient 163152830006189494996567900804 = 76777755651109896230923665408 := by
  rw [← show ((([(2, 2), (17, 1), (1651597, 1), (352648193, 1), (4119456777493, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900804 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_17, prime_oneHundredThirtyEightEF_1651597, prime_oneHundredThirtyEightEF_352648193, prime_oneHundredThirtyEightEF_4119456777493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900805 : Nat.totient 163152830006189494996567900805 = 123643499565634805671142731776 := by
  rw [← show ((([(5, 1), (29, 1), (53, 1), (531793, 1), (967881323, 1), (41246396627, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900805 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_5, prime_oneHundredThirtyEightEF_29, prime_oneHundredThirtyEightEF_53, prime_oneHundredThirtyEightEF_531793, prime_oneHundredThirtyEightEF_967881323, prime_oneHundredThirtyEightEF_41246396627]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900806 : Nat.totient 163152830006189494996567900806 = 48803509056563586910230912000 := by
  rw [← show ((([(2, 1), (3, 3), (13, 1), (41, 1), (421, 1), (863, 1), (15602017149911940271, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900806 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_3, prime_oneHundredThirtyEightEF_13, prime_oneHundredThirtyEightEF_41, prime_oneHundredThirtyEightEF_421, prime_oneHundredThirtyEightEF_863, prime_oneHundredThirtyEightEF_15602017149911940271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900807 : Nat.totient 163152830006189494996567900807 = 163095189460744967291811889152 := by
  rw [← show ((([(2833, 1), (3363713, 1), (84466127, 1), (202696627129, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900807 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2833, prime_oneHundredThirtyEightEF_3363713, prime_oneHundredThirtyEightEF_84466127, prime_oneHundredThirtyEightEF_202696627129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900808 : Nat.totient 163152830006189494996567900808 = 81549554148632088707537055168 := by
  rw [← show ((([(2, 3), (3037, 1), (6715213615664697686720773, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900808 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_3037, prime_oneHundredThirtyEightEF_6715213615664697686720773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900809 : Nat.totient 163152830006189494996567900809 = 90668477601577241559716843520 := by
  rw [← show ((([(3, 1), (7, 1), (37, 1), (2161, 1), (97167007031868614497297, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900809 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_3, prime_oneHundredThirtyEightEF_7, prime_oneHundredThirtyEightEF_37, prime_oneHundredThirtyEightEF_2161, prime_oneHundredThirtyEightEF_97167007031868614497297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900810 : Nat.totient 163152830006189494996567900810 = 65261132002475797998627160320 := by
  rw [← show ((([(2, 1), (5, 1), (16315283000618949499656790081, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900810 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_5, prime_oneHundredThirtyEightEF_16315283000618949499656790081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900811 : Nat.totient 163152830006189494996567900811 = 162421202961931815976649117760 := by
  rw [← show ((([(223, 1), (41956621481, 1), (17437701477413197, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900811 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_223, prime_oneHundredThirtyEightEF_41956621481, prime_oneHundredThirtyEightEF_17437701477413197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900812 : Nat.totient 163152830006189494996567900812 = 54374864802792827458860986368 := by
  rw [← show ((([(2, 2), (3, 1), (10979, 1), (15149, 1), (63029, 1), (9642827, 1), (134499857, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900812 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_3, prime_oneHundredThirtyEightEF_10979, prime_oneHundredThirtyEightEF_15149, prime_oneHundredThirtyEightEF_63029, prime_oneHundredThirtyEightEF_9642827, prime_oneHundredThirtyEightEF_134499857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900813 : Nat.totient 163152830006189494996567900813 = 163152830006189494996567900812 := by
  rw [← show ((([(163152830006189494996567900813, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900813 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_163152830006189494996567900813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900814 : Nat.totient 163152830006189494996567900814 = 74160376537741229469888463800 := by
  rw [← show ((([(2, 1), (11, 1), (100515631, 1), (73779945007300088027, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900814 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_11, prime_oneHundredThirtyEightEF_100515631, prime_oneHundredThirtyEightEF_73779945007300088027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900815 : Nat.totient 163152830006189494996567900815 = 85580850875081711764046423040 := by
  rw [← show ((([(3, 2), (5, 1), (61, 1), (11383, 1), (5221502938062639826289, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900815 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_3, prime_oneHundredThirtyEightEF_5, prime_oneHundredThirtyEightEF_61, prime_oneHundredThirtyEightEF_11383, prime_oneHundredThirtyEightEF_5221502938062639826289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900816 : Nat.totient 163152830006189494996567900816 = 69037544704246549419885871104 := by
  rw [← show ((([(2, 4), (7, 1), (79, 1), (18439515145364997174114817, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900816 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_7, prime_oneHundredThirtyEightEF_79, prime_oneHundredThirtyEightEF_18439515145364997174114817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900817 : Nat.totient 163152830006189494996567900817 = 163139764191341557982473504740 := by
  rw [← show ((([(12487, 1), (13065814847937014094383591, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900817 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_12487, prime_oneHundredThirtyEightEF_13065814847937014094383591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900818 : Nat.totient 163152830006189494996567900818 = 54384276668729831665522633604 := by
  rw [← show ((([(2, 1), (3, 1), (27192138334364915832761316803, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900818 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_3, prime_oneHundredThirtyEightEF_27192138334364915832761316803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900819 : Nat.totient 163152830006189494996567900819 = 150602612313405687689139600744 := by
  rw [← show ((([(13, 1), (12550217692783807307428300063, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900819 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_13, prime_oneHundredThirtyEightEF_12550217692783807307428300063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900820 : Nat.totient 163152830006189494996567900820 = 64102881573487753001431138944 := by
  rw [← show ((([(2, 2), (5, 1), (67, 1), (349, 1), (348870611140977408793927, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900820 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_5, prime_oneHundredThirtyEightEF_67, prime_oneHundredThirtyEightEF_349, prime_oneHundredThirtyEightEF_348870611140977408793927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900821 : Nat.totient 163152830006189494996567900821 = 94031936258781915235354890240 := by
  rw [← show ((([(3, 1), (17, 1), (19, 2), (47, 1), (107, 1), (6437285321, 1), (273736581179, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900821 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_3, prime_oneHundredThirtyEightEF_17, prime_oneHundredThirtyEightEF_19, prime_oneHundredThirtyEightEF_47, prime_oneHundredThirtyEightEF_107, prime_oneHundredThirtyEightEF_6437285321, prime_oneHundredThirtyEightEF_273736581179]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900822 : Nat.totient 163152830006189494996567900822 = 81498334432064961655171952640 := by
  rw [← show ((([(2, 1), (1433, 1), (4093, 1), (71483, 1), (843473, 1), (230676166141, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900822 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_1433, prime_oneHundredThirtyEightEF_4093, prime_oneHundredThirtyEightEF_71483, prime_oneHundredThirtyEightEF_843473, prime_oneHundredThirtyEightEF_230676166141]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900823 : Nat.totient 163152830006189494996567900823 = 133649038382513881514375531520 := by
  rw [← show ((([(7, 1), (23, 1), (1153, 1), (878899926231809511221431, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900823 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_7, prime_oneHundredThirtyEightEF_23, prime_oneHundredThirtyEightEF_1153, prime_oneHundredThirtyEightEF_878899926231809511221431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900824 : Nat.totient 163152830006189494996567900824 = 53462509267564919264412079104 := by
  rw [← show ((([(2, 3), (3, 2), (59, 1), (38406975048538016712939713, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900824 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_3, prime_oneHundredThirtyEightEF_59, prime_oneHundredThirtyEightEF_38406975048538016712939713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900825 : Nat.totient 163152830006189494996567900825 = 118656603035291440149465192000 := by
  rw [← show ((([(5, 2), (11, 1), (195940831, 1), (3027868235407889213, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900825 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_5, prime_oneHundredThirtyEightEF_11, prime_oneHundredThirtyEightEF_195940831, prime_oneHundredThirtyEightEF_3027868235407889213]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900826 : Nat.totient 163152830006189494996567900826 = 81576415003094747498283950412 := by
  rw [← show ((([(2, 1), (81576415003094747498283950413, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900826 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_81576415003094747498283950413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900827 : Nat.totient 163152830006189494996567900827 = 105259890326573867739721226280 := by
  rw [← show ((([(3, 1), (31, 1), (1754331505442897795662020439, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900827 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_3, prime_oneHundredThirtyEightEF_31, prime_oneHundredThirtyEightEF_1754331505442897795662020439]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900828 : Nat.totient 163152830006189494996567900828 = 81435648060767370802253230080 := by
  rw [← show ((([(2, 2), (647, 1), (11059, 1), (11131, 1), (82782577, 1), (6186447857, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900828 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_647, prime_oneHundredThirtyEightEF_11059, prime_oneHundredThirtyEightEF_11131, prime_oneHundredThirtyEightEF_82782577, prime_oneHundredThirtyEightEF_6186447857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900829 : Nat.totient 163152830006189494996567900829 = 163152694578580218745959779856 := by
  rw [← show ((([(1204787, 1), (22963759909, 1), (5897138680963, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900829 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_1204787, prime_oneHundredThirtyEightEF_22963759909, prime_oneHundredThirtyEightEF_5897138680963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900830 : Nat.totient 163152830006189494996567900830 = 37268277041071054668921479424 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (7, 1), (1567, 1), (495799769064908666838569, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900830 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_3, prime_oneHundredThirtyEightEF_5, prime_oneHundredThirtyEightEF_7, prime_oneHundredThirtyEightEF_1567, prime_oneHundredThirtyEightEF_495799769064908666838569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900831 : Nat.totient 163152830006189494996567900831 = 163152797760916975834667280000 := by
  rw [← show ((([(5060051, 1), (121904674741, 1), (264496151441, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900831 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_5060051, prime_oneHundredThirtyEightEF_121904674741, prime_oneHundredThirtyEightEF_264496151441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900832 : Nat.totient 163152830006189494996567900832 = 75257962370931144271510278144 := by
  rw [← show ((([(2, 5), (13, 1), (2549, 1), (10093, 1), (11863, 1), (1285039985930447, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900832 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_13, prime_oneHundredThirtyEightEF_2549, prime_oneHundredThirtyEightEF_10093, prime_oneHundredThirtyEightEF_11863, prime_oneHundredThirtyEightEF_1285039985930447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900833 : Nat.totient 163152830006189494996567900833 = 108767490282900426257402604192 := by
  rw [← show ((([(3, 4), (102317, 1), (19686195541427289576629, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900833 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_3, prime_oneHundredThirtyEightEF_102317, prime_oneHundredThirtyEightEF_19686195541427289576629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900834 : Nat.totient 163152830006189494996567900834 = 78763327682583029849524078400 := by
  rw [← show ((([(2, 1), (29, 2), (732827, 1), (9568988021, 1), (13832514911, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900834 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_29, prime_oneHundredThirtyEightEF_732827, prime_oneHundredThirtyEightEF_9568988021, prime_oneHundredThirtyEightEF_13832514911]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900835 : Nat.totient 163152830006189494996567900835 = 130100610171648757481429483520 := by
  rw [← show ((([(5, 1), (317, 1), (13127, 1), (54490803541, 1), (143905252993, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900835 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_5, prime_oneHundredThirtyEightEF_317, prime_oneHundredThirtyEightEF_13127, prime_oneHundredThirtyEightEF_54490803541, prime_oneHundredThirtyEightEF_143905252993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900836 : Nat.totient 163152830006189494996567900836 = 49256269437056481194053302400 := by
  rw [← show ((([(2, 2), (3, 1), (11, 1), (269, 1), (260171, 1), (17660765089967180327, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900836 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_3, prime_oneHundredThirtyEightEF_11, prime_oneHundredThirtyEightEF_269, prime_oneHundredThirtyEightEF_260171, prime_oneHundredThirtyEightEF_17660765089967180327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900837 : Nat.totient 163152830006189494996567900837 = 139845282862448138568486772140 := by
  rw [← show ((([(7, 1), (23307547143741356428081128691, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900837 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_7, prime_oneHundredThirtyEightEF_23307547143741356428081128691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900838 : Nat.totient 163152830006189494996567900838 = 76757267740119795616024831104 := by
  rw [← show ((([(2, 1), (17, 1), (3739, 1), (254909047, 1), (5034716024068079, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900838 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_17, prime_oneHundredThirtyEightEF_3739, prime_oneHundredThirtyEightEF_254909047, prime_oneHundredThirtyEightEF_5034716024068079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900839 : Nat.totient 163152830006189494996567900839 = 108767440376584821066585893376 := by
  rw [← show ((([(3, 1), (97729, 1), (556480437421132229589197, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900839 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_3, prime_oneHundredThirtyEightEF_97729, prime_oneHundredThirtyEightEF_556480437421132229589197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900840 : Nat.totient 163152830006189494996567900840 = 61480937058492342483858055680 := by
  rw [← show ((([(2, 3), (5, 1), (19, 1), (179, 1), (1199300426390690201386121, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900840 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_5, prime_oneHundredThirtyEightEF_19, prime_oneHundredThirtyEightEF_179, prime_oneHundredThirtyEightEF_1199300426390690201386121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900841 : Nat.totient 163152830006189494996567900841 = 163151203211860929228004354500 := by
  rw [← show ((([(100291, 1), (1626794328565768563446051, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900841 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_100291, prime_oneHundredThirtyEightEF_1626794328565768563446051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900842 : Nat.totient 163152830006189494996567900842 = 53086141235274243916077941760 := by
  rw [← show ((([(2, 1), (3, 2), (43, 1), (1597, 1), (432499, 1), (305185311208195361, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900842 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_3, prime_oneHundredThirtyEightEF_43, prime_oneHundredThirtyEightEF_1597, prime_oneHundredThirtyEightEF_432499, prime_oneHundredThirtyEightEF_305185311208195361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900843 : Nat.totient 163152830006189494996567900843 = 161187133259126970960464673040 := by
  rw [← show ((([(83, 1), (1965696747062524036103227721, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900843 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_83, prime_oneHundredThirtyEightEF_1965696747062524036103227721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900844 : Nat.totient 163152830006189494996567900844 = 69922641416616829700751765456 := by
  rw [← show ((([(2, 2), (7, 1), (4786848419, 1), (1217269960504119967, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900844 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_7, prime_oneHundredThirtyEightEF_4786848419, prime_oneHundredThirtyEightEF_1217269960504119967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900845 : Nat.totient 163152830006189494996567900845 = 80321391475236025388181722880 := by
  rw [← show ((([(3, 1), (5, 1), (13, 2), (45673997, 1), (1409118863239069111, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900845 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_3, prime_oneHundredThirtyEightEF_5, prime_oneHundredThirtyEightEF_13, prime_oneHundredThirtyEightEF_45673997, prime_oneHundredThirtyEightEF_1409118863239069111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900846 : Nat.totient 163152830006189494996567900846 = 75918270703718758884273974016 := by
  rw [← show ((([(2, 1), (23, 1), (37, 1), (31177, 1), (3074685732733041494149, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900846 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_23, prime_oneHundredThirtyEightEF_37, prime_oneHundredThirtyEightEF_31177, prime_oneHundredThirtyEightEF_3074685732733041494149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900847 : Nat.totient 163152830006189494996567900847 = 144699678782144151279135961600 := by
  rw [← show ((([(11, 1), (41, 1), (41387, 1), (3150604199, 1), (2774343778169, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900847 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_11, prime_oneHundredThirtyEightEF_41, prime_oneHundredThirtyEightEF_41387, prime_oneHundredThirtyEightEF_3150604199, prime_oneHundredThirtyEightEF_2774343778169]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900848 : Nat.totient 163152830006189494996567900848 = 53956054017768822405884713728 := by
  rw [← show ((([(2, 4), (3, 1), (127, 1), (2577668428667, 1), (10382993943589, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900848 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_3, prime_oneHundredThirtyEightEF_127, prime_oneHundredThirtyEightEF_2577668428667, prime_oneHundredThirtyEightEF_10382993943589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900849 : Nat.totient 163152830006189494996567900849 = 162604482723252926448639049216 := by
  rw [← show ((([(359, 1), (1733, 1), (2043987233, 1), (128299044275099, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900849 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_359, prime_oneHundredThirtyEightEF_1733, prime_oneHundredThirtyEightEF_2043987233, prime_oneHundredThirtyEightEF_128299044275099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900850 : Nat.totient 163152830006189494996567900850 = 64927748714152995420301728000 := by
  rw [← show ((([(2, 1), (5, 2), (199, 1), (11941, 1), (977485711, 1), (1404819136933, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900850 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_5, prime_oneHundredThirtyEightEF_199, prime_oneHundredThirtyEightEF_11941, prime_oneHundredThirtyEightEF_977485711, prime_oneHundredThirtyEightEF_1404819136933]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900851 : Nat.totient 163152830006189494996567900851 = 91917027918649966003767290880 := by
  rw [← show ((([(3, 2), (7, 2), (71, 1), (1547197, 1), (3367844712889765153, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900851 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_3, prime_oneHundredThirtyEightEF_7, prime_oneHundredThirtyEightEF_71, prime_oneHundredThirtyEightEF_1547197, prime_oneHundredThirtyEightEF_3367844712889765153]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900852 : Nat.totient 163152830006189494996567900852 = 80778373726275836406028720800 := by
  rw [← show ((([(2, 2), (103, 1), (13381, 1), (29594351287506900995791, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900852 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_103, prime_oneHundredThirtyEightEF_13381, prime_oneHundredThirtyEightEF_29594351287506900995791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900853 : Nat.totient 163152830006189494996567900853 = 161524943837123028901265002000 := by
  rw [← show ((([(101, 1), (12911, 1), (125116145497384220682623, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900853 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_101, prime_oneHundredThirtyEightEF_12911, prime_oneHundredThirtyEightEF_125116145497384220682623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900854 : Nat.totient 163152830006189494996567900854 = 54333991242747525360120381312 := by
  rw [← show ((([(2, 1), (3, 1), (1093, 1), (102983, 1), (58233839, 1), (4148415406349, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900854 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_3, prime_oneHundredThirtyEightEF_1093, prime_oneHundredThirtyEightEF_102983, prime_oneHundredThirtyEightEF_58233839, prime_oneHundredThirtyEightEF_4148415406349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900855 : Nat.totient 163152830006189494996567900855 = 122844483769366207997415831168 := by
  rw [← show ((([(5, 1), (17, 1), (1919445058896346999959622363, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900855 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_5, prime_oneHundredThirtyEightEF_17, prime_oneHundredThirtyEightEF_1919445058896346999959622363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900856 : Nat.totient 163152830006189494996567900856 = 81514360473935218549478402688 := by
  rw [← show ((([(2, 3), (1319, 1), (393157, 1), (4484229943, 1), (8770128203, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900856 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_1319, prime_oneHundredThirtyEightEF_393157, prime_oneHundredThirtyEightEF_4484229943, prime_oneHundredThirtyEightEF_8770128203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900857 : Nat.totient 163152830006189494996567900857 = 108768305910611909737343941760 := by
  rw [← show ((([(3, 1), (440831, 1), (157274357, 1), (784410342216857, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900857 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_3, prime_oneHundredThirtyEightEF_440831, prime_oneHundredThirtyEightEF_157274357, prime_oneHundredThirtyEightEF_784410342216857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900858 : Nat.totient 163152830006189494996567900858 = 55404367130312738766379008000 := by
  rw [← show ((([(2, 1), (7, 1), (11, 1), (13, 1), (31, 2), (53, 1), (181, 1), (318098309, 1), (27790179097, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900858 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_7, prime_oneHundredThirtyEightEF_11, prime_oneHundredThirtyEightEF_13, prime_oneHundredThirtyEightEF_31, prime_oneHundredThirtyEightEF_53, prime_oneHundredThirtyEightEF_181, prime_oneHundredThirtyEightEF_318098309, prime_oneHundredThirtyEightEF_27790179097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900859 : Nat.totient 163152830006189494996567900859 = 154273489162918451286045714720 := by
  rw [← show ((([(19, 1), (659, 1), (2671, 1), (6589883, 1), (740293615282103, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900859 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_19, prime_oneHundredThirtyEightEF_659, prime_oneHundredThirtyEightEF_2671, prime_oneHundredThirtyEightEF_6589883, prime_oneHundredThirtyEightEF_740293615282103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900860 : Nat.totient 163152830006189494996567900860 = 43473643265192353697177745408 := by
  rw [← show ((([(2, 2), (3, 3), (5, 1), (1289, 1), (1723669, 1), (135985957393556749, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900860 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_3, prime_oneHundredThirtyEightEF_5, prime_oneHundredThirtyEightEF_1289, prime_oneHundredThirtyEightEF_1723669, prime_oneHundredThirtyEightEF_135985957393556749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900861 : Nat.totient 163152830006189494996567900861 = 163068403207767242698476601344 := by
  rw [← show ((([(1933, 1), (7502813, 1), (146280997, 1), (76904317697, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900861 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_1933, prime_oneHundredThirtyEightEF_7502813, prime_oneHundredThirtyEightEF_146280997, prime_oneHundredThirtyEightEF_76904317697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900862 : Nat.totient 163152830006189494996567900862 = 81211199806937142366652800000 := by
  rw [← show ((([(2, 1), (251, 1), (2081, 1), (75347, 1), (930173, 1), (2228379320971, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900862 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_251, prime_oneHundredThirtyEightEF_2081, prime_oneHundredThirtyEightEF_75347, prime_oneHundredThirtyEightEF_930173, prime_oneHundredThirtyEightEF_2228379320971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900863 : Nat.totient 163152830006189494996567900863 = 104215140274263486137136230400 := by
  rw [← show ((([(3, 1), (29, 1), (131, 1), (94463, 1), (15835373, 1), (9570046137121, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900863 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_3, prime_oneHundredThirtyEightEF_29, prime_oneHundredThirtyEightEF_131, prime_oneHundredThirtyEightEF_94463, prime_oneHundredThirtyEightEF_15835373, prime_oneHundredThirtyEightEF_9570046137121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900864 : Nat.totient 163152830006189494996567900864 = 79297022290207632506861322240 := by
  rw [← show ((([(2, 6), (73, 1), (137, 1), (139, 1), (6066709541, 1), (302275680349, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900864 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_73, prime_oneHundredThirtyEightEF_137, prime_oneHundredThirtyEightEF_139, prime_oneHundredThirtyEightEF_6066709541, prime_oneHundredThirtyEightEF_302275680349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900865 : Nat.totient 163152830006189494996567900865 = 111135320557950251988615960000 := by
  rw [← show ((([(5, 1), (7, 1), (151, 1), (31120339, 1), (991985446212325951, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900865 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_5, prime_oneHundredThirtyEightEF_7, prime_oneHundredThirtyEightEF_151, prime_oneHundredThirtyEightEF_31120339, prime_oneHundredThirtyEightEF_991985446212325951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900866 : Nat.totient 163152830006189494996567900866 = 54384276668728153391504717184 := by
  rw [← show ((([(2, 1), (3, 1), (33763383185377, 1), (805373625772843, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900866 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_3, prime_oneHundredThirtyEightEF_33763383185377, prime_oneHundredThirtyEightEF_805373625772843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900867 : Nat.totient 163152830006189494996567900867 = 162958182544868038638820524672 := by
  rw [← show ((([(887, 1), (15217, 1), (12087652072375107603173, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900867 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_887, prime_oneHundredThirtyEightEF_15217, prime_oneHundredThirtyEightEF_12087652072375107603173]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900868 : Nat.totient 163152830006189494996567900868 = 79669781402203393127602466976 := by
  rw [← show ((([(2, 2), (47, 1), (467, 1), (190117865719, 1), (9774554023907, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900868 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_47, prime_oneHundredThirtyEightEF_467, prime_oneHundredThirtyEightEF_190117865719, prime_oneHundredThirtyEightEF_9774554023907]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900869 : Nat.totient 163152830006189494996567900869 = 94374836819425221615059328000 := by
  rw [← show ((([(3, 2), (11, 1), (23, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900869 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_3, prime_oneHundredThirtyEightEF_11, prime_oneHundredThirtyEightEF_23, prime_oneHundredThirtyEightEF_461, prime_oneHundredThirtyEightEF_69997, prime_oneHundredThirtyEightEF_2220502305087140441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900870 : Nat.totient 163152830006189494996567900870 = 65158636711753954666301509248 := by
  rw [← show ((([(2, 1), (5, 1), (773, 1), (3607, 1), (5851523790925058935517, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900870 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_5, prime_oneHundredThirtyEightEF_773, prime_oneHundredThirtyEightEF_3607, prime_oneHundredThirtyEightEF_5851523790925058935517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900871 : Nat.totient 163152830006189494996567900871 = 150602577738148096834232095200 := by
  rw [← show ((([(13, 1), (4362427, 1), (2871859811, 1), (1001751151411, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900871 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_13, prime_oneHundredThirtyEightEF_4362427, prime_oneHundredThirtyEightEF_2871859811, prime_oneHundredThirtyEightEF_1001751151411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900872 : Nat.totient 163152830006189494996567900872 = 43856517674530438254895595520 := by
  rw [← show ((([(2, 3), (3, 1), (7, 1), (17, 1), (2657, 1), (21500316536914473447941, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900872 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_3, prime_oneHundredThirtyEightEF_7, prime_oneHundredThirtyEightEF_17, prime_oneHundredThirtyEightEF_2657, prime_oneHundredThirtyEightEF_21500316536914473447941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900873 : Nat.totient 163152830006189494996567900873 = 163152829985084599426111135108 := by
  rw [← show ((([(7730567987, 1), (21104895562726197779, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900873 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_7730567987, prime_oneHundredThirtyEightEF_21104895562726197779]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900874 : Nat.totient 163152830006189494996567900874 = 81220185985703719103938133184 := by
  rw [← show ((([(2, 1), (229, 1), (620405717, 1), (574186982349158909, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900874 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_229, prime_oneHundredThirtyEightEF_620405717, prime_oneHundredThirtyEightEF_574186982349158909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900875 : Nat.totient 163152830006189494996567900875 = 86962184631772554628760371200 := by
  rw [← show ((([(3, 1), (5, 3), (1657, 1), (601589, 1), (436456482815239553, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900875 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_3, prime_oneHundredThirtyEightEF_5, prime_oneHundredThirtyEightEF_1657, prime_oneHundredThirtyEightEF_601589, prime_oneHundredThirtyEightEF_436456482815239553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900876 : Nat.totient 163152830006189494996567900876 = 80239087425659697868374097920 := by
  rw [← show ((([(2, 2), (61, 2), (15019549, 1), (20292353, 1), (35965462487, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900876 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_61, prime_oneHundredThirtyEightEF_15019549, prime_oneHundredThirtyEightEF_20292353, prime_oneHundredThirtyEightEF_35965462487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900877 : Nat.totient 163152830006189494996567900877 = 161439168355438286163849343488 := by
  rw [← show ((([(97, 1), (5519, 1), (67043, 1), (19180019, 1), (237006365467, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900877 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_97, prime_oneHundredThirtyEightEF_5519, prime_oneHundredThirtyEightEF_67043, prime_oneHundredThirtyEightEF_19180019, prime_oneHundredThirtyEightEF_237006365467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900878 : Nat.totient 163152830006189494996567900878 = 51466933832935529214180246528 := by
  rw [← show ((([(2, 1), (3, 2), (19, 1), (937, 1), (1948313, 1), (261318517715367989, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900878 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_3, prime_oneHundredThirtyEightEF_19, prime_oneHundredThirtyEightEF_937, prime_oneHundredThirtyEightEF_1948313, prime_oneHundredThirtyEightEF_261318517715367989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900879 : Nat.totient 163152830006189494996567900879 = 139845282862355792893224584160 := by
  rw [← show ((([(7, 1), (1514516462477, 1), (15389431360568861, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900879 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_7, prime_oneHundredThirtyEightEF_1514516462477, prime_oneHundredThirtyEightEF_15389431360568861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900880 : Nat.totient 163152830006189494996567900880 = 59025822354576638687182848000 := by
  rw [← show ((([(2, 4), (5, 1), (11, 3), (263, 1), (769, 1), (1476473, 1), (5131200336701, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900880 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_5, prime_oneHundredThirtyEightEF_11, prime_oneHundredThirtyEightEF_263, prime_oneHundredThirtyEightEF_769, prime_oneHundredThirtyEightEF_1476473, prime_oneHundredThirtyEightEF_5131200336701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900881 : Nat.totient 163152830006189494996567900881 = 108768553337459663331045267252 := by
  rw [← show ((([(3, 1), (54384276668729831665522633627, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900881 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_3, prime_oneHundredThirtyEightEF_54384276668729831665522633627]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900882 : Nat.totient 163152830006189494996567900882 = 81576414933614786185117234500 := by
  rw [← show ((([(2, 1), (1174099891, 1), (69479961311992616051, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900882 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_1174099891, prime_oneHundredThirtyEightEF_69479961311992616051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900883 : Nat.totient 163152830006189494996567900883 = 154654326819101684165368707072 := by
  rw [← show ((([(37, 1), (59, 1), (163, 1), (373, 1), (6397, 1), (148853, 1), (1290953195339, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900883 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_37, prime_oneHundredThirtyEightEF_59, prime_oneHundredThirtyEightEF_163, prime_oneHundredThirtyEightEF_373, prime_oneHundredThirtyEightEF_6397, prime_oneHundredThirtyEightEF_148853, prime_oneHundredThirtyEightEF_1290953195339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900884 : Nat.totient 163152830006189494996567900884 = 49636815557740527051985471488 := by
  rw [← show ((([(2, 2), (3, 1), (13, 1), (89, 1), (102211363, 1), (114969019264351177, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900884 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_3, prime_oneHundredThirtyEightEF_13, prime_oneHundredThirtyEightEF_89, prime_oneHundredThirtyEightEF_102211363, prime_oneHundredThirtyEightEF_114969019264351177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900885 : Nat.totient 163152830006189494996567900885 = 127033172614059209470803747840 := by
  rw [← show ((([(5, 1), (43, 1), (281, 1), (714928392707, 1), (3777350514617, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900885 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_5, prime_oneHundredThirtyEightEF_43, prime_oneHundredThirtyEightEF_281, prime_oneHundredThirtyEightEF_714928392707, prime_oneHundredThirtyEightEF_3777350514617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900886 : Nat.totient 163152830006189494996567900886 = 69281149076396591760983269152 := by
  rw [← show ((([(2, 1), (7, 1), (109, 1), (299134639, 1), (357415490990239999, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900886 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_7, prime_oneHundredThirtyEightEF_109, prime_oneHundredThirtyEightEF_299134639, prime_oneHundredThirtyEightEF_357415490990239999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900887 : Nat.totient 163152830006189494996567900887 = 107142185106929378929816719360 := by
  rw [← show ((([(3, 3), (67, 1), (36241, 1), (204234839, 1), (12185014335457, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900887 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_3, prime_oneHundredThirtyEightEF_67, prime_oneHundredThirtyEightEF_36241, prime_oneHundredThirtyEightEF_204234839, prime_oneHundredThirtyEightEF_12185014335457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900888 : Nat.totient 163152830006189494996567900888 = 79586746341819775119099109120 := by
  rw [← show ((([(2, 3), (41, 1), (29887239047, 1), (16643128656708293, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900888 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_41, prime_oneHundredThirtyEightEF_29887239047, prime_oneHundredThirtyEightEF_16643128656708293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900889 : Nat.totient 163152830006189494996567900889 = 148277029184454165084760896000 := by
  rw [← show ((([(17, 1), (31, 1), (457, 1), (677435257604414131417951, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900889 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_17, prime_oneHundredThirtyEightEF_31, prime_oneHundredThirtyEightEF_457, prime_oneHundredThirtyEightEF_677435257604414131417951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900890 : Nat.totient 163152830006189494996567900890 = 43507421334978063453435248384 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (7578033636209, 1), (717656839221107, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900890 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_3, prime_oneHundredThirtyEightEF_5, prime_oneHundredThirtyEightEF_7578033636209, prime_oneHundredThirtyEightEF_717656839221107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900891 : Nat.totient 163152830006189494996567900891 = 148103710540821795472525979680 := by
  rw [← show ((([(11, 1), (797, 1), (4787, 1), (3887587502410238495879, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900891 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_11, prime_oneHundredThirtyEightEF_797, prime_oneHundredThirtyEightEF_4787, prime_oneHundredThirtyEightEF_3887587502410238495879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900892 : Nat.totient 163152830006189494996567900892 = 74505913884937039819856740352 := by
  rw [← show ((([(2, 2), (23, 1), (29, 1), (113, 1), (449, 1), (1205269042013298899237, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900892 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_23, prime_oneHundredThirtyEightEF_29, prime_oneHundredThirtyEightEF_113, prime_oneHundredThirtyEightEF_449, prime_oneHundredThirtyEightEF_1205269042013298899237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900893 : Nat.totient 163152830006189494996567900893 = 93230188573467966362580645360 := by
  rw [← show ((([(3, 1), (7, 1), (62258942191, 1), (124788216886380263, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900893 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_3, prime_oneHundredThirtyEightEF_7, prime_oneHundredThirtyEightEF_62258942191, prime_oneHundredThirtyEightEF_124788216886380263]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900894 : Nat.totient 163152830006189494996567900894 = 81495363274405181032436101944 := by
  rw [← show ((([(2, 1), (1039, 1), (32119, 1), (2444483176691693030567, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900894 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_1039, prime_oneHundredThirtyEightEF_32119, prime_oneHundredThirtyEightEF_2444483176691693030567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900895 : Nat.totient 163152830006189494996567900895 = 128856947915470347103946688000 := by
  rw [← show ((([(5, 1), (79, 1), (9811, 1), (481519921, 1), (87431913027871, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900895 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_5, prime_oneHundredThirtyEightEF_79, prime_oneHundredThirtyEightEF_9811, prime_oneHundredThirtyEightEF_481519921, prime_oneHundredThirtyEightEF_87431913027871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900896 : Nat.totient 163152830006189494996567900896 = 54384276330307172357547275520 := by
  rw [← show ((([(2, 5), (3, 2), (160699277, 1), (3525236034297377371, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900896 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_3, prime_oneHundredThirtyEightEF_160699277, prime_oneHundredThirtyEightEF_3525236034297377371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900897 : Nat.totient 163152830006189494996567900897 = 142676159011314363292658393664 := by
  rw [← show ((([(13, 1), (19, 1), (6358573219, 1), (103881444870472429, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900897 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_13, prime_oneHundredThirtyEightEF_19, prime_oneHundredThirtyEightEF_6358573219, prime_oneHundredThirtyEightEF_103881444870472429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900898 : Nat.totient 163152830006189494996567900898 = 81576401350656940015022946036 := by
  rw [← show ((([(2, 1), (5975227, 1), (13652437807483255029187, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900898 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_5975227, prime_oneHundredThirtyEightEF_13652437807483255029187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900899 : Nat.totient 163152830006189494996567900899 = 108768553336877818660077583496 := by
  rw [← show ((([(3, 1), (186937560239, 1), (290922148546281647, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900899 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_3, prime_oneHundredThirtyEightEF_186937560239, prime_oneHundredThirtyEightEF_290922148546281647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900900 : Nat.totient 163152830006189494996567900900 = 55937228045571854331549696000 := by
  rw [← show ((([(2, 2), (5, 2), (7, 3), (152729, 1), (162641, 1), (319981, 1), (598445707, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900900 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_2, prime_oneHundredThirtyEightEF_5, prime_oneHundredThirtyEightEF_7, prime_oneHundredThirtyEightEF_152729, prime_oneHundredThirtyEightEF_162641, prime_oneHundredThirtyEightEF_319981, prime_oneHundredThirtyEightEF_598445707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyEightEF_163152830006189494996567900901 : Nat.totient 163152830006189494996567900901 = 162175866952260216583414799532 := by
  rw [← show ((([(167, 1), (976963053929278413153101203, 1)] : List FactorBlock).map factorBlockValue).prod) = 163152830006189494996567900901 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyEightEF_167, prime_oneHundredThirtyEightEF_976963053929278413153101203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredThirtyEightEF : certifiedKill 1 163152830006189494996567900799 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredThirtyEightEF_163152830006189494996567900800, phi_oneHundredThirtyEightEF_163152830006189494996567900801, phi_oneHundredThirtyEightEF_163152830006189494996567900802,
    phi_oneHundredThirtyEightEF_163152830006189494996567900803, phi_oneHundredThirtyEightEF_163152830006189494996567900804, phi_oneHundredThirtyEightEF_163152830006189494996567900805,
    phi_oneHundredThirtyEightEF_163152830006189494996567900806, phi_oneHundredThirtyEightEF_163152830006189494996567900807, phi_oneHundredThirtyEightEF_163152830006189494996567900808,
    phi_oneHundredThirtyEightEF_163152830006189494996567900809, phi_oneHundredThirtyEightEF_163152830006189494996567900810, phi_oneHundredThirtyEightEF_163152830006189494996567900811,
    phi_oneHundredThirtyEightEF_163152830006189494996567900812, phi_oneHundredThirtyEightEF_163152830006189494996567900813, phi_oneHundredThirtyEightEF_163152830006189494996567900814,
    phi_oneHundredThirtyEightEF_163152830006189494996567900815, phi_oneHundredThirtyEightEF_163152830006189494996567900816, phi_oneHundredThirtyEightEF_163152830006189494996567900817,
    phi_oneHundredThirtyEightEF_163152830006189494996567900818, phi_oneHundredThirtyEightEF_163152830006189494996567900819, phi_oneHundredThirtyEightEF_163152830006189494996567900820,
    phi_oneHundredThirtyEightEF_163152830006189494996567900821, phi_oneHundredThirtyEightEF_163152830006189494996567900822, phi_oneHundredThirtyEightEF_163152830006189494996567900823,
    phi_oneHundredThirtyEightEF_163152830006189494996567900824, phi_oneHundredThirtyEightEF_163152830006189494996567900825, phi_oneHundredThirtyEightEF_163152830006189494996567900826,
    phi_oneHundredThirtyEightEF_163152830006189494996567900827, phi_oneHundredThirtyEightEF_163152830006189494996567900828, phi_oneHundredThirtyEightEF_163152830006189494996567900829,
    phi_oneHundredThirtyEightEF_163152830006189494996567900830, phi_oneHundredThirtyEightEF_163152830006189494996567900831, phi_oneHundredThirtyEightEF_163152830006189494996567900832,
    phi_oneHundredThirtyEightEF_163152830006189494996567900833, phi_oneHundredThirtyEightEF_163152830006189494996567900834, phi_oneHundredThirtyEightEF_163152830006189494996567900835,
    phi_oneHundredThirtyEightEF_163152830006189494996567900836, phi_oneHundredThirtyEightEF_163152830006189494996567900837, phi_oneHundredThirtyEightEF_163152830006189494996567900838,
    phi_oneHundredThirtyEightEF_163152830006189494996567900839, phi_oneHundredThirtyEightEF_163152830006189494996567900840, phi_oneHundredThirtyEightEF_163152830006189494996567900841,
    phi_oneHundredThirtyEightEF_163152830006189494996567900842, phi_oneHundredThirtyEightEF_163152830006189494996567900843, phi_oneHundredThirtyEightEF_163152830006189494996567900844,
    phi_oneHundredThirtyEightEF_163152830006189494996567900845, phi_oneHundredThirtyEightEF_163152830006189494996567900846, phi_oneHundredThirtyEightEF_163152830006189494996567900847,
    phi_oneHundredThirtyEightEF_163152830006189494996567900848, phi_oneHundredThirtyEightEF_163152830006189494996567900849, phi_oneHundredThirtyEightEF_163152830006189494996567900850,
    phi_oneHundredThirtyEightEF_163152830006189494996567900851, phi_oneHundredThirtyEightEF_163152830006189494996567900852, phi_oneHundredThirtyEightEF_163152830006189494996567900853,
    phi_oneHundredThirtyEightEF_163152830006189494996567900854, phi_oneHundredThirtyEightEF_163152830006189494996567900855, phi_oneHundredThirtyEightEF_163152830006189494996567900856,
    phi_oneHundredThirtyEightEF_163152830006189494996567900857, phi_oneHundredThirtyEightEF_163152830006189494996567900858, phi_oneHundredThirtyEightEF_163152830006189494996567900859,
    phi_oneHundredThirtyEightEF_163152830006189494996567900860, phi_oneHundredThirtyEightEF_163152830006189494996567900861, phi_oneHundredThirtyEightEF_163152830006189494996567900862,
    phi_oneHundredThirtyEightEF_163152830006189494996567900863, phi_oneHundredThirtyEightEF_163152830006189494996567900864, phi_oneHundredThirtyEightEF_163152830006189494996567900865,
    phi_oneHundredThirtyEightEF_163152830006189494996567900866, phi_oneHundredThirtyEightEF_163152830006189494996567900867, phi_oneHundredThirtyEightEF_163152830006189494996567900868,
    phi_oneHundredThirtyEightEF_163152830006189494996567900869, phi_oneHundredThirtyEightEF_163152830006189494996567900870, phi_oneHundredThirtyEightEF_163152830006189494996567900871,
    phi_oneHundredThirtyEightEF_163152830006189494996567900872, phi_oneHundredThirtyEightEF_163152830006189494996567900873, phi_oneHundredThirtyEightEF_163152830006189494996567900874,
    phi_oneHundredThirtyEightEF_163152830006189494996567900875, phi_oneHundredThirtyEightEF_163152830006189494996567900876, phi_oneHundredThirtyEightEF_163152830006189494996567900877,
    phi_oneHundredThirtyEightEF_163152830006189494996567900878, phi_oneHundredThirtyEightEF_163152830006189494996567900879, phi_oneHundredThirtyEightEF_163152830006189494996567900880,
    phi_oneHundredThirtyEightEF_163152830006189494996567900881, phi_oneHundredThirtyEightEF_163152830006189494996567900882, phi_oneHundredThirtyEightEF_163152830006189494996567900883,
    phi_oneHundredThirtyEightEF_163152830006189494996567900884, phi_oneHundredThirtyEightEF_163152830006189494996567900885, phi_oneHundredThirtyEightEF_163152830006189494996567900886,
    phi_oneHundredThirtyEightEF_163152830006189494996567900887, phi_oneHundredThirtyEightEF_163152830006189494996567900888, phi_oneHundredThirtyEightEF_163152830006189494996567900889,
    phi_oneHundredThirtyEightEF_163152830006189494996567900890, phi_oneHundredThirtyEightEF_163152830006189494996567900891, phi_oneHundredThirtyEightEF_163152830006189494996567900892,
    phi_oneHundredThirtyEightEF_163152830006189494996567900893, phi_oneHundredThirtyEightEF_163152830006189494996567900894, phi_oneHundredThirtyEightEF_163152830006189494996567900895,
    phi_oneHundredThirtyEightEF_163152830006189494996567900896, phi_oneHundredThirtyEightEF_163152830006189494996567900897, phi_oneHundredThirtyEightEF_163152830006189494996567900898,
    phi_oneHundredThirtyEightEF_163152830006189494996567900899, phi_oneHundredThirtyEightEF_163152830006189494996567900900, phi_oneHundredThirtyEightEF_163152830006189494996567900901]

end TotientTailPeriodKiller
end Erdos249257
