import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredNineteenDMFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredNineteenDMFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredNineteenDMFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredNineteenDMFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredNineteenDMFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredNineteenDMFastPow a n * oneHundredNineteenDMFastPow a n * a else oneHundredNineteenDMFastPow a n * oneHundredNineteenDMFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredNineteenDM_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredNineteenDM_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredNineteenDM_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredNineteenDM_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredNineteenDM_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredNineteenDM_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredNineteenDM_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredNineteenDM_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredNineteenDM_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredNineteenDM_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredNineteenDM_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredNineteenDM_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredNineteenDM_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredNineteenDM_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredNineteenDM_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredNineteenDM_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredNineteenDM_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredNineteenDM_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredNineteenDM_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredNineteenDM_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredNineteenDM_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredNineteenDM_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredNineteenDM_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredNineteenDM_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredNineteenDM_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredNineteenDM_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredNineteenDM_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredNineteenDM_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredNineteenDM_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredNineteenDM_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredNineteenDM_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredNineteenDM_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredNineteenDM_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredNineteenDM_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredNineteenDM_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredNineteenDM_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredNineteenDM_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredNineteenDM_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredNineteenDM_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredNineteenDM_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredNineteenDM_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredNineteenDM_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredNineteenDM_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredNineteenDM_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredNineteenDM_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredNineteenDM_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredNineteenDM_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredNineteenDM_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredNineteenDM_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredNineteenDM_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredNineteenDM_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredNineteenDM_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredNineteenDM_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredNineteenDM_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredNineteenDM_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredNineteenDM_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredNineteenDM_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredNineteenDM_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredNineteenDM_331 : Nat.Prime 331 := by norm_num

private theorem prime_oneHundredNineteenDM_337 : Nat.Prime 337 := by norm_num

private theorem prime_oneHundredNineteenDM_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredNineteenDM_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredNineteenDM_359 : Nat.Prime 359 := by norm_num

private theorem prime_oneHundredNineteenDM_373 : Nat.Prime 373 := by norm_num

private theorem prime_oneHundredNineteenDM_379 : Nat.Prime 379 := by norm_num

private theorem prime_oneHundredNineteenDM_383 : Nat.Prime 383 := by norm_num

private theorem prime_oneHundredNineteenDM_389 : Nat.Prime 389 := by norm_num

private theorem prime_oneHundredNineteenDM_401 : Nat.Prime 401 := by norm_num

private theorem prime_oneHundredNineteenDM_409 : Nat.Prime 409 := by norm_num

private theorem prime_oneHundredNineteenDM_421 : Nat.Prime 421 := by norm_num

private theorem prime_oneHundredNineteenDM_431 : Nat.Prime 431 := by norm_num

private theorem prime_oneHundredNineteenDM_433 : Nat.Prime 433 := by norm_num

private theorem prime_oneHundredNineteenDM_443 : Nat.Prime 443 := by norm_num

private theorem prime_oneHundredNineteenDM_449 : Nat.Prime 449 := by norm_num

private theorem prime_oneHundredNineteenDM_463 : Nat.Prime 463 := by norm_num

private theorem prime_oneHundredNineteenDM_479 : Nat.Prime 479 := by norm_num

private theorem prime_oneHundredNineteenDM_487 : Nat.Prime 487 := by norm_num

private theorem prime_oneHundredNineteenDM_503 : Nat.Prime 503 := by norm_num

private theorem prime_oneHundredNineteenDM_521 : Nat.Prime 521 := by norm_num

private theorem prime_oneHundredNineteenDM_523 : Nat.Prime 523 := by norm_num

private theorem prime_oneHundredNineteenDM_541 : Nat.Prime 541 := by norm_num

private theorem prime_oneHundredNineteenDM_547 : Nat.Prime 547 := by norm_num

private theorem prime_oneHundredNineteenDM_557 : Nat.Prime 557 := by norm_num

private theorem prime_oneHundredNineteenDM_571 : Nat.Prime 571 := by norm_num

private theorem prime_oneHundredNineteenDM_593 : Nat.Prime 593 := by norm_num

private theorem prime_oneHundredNineteenDM_607 : Nat.Prime 607 := by norm_num

private theorem prime_oneHundredNineteenDM_617 : Nat.Prime 617 := by norm_num

private theorem prime_oneHundredNineteenDM_619 : Nat.Prime 619 := by norm_num

private theorem prime_oneHundredNineteenDM_631 : Nat.Prime 631 := by norm_num

private theorem prime_oneHundredNineteenDM_659 : Nat.Prime 659 := by norm_num

private theorem prime_oneHundredNineteenDM_661 : Nat.Prime 661 := by norm_num

private theorem prime_oneHundredNineteenDM_691 : Nat.Prime 691 := by norm_num

private theorem prime_oneHundredNineteenDM_701 : Nat.Prime 701 := by norm_num

private theorem prime_oneHundredNineteenDM_719 : Nat.Prime 719 := by norm_num

private theorem prime_oneHundredNineteenDM_727 : Nat.Prime 727 := by norm_num

private theorem prime_oneHundredNineteenDM_809 : Nat.Prime 809 := by norm_num

private theorem prime_oneHundredNineteenDM_811 : Nat.Prime 811 := by norm_num

private theorem prime_oneHundredNineteenDM_821 : Nat.Prime 821 := by norm_num

private theorem prime_oneHundredNineteenDM_859 : Nat.Prime 859 := by norm_num

private theorem prime_oneHundredNineteenDM_881 : Nat.Prime 881 := by norm_num

private theorem prime_oneHundredNineteenDM_971 : Nat.Prime 971 := by norm_num

private theorem prime_oneHundredNineteenDM_983 : Nat.Prime 983 := by norm_num

private theorem prime_oneHundredNineteenDM_1039 : Nat.Prime 1039 := by norm_num

private theorem prime_oneHundredNineteenDM_1049 : Nat.Prime 1049 := by norm_num

private theorem prime_oneHundredNineteenDM_1051 : Nat.Prime 1051 := by norm_num

private theorem prime_oneHundredNineteenDM_1061 : Nat.Prime 1061 := by norm_num

private theorem prime_oneHundredNineteenDM_1063 : Nat.Prime 1063 := by norm_num

private theorem prime_oneHundredNineteenDM_1069 : Nat.Prime 1069 := by norm_num

private theorem prime_oneHundredNineteenDM_1087 : Nat.Prime 1087 := by norm_num

private theorem prime_oneHundredNineteenDM_1103 : Nat.Prime 1103 := by norm_num

private theorem prime_oneHundredNineteenDM_1109 : Nat.Prime 1109 := by norm_num

private theorem prime_oneHundredNineteenDM_1117 : Nat.Prime 1117 := by norm_num

private theorem prime_oneHundredNineteenDM_1163 : Nat.Prime 1163 := by norm_num

private theorem prime_oneHundredNineteenDM_1171 : Nat.Prime 1171 := by norm_num

private theorem prime_oneHundredNineteenDM_1201 : Nat.Prime 1201 := by norm_num

private theorem prime_oneHundredNineteenDM_1231 : Nat.Prime 1231 := by norm_num

private theorem prime_oneHundredNineteenDM_1297 : Nat.Prime 1297 := by norm_num

private theorem prime_oneHundredNineteenDM_1307 : Nat.Prime 1307 := by norm_num

private theorem prime_oneHundredNineteenDM_1321 : Nat.Prime 1321 := by norm_num

private theorem prime_oneHundredNineteenDM_1399 : Nat.Prime 1399 := by norm_num

private theorem prime_oneHundredNineteenDM_1423 : Nat.Prime 1423 := by norm_num

private theorem prime_oneHundredNineteenDM_1493 : Nat.Prime 1493 := by norm_num

private theorem prime_oneHundredNineteenDM_1567 : Nat.Prime 1567 := by norm_num

private theorem prime_oneHundredNineteenDM_1607 : Nat.Prime 1607 := by norm_num

private theorem prime_oneHundredNineteenDM_1613 : Nat.Prime 1613 := by norm_num

private theorem prime_oneHundredNineteenDM_1663 : Nat.Prime 1663 := by norm_num

private theorem prime_oneHundredNineteenDM_1669 : Nat.Prime 1669 := by norm_num

private theorem prime_oneHundredNineteenDM_1789 : Nat.Prime 1789 := by norm_num

private theorem prime_oneHundredNineteenDM_1823 : Nat.Prime 1823 := by norm_num

private theorem prime_oneHundredNineteenDM_1831 : Nat.Prime 1831 := by norm_num

private theorem prime_oneHundredNineteenDM_1847 : Nat.Prime 1847 := by norm_num

private theorem prime_oneHundredNineteenDM_1879 : Nat.Prime 1879 := by norm_num

private theorem prime_oneHundredNineteenDM_1931 : Nat.Prime 1931 := by norm_num

private theorem prime_oneHundredNineteenDM_2003 : Nat.Prime 2003 := by norm_num

private theorem prime_oneHundredNineteenDM_2179 : Nat.Prime 2179 := by norm_num

private theorem prime_oneHundredNineteenDM_2239 : Nat.Prime 2239 := by norm_num

private theorem prime_oneHundredNineteenDM_2341 : Nat.Prime 2341 := by norm_num

private theorem prime_oneHundredNineteenDM_2437 : Nat.Prime 2437 := by norm_num

private theorem prime_oneHundredNineteenDM_2447 : Nat.Prime 2447 := by norm_num

private theorem prime_oneHundredNineteenDM_2477 : Nat.Prime 2477 := by norm_num

private theorem prime_oneHundredNineteenDM_2591 : Nat.Prime 2591 := by norm_num

private theorem prime_oneHundredNineteenDM_2657 : Nat.Prime 2657 := by norm_num

private theorem prime_oneHundredNineteenDM_2659 : Nat.Prime 2659 := by norm_num

private theorem prime_oneHundredNineteenDM_2689 : Nat.Prime 2689 := by norm_num

private theorem prime_oneHundredNineteenDM_2767 : Nat.Prime 2767 := by norm_num

private theorem prime_oneHundredNineteenDM_2897 : Nat.Prime 2897 := by norm_num

private theorem prime_oneHundredNineteenDM_2927 : Nat.Prime 2927 := by norm_num

private theorem prime_oneHundredNineteenDM_3181 : Nat.Prime 3181 := by norm_num

private theorem prime_oneHundredNineteenDM_3187 : Nat.Prime 3187 := by norm_num

private theorem prime_oneHundredNineteenDM_3271 : Nat.Prime 3271 := by norm_num

private theorem prime_oneHundredNineteenDM_3361 : Nat.Prime 3361 := by norm_num

private theorem prime_oneHundredNineteenDM_3463 : Nat.Prime 3463 := by norm_num

private theorem prime_oneHundredNineteenDM_3467 : Nat.Prime 3467 := by norm_num

private theorem prime_oneHundredNineteenDM_3583 : Nat.Prime 3583 := by norm_num

private theorem prime_oneHundredNineteenDM_3617 : Nat.Prime 3617 := by norm_num

private theorem prime_oneHundredNineteenDM_3769 : Nat.Prime 3769 := by norm_num

private theorem prime_oneHundredNineteenDM_3877 : Nat.Prime 3877 := by norm_num

private theorem prime_oneHundredNineteenDM_3881 : Nat.Prime 3881 := by norm_num

private theorem prime_oneHundredNineteenDM_3931 : Nat.Prime 3931 := by norm_num

private theorem prime_oneHundredNineteenDM_3967 : Nat.Prime 3967 := by norm_num

private theorem prime_oneHundredNineteenDM_4051 : Nat.Prime 4051 := by norm_num

private theorem prime_oneHundredNineteenDM_4057 : Nat.Prime 4057 := by norm_num

private theorem prime_oneHundredNineteenDM_4111 : Nat.Prime 4111 := by norm_num

private theorem prime_oneHundredNineteenDM_4177 : Nat.Prime 4177 := by norm_num

private theorem prime_oneHundredNineteenDM_4457 : Nat.Prime 4457 := by norm_num

private theorem prime_oneHundredNineteenDM_4649 : Nat.Prime 4649 := by norm_num

private theorem prime_oneHundredNineteenDM_4673 : Nat.Prime 4673 := by norm_num

private theorem prime_oneHundredNineteenDM_4871 : Nat.Prime 4871 := by norm_num

private theorem prime_oneHundredNineteenDM_4903 : Nat.Prime 4903 := by norm_num

private theorem prime_oneHundredNineteenDM_4933 : Nat.Prime 4933 := by norm_num

private theorem prime_oneHundredNineteenDM_4967 : Nat.Prime 4967 := by norm_num

private theorem prime_oneHundredNineteenDM_5227 : Nat.Prime 5227 := by norm_num

private theorem prime_oneHundredNineteenDM_5237 : Nat.Prime 5237 := by norm_num

private theorem prime_oneHundredNineteenDM_5471 : Nat.Prime 5471 := by norm_num

private theorem prime_oneHundredNineteenDM_5569 : Nat.Prime 5569 := by norm_num

private theorem prime_oneHundredNineteenDM_5573 : Nat.Prime 5573 := by norm_num

private theorem prime_oneHundredNineteenDM_5741 : Nat.Prime 5741 := by norm_num

private theorem prime_oneHundredNineteenDM_6361 : Nat.Prime 6361 := by norm_num

private theorem prime_oneHundredNineteenDM_6481 : Nat.Prime 6481 := by norm_num

private theorem prime_oneHundredNineteenDM_6521 : Nat.Prime 6521 := by norm_num

private theorem prime_oneHundredNineteenDM_6529 : Nat.Prime 6529 := by norm_num

private theorem prime_oneHundredNineteenDM_6571 : Nat.Prime 6571 := by norm_num

private theorem prime_oneHundredNineteenDM_6581 : Nat.Prime 6581 := by norm_num

private theorem prime_oneHundredNineteenDM_6653 : Nat.Prime 6653 := by norm_num

private theorem prime_oneHundredNineteenDM_6869 : Nat.Prime 6869 := by norm_num

private theorem prime_oneHundredNineteenDM_6977 : Nat.Prime 6977 := by norm_num

private theorem prime_oneHundredNineteenDM_7211 : Nat.Prime 7211 := by norm_num

private theorem prime_oneHundredNineteenDM_7229 : Nat.Prime 7229 := by norm_num

private theorem prime_oneHundredNineteenDM_7529 : Nat.Prime 7529 := by norm_num

private theorem prime_oneHundredNineteenDM_7717 : Nat.Prime 7717 := by norm_num

private theorem prime_oneHundredNineteenDM_7727 : Nat.Prime 7727 := by norm_num

private theorem prime_oneHundredNineteenDM_7867 : Nat.Prime 7867 := by norm_num

private theorem prime_oneHundredNineteenDM_8009 : Nat.Prime 8009 := by norm_num

private theorem prime_oneHundredNineteenDM_8171 : Nat.Prime 8171 := by norm_num

private theorem prime_oneHundredNineteenDM_8219 : Nat.Prime 8219 := by norm_num

private theorem prime_oneHundredNineteenDM_8329 : Nat.Prime 8329 := by norm_num

private theorem prime_oneHundredNineteenDM_8377 : Nat.Prime 8377 := by norm_num

private theorem prime_oneHundredNineteenDM_8431 : Nat.Prime 8431 := by norm_num

private theorem prime_oneHundredNineteenDM_9059 : Nat.Prime 9059 := by norm_num

private theorem prime_oneHundredNineteenDM_9467 : Nat.Prime 9467 := by norm_num

private theorem prime_oneHundredNineteenDM_9491 : Nat.Prime 9491 := by norm_num

private theorem prime_oneHundredNineteenDM_9551 : Nat.Prime 9551 := by norm_num

private theorem prime_oneHundredNineteenDM_9769 : Nat.Prime 9769 := by norm_num

private theorem prime_oneHundredNineteenDM_9857 : Nat.Prime 9857 := by norm_num

private theorem prime_oneHundredNineteenDM_10853 : Nat.Prime 10853 := by norm_num

private theorem prime_oneHundredNineteenDM_11069 : Nat.Prime 11069 := by norm_num

private theorem prime_oneHundredNineteenDM_11261 : Nat.Prime 11261 := by norm_num

private theorem prime_oneHundredNineteenDM_11299 : Nat.Prime 11299 := by norm_num

private theorem prime_oneHundredNineteenDM_12107 : Nat.Prime 12107 := by norm_num

private theorem prime_oneHundredNineteenDM_12203 : Nat.Prime 12203 := by norm_num

private theorem prime_oneHundredNineteenDM_12401 : Nat.Prime 12401 := by norm_num

private theorem prime_oneHundredNineteenDM_12479 : Nat.Prime 12479 := by norm_num

private theorem prime_oneHundredNineteenDM_12583 : Nat.Prime 12583 := by norm_num

private theorem prime_oneHundredNineteenDM_12899 : Nat.Prime 12899 := by norm_num

private theorem prime_oneHundredNineteenDM_13441 : Nat.Prime 13441 := by norm_num

private theorem prime_oneHundredNineteenDM_13669 : Nat.Prime 13669 := by norm_num

private theorem prime_oneHundredNineteenDM_14831 : Nat.Prime 14831 := by norm_num

private theorem prime_oneHundredNineteenDM_14957 : Nat.Prime 14957 := by norm_num

private theorem prime_oneHundredNineteenDM_15173 : Nat.Prime 15173 := by norm_num

private theorem prime_oneHundredNineteenDM_15443 : Nat.Prime 15443 := by norm_num

private theorem prime_oneHundredNineteenDM_15473 : Nat.Prime 15473 := by norm_num

private theorem prime_oneHundredNineteenDM_15923 : Nat.Prime 15923 := by norm_num

private theorem prime_oneHundredNineteenDM_16487 : Nat.Prime 16487 := by norm_num

private theorem prime_oneHundredNineteenDM_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredNineteenDM_17207 : Nat.Prime 17207 := by norm_num

private theorem prime_oneHundredNineteenDM_17293 : Nat.Prime 17293 := by norm_num

private theorem prime_oneHundredNineteenDM_17509 : Nat.Prime 17509 := by norm_num

private theorem prime_oneHundredNineteenDM_19073 : Nat.Prime 19073 := by norm_num

private theorem prime_oneHundredNineteenDM_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredNineteenDM_21317 : Nat.Prime 21317 := by norm_num

private theorem prime_oneHundredNineteenDM_21377 : Nat.Prime 21377 := by norm_num

private theorem prime_oneHundredNineteenDM_21977 : Nat.Prime 21977 := by norm_num

private theorem prime_oneHundredNineteenDM_22091 : Nat.Prime 22091 := by norm_num

private theorem prime_oneHundredNineteenDM_22621 : Nat.Prime 22621 := by norm_num

private theorem prime_oneHundredNineteenDM_23029 : Nat.Prime 23029 := by norm_num

private theorem prime_oneHundredNineteenDM_23269 : Nat.Prime 23269 := by norm_num

private theorem prime_oneHundredNineteenDM_23509 : Nat.Prime 23509 := by norm_num

private theorem prime_oneHundredNineteenDM_23719 : Nat.Prime 23719 := by norm_num

private theorem prime_oneHundredNineteenDM_25541 : Nat.Prime 25541 := by norm_num

private theorem prime_oneHundredNineteenDM_26053 : Nat.Prime 26053 := by norm_num

private theorem prime_oneHundredNineteenDM_26297 : Nat.Prime 26297 := by norm_num

private theorem prime_oneHundredNineteenDM_28393 : Nat.Prime 28393 := by norm_num

private theorem prime_oneHundredNineteenDM_29347 : Nat.Prime 29347 := by norm_num

private theorem prime_oneHundredNineteenDM_30491 : Nat.Prime 30491 := by norm_num

private theorem prime_oneHundredNineteenDM_33623 : Nat.Prime 33623 := by norm_num

private theorem prime_oneHundredNineteenDM_33857 : Nat.Prime 33857 := by norm_num

private theorem prime_oneHundredNineteenDM_36073 : Nat.Prime 36073 := by norm_num

private theorem prime_oneHundredNineteenDM_36629 : Nat.Prime 36629 := by norm_num

private theorem prime_oneHundredNineteenDM_37039 : Nat.Prime 37039 := by norm_num

private theorem prime_oneHundredNineteenDM_39373 : Nat.Prime 39373 := by norm_num

private theorem prime_oneHundredNineteenDM_40433 : Nat.Prime 40433 := by norm_num

private theorem prime_oneHundredNineteenDM_41269 : Nat.Prime 41269 := by norm_num

private theorem prime_oneHundredNineteenDM_41999 : Nat.Prime 41999 := by norm_num

private theorem prime_oneHundredNineteenDM_42323 : Nat.Prime 42323 := by norm_num

private theorem prime_oneHundredNineteenDM_43117 : Nat.Prime 43117 := by norm_num

private theorem prime_oneHundredNineteenDM_43607 : Nat.Prime 43607 := by norm_num

private theorem prime_oneHundredNineteenDM_44797 : Nat.Prime 44797 := by norm_num

private theorem prime_oneHundredNineteenDM_45013 : Nat.Prime 45013 := by norm_num

private theorem prime_oneHundredNineteenDM_46307 : Nat.Prime 46307 := by norm_num

private theorem prime_oneHundredNineteenDM_46619 : Nat.Prime 46619 := by norm_num

private theorem prime_oneHundredNineteenDM_46861 : Nat.Prime 46861 := by norm_num

private theorem prime_oneHundredNineteenDM_47111 : Nat.Prime 47111 := by norm_num

private theorem prime_oneHundredNineteenDM_47317 : Nat.Prime 47317 := by norm_num

private theorem prime_oneHundredNineteenDM_47623 : Nat.Prime 47623 := by norm_num

private theorem prime_oneHundredNineteenDM_47699 : Nat.Prime 47699 := by norm_num

private theorem prime_oneHundredNineteenDM_49369 : Nat.Prime 49369 := by norm_num

private theorem prime_oneHundredNineteenDM_49559 : Nat.Prime 49559 := by norm_num

private theorem prime_oneHundredNineteenDM_50077 : Nat.Prime 50077 := by norm_num

private theorem prime_oneHundredNineteenDM_52027 : Nat.Prime 52027 := by norm_num

private theorem prime_oneHundredNineteenDM_52153 : Nat.Prime 52153 := by norm_num

private theorem prime_oneHundredNineteenDM_52253 : Nat.Prime 52253 := by norm_num

private theorem prime_oneHundredNineteenDM_52363 : Nat.Prime 52363 := by norm_num

private theorem prime_oneHundredNineteenDM_53327 : Nat.Prime 53327 := by norm_num

private theorem prime_oneHundredNineteenDM_59239 : Nat.Prime 59239 := by norm_num

private theorem prime_oneHundredNineteenDM_59473 : Nat.Prime 59473 := by norm_num

private theorem prime_oneHundredNineteenDM_62627 : Nat.Prime 62627 := by norm_num

private theorem prime_oneHundredNineteenDM_65033 : Nat.Prime 65033 := by norm_num

private theorem prime_oneHundredNineteenDM_65731 : Nat.Prime 65731 := by norm_num

private theorem prime_oneHundredNineteenDM_67343 : Nat.Prime 67343 := by norm_num

private theorem prime_oneHundredNineteenDM_67411 : Nat.Prime 67411 := by norm_num

private theorem prime_oneHundredNineteenDM_67807 : Nat.Prime 67807 := by norm_num

private theorem prime_oneHundredNineteenDM_69557 : Nat.Prime 69557 := by norm_num

private theorem prime_oneHundredNineteenDM_70571 : Nat.Prime 70571 := by norm_num

private theorem prime_oneHundredNineteenDM_77269 : Nat.Prime 77269 := by norm_num

private theorem prime_oneHundredNineteenDM_80831 : Nat.Prime 80831 := by norm_num

private theorem prime_oneHundredNineteenDM_85601 : Nat.Prime 85601 := by norm_num

private theorem prime_oneHundredNineteenDM_87881 : Nat.Prime 87881 := by norm_num

private theorem prime_oneHundredNineteenDM_89597 : Nat.Prime 89597 := by norm_num

private theorem prime_oneHundredNineteenDM_91571 : Nat.Prime 91571 := by norm_num

private theorem prime_oneHundredNineteenDM_92179 : Nat.Prime 92179 := by norm_num

private theorem prime_oneHundredNineteenDM_98887 : Nat.Prime 98887 := by norm_num

private theorem prime_oneHundredNineteenDM_104311 : Nat.Prime 104311 := by norm_num

private theorem prime_oneHundredNineteenDM_126583 : Nat.Prime 126583 := by norm_num

private theorem prime_oneHundredNineteenDM_132173 : Nat.Prime 132173 := by norm_num

private theorem prime_oneHundredNineteenDM_132761 : Nat.Prime 132761 := by norm_num

private theorem prime_oneHundredNineteenDM_145829 : Nat.Prime 145829 := by norm_num

private theorem prime_oneHundredNineteenDM_148193 : Nat.Prime 148193 := by norm_num

private theorem prime_oneHundredNineteenDM_151433 : Nat.Prime 151433 := by norm_num

private theorem prime_oneHundredNineteenDM_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredNineteenDM_199501 : Nat.Prime 199501 := by norm_num

private theorem prime_oneHundredNineteenDM_204947 : Nat.Prime 204947 := by norm_num

private theorem prime_oneHundredNineteenDM_229637 : Nat.Prime 229637 := by norm_num

private theorem prime_oneHundredNineteenDM_237019 : Nat.Prime 237019 := by norm_num

private theorem prime_oneHundredNineteenDM_245171 : Nat.Prime 245171 := by norm_num

private theorem prime_oneHundredNineteenDM_247519 : Nat.Prime 247519 := by norm_num

private theorem prime_oneHundredNineteenDM_249037 : Nat.Prime 249037 := by norm_num

private theorem prime_oneHundredNineteenDM_252533 : Nat.Prime 252533 := by norm_num

private theorem prime_oneHundredNineteenDM_271003 : Nat.Prime 271003 := by norm_num

private theorem prime_oneHundredNineteenDM_271163 : Nat.Prime 271163 := by norm_num

private theorem prime_oneHundredNineteenDM_296377 : Nat.Prime 296377 := by norm_num

private theorem prime_oneHundredNineteenDM_331871 : Nat.Prime 331871 := by norm_num

private theorem prime_oneHundredNineteenDM_335117 : Nat.Prime 335117 := by norm_num

private theorem prime_oneHundredNineteenDM_336031 : Nat.Prime 336031 := by norm_num

private theorem prime_oneHundredNineteenDM_346091 : Nat.Prime 346091 := by norm_num

private theorem prime_oneHundredNineteenDM_351653 : Nat.Prime 351653 := by norm_num

private theorem prime_oneHundredNineteenDM_357131 : Nat.Prime 357131 := by norm_num

private theorem prime_oneHundredNineteenDM_421847 : Nat.Prime 421847 := by norm_num

private theorem prime_oneHundredNineteenDM_434981 : Nat.Prime 434981 := by norm_num

private theorem prime_oneHundredNineteenDM_444523 : Nat.Prime 444523 := by norm_num

private theorem prime_oneHundredNineteenDM_450301 : Nat.Prime 450301 := by norm_num

private theorem prime_oneHundredNineteenDM_454159 : Nat.Prime 454159 := by norm_num

private theorem prime_oneHundredNineteenDM_518863 : Nat.Prime 518863 := by norm_num

private theorem prime_oneHundredNineteenDM_525871 : Nat.Prime 525871 := by norm_num

private theorem prime_oneHundredNineteenDM_526373 : Nat.Prime 526373 := by norm_num

private theorem prime_oneHundredNineteenDM_535219 : Nat.Prime 535219 := by norm_num

private theorem prime_oneHundredNineteenDM_543601 : Nat.Prime 543601 := by norm_num

private theorem prime_oneHundredNineteenDM_553481 : Nat.Prime 553481 := by norm_num

private theorem prime_oneHundredNineteenDM_575417 : Nat.Prime 575417 := by norm_num

private theorem prime_oneHundredNineteenDM_586067 : Nat.Prime 586067 := by norm_num

private theorem prime_oneHundredNineteenDM_596653 : Nat.Prime 596653 := by norm_num

private theorem prime_oneHundredNineteenDM_612643 : Nat.Prime 612643 := by norm_num

private theorem prime_oneHundredNineteenDM_614279 : Nat.Prime 614279 := by norm_num

private theorem prime_oneHundredNineteenDM_649217 : Nat.Prime 649217 := by norm_num

private theorem prime_oneHundredNineteenDM_649507 : Nat.Prime 649507 := by norm_num

private theorem prime_oneHundredNineteenDM_664211 : Nat.Prime 664211 := by norm_num

private theorem prime_oneHundredNineteenDM_723413 : Nat.Prime 723413 := by norm_num

private theorem prime_oneHundredNineteenDM_769007 : Nat.Prime 769007 := by norm_num

private theorem prime_oneHundredNineteenDM_799633 : Nat.Prime 799633 := by norm_num

private theorem prime_oneHundredNineteenDM_873113 : Nat.Prime 873113 := by norm_num

private theorem prime_oneHundredNineteenDM_910451 : Nat.Prime 910451 := by norm_num

private theorem prime_oneHundredNineteenDM_920273 : Nat.Prime 920273 := by norm_num

private theorem prime_oneHundredNineteenDM_998353 : Nat.Prime 998353 := by norm_num

private theorem prime_oneHundredNineteenDM_1023277 : Nat.Prime 1023277 := by norm_num

private theorem prime_oneHundredNineteenDM_1094963 : Nat.Prime 1094963 := by norm_num

private theorem prime_oneHundredNineteenDM_1119109 : Nat.Prime 1119109 := by norm_num

private theorem prime_oneHundredNineteenDM_1238771 : Nat.Prime 1238771 := by norm_num

private theorem prime_oneHundredNineteenDM_1258937 : Nat.Prime 1258937 := by norm_num

private theorem prime_oneHundredNineteenDM_1360213 : Nat.Prime 1360213 := by norm_num

private theorem prime_oneHundredNineteenDM_1409503 : Nat.Prime 1409503 := by norm_num

private theorem prime_oneHundredNineteenDM_1411411 : Nat.Prime 1411411 := by norm_num

private theorem prime_oneHundredNineteenDM_1457389 : Nat.Prime 1457389 := by norm_num

private theorem prime_oneHundredNineteenDM_1521103 : Nat.Prime 1521103 := by norm_num

private theorem prime_oneHundredNineteenDM_1557481 : Nat.Prime 1557481 := by norm_num

private theorem prime_oneHundredNineteenDM_1612823 : Nat.Prime 1612823 := by norm_num

private theorem prime_oneHundredNineteenDM_1618807 : Nat.Prime 1618807 := by norm_num

private theorem prime_oneHundredNineteenDM_1628171 : Nat.Prime 1628171 := by norm_num

private theorem prime_oneHundredNineteenDM_1708037 : Nat.Prime 1708037 := by norm_num

private theorem prime_oneHundredNineteenDM_1731209 : Nat.Prime 1731209 := by norm_num

private theorem prime_oneHundredNineteenDM_1736981 : Nat.Prime 1736981 := by norm_num

private theorem prime_oneHundredNineteenDM_2104961 : Nat.Prime 2104961 := by norm_num

private theorem prime_oneHundredNineteenDM_2126587 : Nat.Prime 2126587 := by norm_num

private theorem prime_oneHundredNineteenDM_2208071 : Nat.Prime 2208071 := by norm_num

private theorem prime_oneHundredNineteenDM_2300357 : Nat.Prime 2300357 := by norm_num

private theorem prime_oneHundredNineteenDM_2489909 : Nat.Prime 2489909 := by norm_num

private theorem prime_oneHundredNineteenDM_2537851 : Nat.Prime 2537851 := by norm_num

private theorem prime_oneHundredNineteenDM_2681267 : Nat.Prime 2681267 := by norm_num

private theorem prime_oneHundredNineteenDM_2709199 : Nat.Prime 2709199 := by norm_num

private theorem prime_oneHundredNineteenDM_2713783 : Nat.Prime 2713783 := by norm_num

private theorem prime_oneHundredNineteenDM_2714843 : Nat.Prime 2714843 := by norm_num

private theorem prime_oneHundredNineteenDM_2717291 : Nat.Prime 2717291 := by norm_num

private theorem prime_oneHundredNineteenDM_2723033 : Nat.Prime 2723033 := by norm_num

private theorem prime_oneHundredNineteenDM_2729093 : Nat.Prime 2729093 := by norm_num

private theorem prime_oneHundredNineteenDM_2777149 : Nat.Prime 2777149 := by norm_num

private theorem prime_oneHundredNineteenDM_2921617 : Nat.Prime 2921617 := by norm_num

private theorem prime_oneHundredNineteenDM_2930593 : Nat.Prime 2930593 := by norm_num

private theorem prime_oneHundredNineteenDM_2938073 : Nat.Prime 2938073 := by norm_num

private theorem prime_oneHundredNineteenDM_3022517 : Nat.Prime 3022517 := by norm_num

private theorem prime_oneHundredNineteenDM_3083581 : Nat.Prime 3083581 := by norm_num

private theorem prime_oneHundredNineteenDM_3148109 : Nat.Prime 3148109 := by norm_num

private theorem prime_oneHundredNineteenDM_3162499 : Nat.Prime 3162499 := by norm_num

private theorem prime_oneHundredNineteenDM_3600307 : Nat.Prime 3600307 := by norm_num

private theorem prime_oneHundredNineteenDM_3614497 : Nat.Prime 3614497 := by norm_num

private theorem prime_oneHundredNineteenDM_3677579 : Nat.Prime 3677579 := by norm_num

private theorem prime_oneHundredNineteenDM_4222007 : Nat.Prime 4222007 := by norm_num

private theorem prime_oneHundredNineteenDM_4264193 : Nat.Prime 4264193 := by norm_num

private theorem prime_oneHundredNineteenDM_4282273 : Nat.Prime 4282273 := by norm_num

private theorem prime_oneHundredNineteenDM_4444217 : Nat.Prime 4444217 := by norm_num

private theorem prime_oneHundredNineteenDM_4526593 : Nat.Prime 4526593 := by norm_num

private theorem prime_oneHundredNineteenDM_4625021 : Nat.Prime 4625021 := by norm_num

private theorem prime_oneHundredNineteenDM_4718083 : Nat.Prime 4718083 := by norm_num

private theorem prime_oneHundredNineteenDM_4778383 : Nat.Prime 4778383 := by norm_num

private theorem prime_oneHundredNineteenDM_5039227 : Nat.Prime 5039227 := by norm_num

private theorem prime_oneHundredNineteenDM_5556319 : Nat.Prime 5556319 := by norm_num

private theorem prime_oneHundredNineteenDM_5563069 : Nat.Prime 5563069 := by norm_num

private theorem prime_oneHundredNineteenDM_5722621 : Nat.Prime 5722621 := by norm_num

private theorem prime_oneHundredNineteenDM_6167303 : Nat.Prime 6167303 := by norm_num

private theorem prime_oneHundredNineteenDM_6314617 : Nat.Prime 6314617 := by norm_num

private theorem prime_oneHundredNineteenDM_6646427 : Nat.Prime 6646427 := by norm_num

private theorem prime_oneHundredNineteenDM_7089619 : Nat.Prime 7089619 := by norm_num

private theorem prime_oneHundredNineteenDM_7374659 : Nat.Prime 7374659 := by norm_num

private theorem prime_oneHundredNineteenDM_8913703 : Nat.Prime 8913703 := by norm_num

private theorem prime_oneHundredNineteenDM_10003657 : Nat.Prime 10003657 := by norm_num

private theorem prime_oneHundredNineteenDM_10369519 : Nat.Prime 10369519 := by norm_num

private theorem prime_oneHundredNineteenDM_10384169 : Nat.Prime 10384169 := by norm_num

private theorem prime_oneHundredNineteenDM_10763729 : Nat.Prime 10763729 := by norm_num

private theorem prime_oneHundredNineteenDM_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredNineteenDM_10914613 : Nat.Prime 10914613 := by norm_num

private theorem prime_oneHundredNineteenDM_11029679 : Nat.Prime 11029679 := by norm_num

private theorem prime_oneHundredNineteenDM_11183369 : Nat.Prime 11183369 := by norm_num

private theorem prime_oneHundredNineteenDM_11695939 : Nat.Prime 11695939 := by norm_num

private theorem prime_oneHundredNineteenDM_12391237 : Nat.Prime 12391237 := by norm_num

private theorem prime_oneHundredNineteenDM_12896381 : Nat.Prime 12896381 := by norm_num

private theorem prime_oneHundredNineteenDM_13453541 : Nat.Prime 13453541 := by norm_num

private theorem prime_oneHundredNineteenDM_14797247 : Nat.Prime 14797247 := by norm_num

private theorem prime_oneHundredNineteenDM_15944843 : Nat.Prime 15944843 := by norm_num

private theorem prime_oneHundredNineteenDM_16040611 : Nat.Prime 16040611 := by norm_num

private theorem prime_oneHundredNineteenDM_17147257 : Nat.Prime 17147257 := by norm_num

private theorem prime_oneHundredNineteenDM_17932279 : Nat.Prime 17932279 := by norm_num

private theorem prime_oneHundredNineteenDM_18243139 : Nat.Prime 18243139 := by norm_num

private theorem prime_oneHundredNineteenDM_18710819 : Nat.Prime 18710819 := by norm_num

private theorem prime_oneHundredNineteenDM_20133779 : Nat.Prime 20133779 := by norm_num

private theorem prime_oneHundredNineteenDM_20743897 : Nat.Prime 20743897 := by norm_num

private theorem prime_oneHundredNineteenDM_22375373 : Nat.Prime 22375373 := by norm_num

private theorem prime_oneHundredNineteenDM_24386939 : Nat.Prime 24386939 := by norm_num

private theorem prime_oneHundredNineteenDM_26066197 : Nat.Prime 26066197 := by norm_num

private theorem prime_oneHundredNineteenDM_26330281 : Nat.Prime 26330281 := by norm_num

private theorem prime_oneHundredNineteenDM_26493997 : Nat.Prime 26493997 := by norm_num

private theorem prime_oneHundredNineteenDM_27755393 : Nat.Prime 27755393 := by norm_num

private theorem prime_oneHundredNineteenDM_31432069 : Nat.Prime 31432069 := by
  apply lucas_primality 31432069 (2 : ZMod 31432069)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (873113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (873113, 1)] : List FactorBlock).map factorBlockValue).prod) = 31432069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_873113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 31432069) ^ 15716034 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 31432069) ^ 10477356 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 31432069) ^ 36 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_32701811 : Nat.Prime 32701811 := by
  apply lucas_primality 32701811 (2 : ZMod 32701811)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (73, 1), (44797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (73, 1), (44797, 1)] : List FactorBlock).map factorBlockValue).prod) = 32701811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_73
      · exact prime_oneHundredNineteenDM_44797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32701811) ^ 16350905 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 32701811) ^ 6540362 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 32701811) ^ 447970 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 32701811) ^ 730 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_34858727 : Nat.Prime 34858727 := by
  apply lucas_primality 34858727 (7 : ZMod 34858727)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2489909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2489909, 1)] : List FactorBlock).map factorBlockValue).prod) = 34858727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_2489909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 34858727) ^ 17429363 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 34858727) ^ 4979818 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 34858727) ^ 14 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_36456613 : Nat.Prime 36456613 := by
  apply lucas_primality 36456613 (6 : ZMod 36456613)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (107, 1), (28393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (107, 1), (28393, 1)] : List FactorBlock).map factorBlockValue).prod) = 36456613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_107
      · exact prime_oneHundredNineteenDM_28393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 36456613) ^ 18228306 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 36456613) ^ 12152204 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 36456613) ^ 340716 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 36456613) ^ 1284 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_37339933 : Nat.Prime 37339933 := by
  apply lucas_primality 37339933 (5 : ZMod 37339933)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (444523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (444523, 1)] : List FactorBlock).map factorBlockValue).prod) = 37339933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_444523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 37339933) ^ 18669966 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 37339933) ^ 12446644 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 37339933) ^ 5334276 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 37339933) ^ 84 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_39951599 : Nat.Prime 39951599 := by
  apply lucas_primality 39951599 (7 : ZMod 39951599)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (23, 1), (47, 1), (1087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (23, 1), (47, 1), (1087, 1)] : List FactorBlock).map factorBlockValue).prod) = 39951599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_17
      · exact prime_oneHundredNineteenDM_23
      · exact prime_oneHundredNineteenDM_47
      · exact prime_oneHundredNineteenDM_1087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 39951599) ^ 19975799 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 39951599) ^ 2350094 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 39951599) ^ 1737026 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 39951599) ^ 850034 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 39951599) ^ 36754 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_40497313 : Nat.Prime 40497313 := by
  apply lucas_primality 40497313 (5 : ZMod 40497313)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (421847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (421847, 1)] : List FactorBlock).map factorBlockValue).prod) = 40497313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_421847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 40497313) ^ 20248656 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 40497313) ^ 13499104 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 40497313) ^ 96 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_40674451 : Nat.Prime 40674451 := by
  apply lucas_primality 40674451 (2 : ZMod 40674451)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (271163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (271163, 1)] : List FactorBlock).map factorBlockValue).prod) = 40674451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_271163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40674451) ^ 20337225 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 40674451) ^ 13558150 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 40674451) ^ 8134890 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 40674451) ^ 150 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_41406427 : Nat.Prime 41406427 := by
  apply lucas_primality 41406427 (2 : ZMod 41406427)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (2300357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (2300357, 1)] : List FactorBlock).map factorBlockValue).prod) = 41406427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_2300357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 41406427) ^ 20703213 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 41406427) ^ 13802142 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 41406427) ^ 18 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_42099221 : Nat.Prime 42099221 := by
  apply lucas_primality 42099221 (2 : ZMod 42099221)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (2104961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (2104961, 1)] : List FactorBlock).map factorBlockValue).prod) = 42099221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_2104961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 42099221) ^ 21049610 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 42099221) ^ 8419844 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 42099221) ^ 20 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_45146593 : Nat.Prime 45146593 := by
  apply lucas_primality 45146593 (11 : ZMod 45146593)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (52253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (52253, 1)] : List FactorBlock).map factorBlockValue).prod) = 45146593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_52253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 45146593) ^ 22573296 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (11 : ZMod 45146593) ^ 15048864 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (11 : ZMod 45146593) ^ 864 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_47582281 : Nat.Prime 47582281 := by
  apply lucas_primality 47582281 (7 : ZMod 47582281)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (132173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (132173, 1)] : List FactorBlock).map factorBlockValue).prod) = 47582281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_132173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 47582281) ^ 23791140 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 47582281) ^ 15860760 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 47582281) ^ 9516456 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 47582281) ^ 360 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_47783831 : Nat.Prime 47783831 := by
  apply lucas_primality 47783831 (14 : ZMod 47783831)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (4778383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (4778383, 1)] : List FactorBlock).map factorBlockValue).prod) = 47783831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_4778383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (14 : ZMod 47783831) ^ 23891915 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (14 : ZMod 47783831) ^ 9556766 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (14 : ZMod 47783831) ^ 10 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_53990197 : Nat.Prime 53990197 := by
  apply lucas_primality 53990197 (5 : ZMod 53990197)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (346091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (346091, 1)] : List FactorBlock).map factorBlockValue).prod) = 53990197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_13
      · exact prime_oneHundredNineteenDM_346091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 53990197) ^ 26995098 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 53990197) ^ 17996732 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 53990197) ^ 4153092 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 53990197) ^ 156 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_55510787 : Nat.Prime 55510787 := by
  apply lucas_primality 55510787 (2 : ZMod 55510787)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (27755393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (27755393, 1)] : List FactorBlock).map factorBlockValue).prod) = 55510787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_27755393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 55510787) ^ 27755393 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 55510787) ^ 2 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_61239001 : Nat.Prime 61239001 := by
  apply lucas_primality 61239001 (17 : ZMod 61239001)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 3), (137, 1), (149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 3), (137, 1), (149, 1)] : List FactorBlock).map factorBlockValue).prod) = 61239001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_137
      · exact prime_oneHundredNineteenDM_149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 61239001) ^ 30619500 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (17 : ZMod 61239001) ^ 20413000 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (17 : ZMod 61239001) ^ 12247800 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (17 : ZMod 61239001) ^ 447000 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (17 : ZMod 61239001) ^ 411000 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_63853327 : Nat.Prime 63853327 := by
  apply lucas_primality 63853327 (3 : ZMod 63853327)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (17, 1), (69557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (17, 1), (69557, 1)] : List FactorBlock).map factorBlockValue).prod) = 63853327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_17
      · exact prime_oneHundredNineteenDM_69557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 63853327) ^ 31926663 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 63853327) ^ 21284442 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 63853327) ^ 3756078 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 63853327) ^ 918 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_64308691 : Nat.Prime 64308691 := by
  apply lucas_primality 64308691 (2 : ZMod 64308691)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (23, 1), (47, 1), (661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (23, 1), (47, 1), (661, 1)] : List FactorBlock).map factorBlockValue).prod) = 64308691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_23
      · exact prime_oneHundredNineteenDM_47
      · exact prime_oneHundredNineteenDM_661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 64308691) ^ 32154345 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 64308691) ^ 21436230 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 64308691) ^ 12861738 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 64308691) ^ 2796030 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 64308691) ^ 1368270 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 64308691) ^ 97290 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_65106751 : Nat.Prime 65106751 := by
  apply lucas_primality 65106751 (12 : ZMod 65106751)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (47, 1), (1847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (47, 1), (1847, 1)] : List FactorBlock).map factorBlockValue).prod) = 65106751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_47
      · exact prime_oneHundredNineteenDM_1847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 65106751) ^ 32553375 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (12 : ZMod 65106751) ^ 21702250 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (12 : ZMod 65106751) ^ 13021350 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (12 : ZMod 65106751) ^ 1385250 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (12 : ZMod 65106751) ^ 35250 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_66213193 : Nat.Prime 66213193 := by
  apply lucas_primality 66213193 (5 : ZMod 66213193)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (619, 1), (4457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (619, 1), (4457, 1)] : List FactorBlock).map factorBlockValue).prod) = 66213193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_619
      · exact prime_oneHundredNineteenDM_4457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 66213193) ^ 33106596 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 66213193) ^ 22071064 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 66213193) ^ 106968 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 66213193) ^ 14856 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_70676777 : Nat.Prime 70676777 := by
  apply lucas_primality 70676777 (3 : ZMod 70676777)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (521, 1), (547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (521, 1), (547, 1)] : List FactorBlock).map factorBlockValue).prod) = 70676777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_31
      · exact prime_oneHundredNineteenDM_521
      · exact prime_oneHundredNineteenDM_547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 70676777) ^ 35338388 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 70676777) ^ 2279896 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 70676777) ^ 135656 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 70676777) ^ 129208 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_73517161 : Nat.Prime 73517161 := by
  apply lucas_primality 73517161 (29 : ZMod 73517161)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (612643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (612643, 1)] : List FactorBlock).map factorBlockValue).prod) = 73517161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_612643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (29 : ZMod 73517161) ^ 36758580 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (29 : ZMod 73517161) ^ 24505720 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (29 : ZMod 73517161) ^ 14703432 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (29 : ZMod 73517161) ^ 120 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_78347011 : Nat.Prime 78347011 := by
  apply lucas_primality 78347011 (3 : ZMod 78347011)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (349, 1), (1069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (349, 1), (1069, 1)] : List FactorBlock).map factorBlockValue).prod) = 78347011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_349
      · exact prime_oneHundredNineteenDM_1069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 78347011) ^ 39173505 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 78347011) ^ 26115670 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 78347011) ^ 15669402 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 78347011) ^ 11192430 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 78347011) ^ 224490 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 78347011) ^ 73290 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_79903199 : Nat.Prime 79903199 := by
  apply lucas_primality 79903199 (17 : ZMod 79903199)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (39951599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (39951599, 1)] : List FactorBlock).map factorBlockValue).prod) = 79903199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_39951599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (17 : ZMod 79903199) ^ 39951599 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (17 : ZMod 79903199) ^ 2 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_90706087 : Nat.Prime 90706087 := by
  apply lucas_primality 90706087 (3 : ZMod 90706087)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5039227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5039227, 1)] : List FactorBlock).map factorBlockValue).prod) = 90706087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5039227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 90706087) ^ 45353043 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 90706087) ^ 30235362 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 90706087) ^ 18 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_93030139 : Nat.Prime 93030139 := by
  apply lucas_primality 93030139 (10 : ZMod 93030139)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (59, 1), (251, 1), (349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (59, 1), (251, 1), (349, 1)] : List FactorBlock).map factorBlockValue).prod) = 93030139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_59
      · exact prime_oneHundredNineteenDM_251
      · exact prime_oneHundredNineteenDM_349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 93030139) ^ 46515069 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (10 : ZMod 93030139) ^ 31010046 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (10 : ZMod 93030139) ^ 1576782 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (10 : ZMod 93030139) ^ 370638 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (10 : ZMod 93030139) ^ 266562 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_95757499 : Nat.Prime 95757499 := by
  apply lucas_primality 95757499 (10 : ZMod 95757499)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (17, 1), (104311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (17, 1), (104311, 1)] : List FactorBlock).map factorBlockValue).prod) = 95757499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_17
      · exact prime_oneHundredNineteenDM_104311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 95757499) ^ 47878749 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (10 : ZMod 95757499) ^ 31919166 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (10 : ZMod 95757499) ^ 5632794 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (10 : ZMod 95757499) ^ 918 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_98038253 : Nat.Prime 98038253 := by
  apply lucas_primality 98038253 (2 : ZMod 98038253)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 2), (17, 1), (19, 1), (449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 2), (17, 1), (19, 1), (449, 1)] : List FactorBlock).map factorBlockValue).prod) = 98038253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_13
      · exact prime_oneHundredNineteenDM_17
      · exact prime_oneHundredNineteenDM_19
      · exact prime_oneHundredNineteenDM_449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 98038253) ^ 49019126 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 98038253) ^ 7541404 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 98038253) ^ 5766956 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 98038253) ^ 5159908 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 98038253) ^ 218348 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_99456199 : Nat.Prime 99456199 := by
  apply lucas_primality 99456199 (3 : ZMod 99456199)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (421, 1), (39373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (421, 1), (39373, 1)] : List FactorBlock).map factorBlockValue).prod) = 99456199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_421
      · exact prime_oneHundredNineteenDM_39373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 99456199) ^ 49728099 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 99456199) ^ 33152066 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 99456199) ^ 236238 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 99456199) ^ 2526 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_104264789 : Nat.Prime 104264789 := by
  apply lucas_primality 104264789 (2 : ZMod 104264789)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (26066197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (26066197, 1)] : List FactorBlock).map factorBlockValue).prod) = 104264789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_26066197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 104264789) ^ 52132394 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 104264789) ^ 4 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_107999813 : Nat.Prime 107999813 := by
  apply lucas_primality 107999813 (2 : ZMod 107999813)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (241, 1), (4871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (241, 1), (4871, 1)] : List FactorBlock).map factorBlockValue).prod) = 107999813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_23
      · exact prime_oneHundredNineteenDM_241
      · exact prime_oneHundredNineteenDM_4871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 107999813) ^ 53999906 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 107999813) ^ 4695644 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 107999813) ^ 448132 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 107999813) ^ 22172 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_119460673 : Nat.Prime 119460673 := by
  apply lucas_primality 119460673 (5 : ZMod 119460673)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (157, 1), (1321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (157, 1), (1321, 1)] : List FactorBlock).map factorBlockValue).prod) = 119460673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_157
      · exact prime_oneHundredNineteenDM_1321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 119460673) ^ 59730336 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 119460673) ^ 39820224 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 119460673) ^ 760896 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 119460673) ^ 90432 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_121364741 : Nat.Prime 121364741 := by
  apply lucas_primality 121364741 (2 : ZMod 121364741)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (151, 1), (5741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (151, 1), (5741, 1)] : List FactorBlock).map factorBlockValue).prod) = 121364741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_151
      · exact prime_oneHundredNineteenDM_5741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 121364741) ^ 60682370 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 121364741) ^ 24272948 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 121364741) ^ 17337820 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 121364741) ^ 803740 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 121364741) ^ 21140 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_122169367 : Nat.Prime 122169367 := by
  apply lucas_primality 122169367 (5 : ZMod 122169367)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (97, 1), (6361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (97, 1), (6361, 1)] : List FactorBlock).map factorBlockValue).prod) = 122169367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_11
      · exact prime_oneHundredNineteenDM_97
      · exact prime_oneHundredNineteenDM_6361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 122169367) ^ 61084683 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 122169367) ^ 40723122 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 122169367) ^ 11106306 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 122169367) ^ 1259478 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 122169367) ^ 19206 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_133513657 : Nat.Prime 133513657 := by
  apply lucas_primality 133513657 (5 : ZMod 133513657)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5563069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5563069, 1)] : List FactorBlock).map factorBlockValue).prod) = 133513657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5563069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 133513657) ^ 66756828 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 133513657) ^ 44504552 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 133513657) ^ 24 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_140647657 : Nat.Prime 140647657 := by
  apply lucas_primality 140647657 (5 : ZMod 140647657)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (37, 1), (149, 1), (1063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (37, 1), (149, 1), (1063, 1)] : List FactorBlock).map factorBlockValue).prod) = 140647657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_37
      · exact prime_oneHundredNineteenDM_149
      · exact prime_oneHundredNineteenDM_1063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 140647657) ^ 70323828 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 140647657) ^ 46882552 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 140647657) ^ 3801288 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 140647657) ^ 943944 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 140647657) ^ 132312 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_146938921 : Nat.Prime 146938921 := by
  apply lucas_primality 146938921 (7 : ZMod 146938921)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (47, 1), (26053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (47, 1), (26053, 1)] : List FactorBlock).map factorBlockValue).prod) = 146938921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_47
      · exact prime_oneHundredNineteenDM_26053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 146938921) ^ 73469460 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 146938921) ^ 48979640 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 146938921) ^ 29387784 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 146938921) ^ 3126360 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 146938921) ^ 5640 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_147454477 : Nat.Prime 147454477 := by
  apply lucas_primality 147454477 (2 : ZMod 147454477)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (31, 1), (30491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (31, 1), (30491, 1)] : List FactorBlock).map factorBlockValue).prod) = 147454477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_13
      · exact prime_oneHundredNineteenDM_31
      · exact prime_oneHundredNineteenDM_30491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 147454477) ^ 73727238 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 147454477) ^ 49151492 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 147454477) ^ 11342652 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 147454477) ^ 4756596 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 147454477) ^ 4836 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_150670193 : Nat.Prime 150670193 := by
  apply lucas_primality 150670193 (3 : ZMod 150670193)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (181, 1), (52027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (181, 1), (52027, 1)] : List FactorBlock).map factorBlockValue).prod) = 150670193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_181
      · exact prime_oneHundredNineteenDM_52027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 150670193) ^ 75335096 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 150670193) ^ 832432 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 150670193) ^ 2896 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_151195171 : Nat.Prime 151195171 := by
  apply lucas_primality 151195171 (2 : ZMod 151195171)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (59, 1), (12203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (59, 1), (12203, 1)] : List FactorBlock).map factorBlockValue).prod) = 151195171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_59
      · exact prime_oneHundredNineteenDM_12203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 151195171) ^ 75597585 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 151195171) ^ 50398390 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 151195171) ^ 30239034 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 151195171) ^ 21599310 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 151195171) ^ 2562630 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 151195171) ^ 12390 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_178763147 : Nat.Prime 178763147 := by
  apply lucas_primality 178763147 (2 : ZMod 178763147)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (167, 1), (535219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (167, 1), (535219, 1)] : List FactorBlock).map factorBlockValue).prod) = 178763147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_167
      · exact prime_oneHundredNineteenDM_535219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 178763147) ^ 89381573 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 178763147) ^ 1070438 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 178763147) ^ 334 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_212514941 : Nat.Prime 212514941 := by
  apply lucas_primality 212514941 (2 : ZMod 212514941)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (23, 1), (41999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (23, 1), (41999, 1)] : List FactorBlock).map factorBlockValue).prod) = 212514941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_11
      · exact prime_oneHundredNineteenDM_23
      · exact prime_oneHundredNineteenDM_41999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 212514941) ^ 106257470 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 212514941) ^ 42502988 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 212514941) ^ 19319540 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 212514941) ^ 9239780 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 212514941) ^ 5060 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_218739679 : Nat.Prime 218739679 := by
  apply lucas_primality 218739679 (6 : ZMod 218739679)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (36456613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (36456613, 1)] : List FactorBlock).map factorBlockValue).prod) = 218739679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_36456613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 218739679) ^ 109369839 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 218739679) ^ 72913226 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 218739679) ^ 6 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_228519589 : Nat.Prime 228519589 := by
  apply lucas_primality 228519589 (2 : ZMod 228519589)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (1731209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (1731209, 1)] : List FactorBlock).map factorBlockValue).prod) = 228519589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_11
      · exact prime_oneHundredNineteenDM_1731209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 228519589) ^ 114259794 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 228519589) ^ 76173196 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 228519589) ^ 20774508 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 228519589) ^ 132 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_238957073 : Nat.Prime 238957073 := by
  apply lucas_primality 238957073 (3 : ZMod 238957073)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (19, 1), (53, 1), (14831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (19, 1), (53, 1), (14831, 1)] : List FactorBlock).map factorBlockValue).prod) = 238957073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_19
      · exact prime_oneHundredNineteenDM_53
      · exact prime_oneHundredNineteenDM_14831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 238957073) ^ 119478536 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 238957073) ^ 12576688 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 238957073) ^ 4508624 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 238957073) ^ 16112 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_262224407 : Nat.Prime 262224407 := by
  apply lucas_primality 262224407 (5 : ZMod 262224407)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (809, 1), (3769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (809, 1), (3769, 1)] : List FactorBlock).map factorBlockValue).prod) = 262224407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_43
      · exact prime_oneHundredNineteenDM_809
      · exact prime_oneHundredNineteenDM_3769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 262224407) ^ 131112203 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 262224407) ^ 6098242 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 262224407) ^ 324134 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 262224407) ^ 69574 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_273126599 : Nat.Prime 273126599 := by
  apply lucas_primality 273126599 (7 : ZMod 273126599)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (10853, 1), (12583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (10853, 1), (12583, 1)] : List FactorBlock).map factorBlockValue).prod) = 273126599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_10853
      · exact prime_oneHundredNineteenDM_12583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 273126599) ^ 136563299 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 273126599) ^ 25166 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 273126599) ^ 21706 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_311908379 : Nat.Prime 311908379 := by
  apply lucas_primality 311908379 (2 : ZMod 311908379)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3617, 1), (43117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3617, 1), (43117, 1)] : List FactorBlock).map factorBlockValue).prod) = 311908379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3617
      · exact prime_oneHundredNineteenDM_43117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 311908379) ^ 155954189 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 311908379) ^ 86234 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 311908379) ^ 7234 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_322911871 : Nat.Prime 322911871 := by
  apply lucas_primality 322911871 (3 : ZMod 322911871)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (10763729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (10763729, 1)] : List FactorBlock).map factorBlockValue).prod) = 322911871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_10763729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 322911871) ^ 161455935 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 322911871) ^ 107637290 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 322911871) ^ 64582374 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 322911871) ^ 30 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_352065557 : Nat.Prime 352065557 := by
  apply lucas_primality 352065557 (2 : ZMod 352065557)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (359, 1), (245171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (359, 1), (245171, 1)] : List FactorBlock).map factorBlockValue).prod) = 352065557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_359
      · exact prime_oneHundredNineteenDM_245171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 352065557) ^ 176032778 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 352065557) ^ 980684 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 352065557) ^ 1436 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_356538293 : Nat.Prime 356538293 := by
  apply lucas_primality 356538293 (2 : ZMod 356538293)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (241, 1), (33623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (241, 1), (33623, 1)] : List FactorBlock).map factorBlockValue).prod) = 356538293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_11
      · exact prime_oneHundredNineteenDM_241
      · exact prime_oneHundredNineteenDM_33623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 356538293) ^ 178269146 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 356538293) ^ 32412572 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 356538293) ^ 1479412 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 356538293) ^ 10604 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_361103651 : Nat.Prime 361103651 := by
  apply lucas_primality 361103651 (2 : ZMod 361103651)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (29, 1), (249037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (29, 1), (249037, 1)] : List FactorBlock).map factorBlockValue).prod) = 361103651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_29
      · exact prime_oneHundredNineteenDM_249037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 361103651) ^ 180551825 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 361103651) ^ 72220730 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 361103651) ^ 12451850 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 361103651) ^ 1450 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_383119963 : Nat.Prime 383119963 := by
  apply lucas_primality 383119963 (2 : ZMod 383119963)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (63853327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (63853327, 1)] : List FactorBlock).map factorBlockValue).prod) = 383119963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_63853327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 383119963) ^ 191559981 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 383119963) ^ 127706654 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 383119963) ^ 6 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_387825637 : Nat.Prime 387825637 := by
  apply lucas_primality 387825637 (7 : ZMod 387825637)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (2938073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (2938073, 1)] : List FactorBlock).map factorBlockValue).prod) = 387825637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_11
      · exact prime_oneHundredNineteenDM_2938073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 387825637) ^ 193912818 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 387825637) ^ 129275212 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 387825637) ^ 35256876 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 387825637) ^ 132 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_405312673 : Nat.Prime 405312673 := by
  apply lucas_primality 405312673 (5 : ZMod 405312673)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (4222007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (4222007, 1)] : List FactorBlock).map factorBlockValue).prod) = 405312673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_4222007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 405312673) ^ 202656336 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 405312673) ^ 135104224 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 405312673) ^ 96 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_413901017 : Nat.Prime 413901017 := by
  apply lucas_primality 413901017 (3 : ZMod 413901017)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (2723033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (2723033, 1)] : List FactorBlock).map factorBlockValue).prod) = 413901017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_19
      · exact prime_oneHundredNineteenDM_2723033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 413901017) ^ 206950508 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 413901017) ^ 21784264 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 413901017) ^ 152 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_440482171 : Nat.Prime 440482171 := by
  apply lucas_primality 440482171 (2 : ZMod 440482171)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (631, 1), (23269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (631, 1), (23269, 1)] : List FactorBlock).map factorBlockValue).prod) = 440482171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_631
      · exact prime_oneHundredNineteenDM_23269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 440482171) ^ 220241085 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 440482171) ^ 146827390 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 440482171) ^ 88096434 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 440482171) ^ 698070 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 440482171) ^ 18930 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_446364439 : Nat.Prime 446364439 := by
  apply lucas_primality 446364439 (12 : ZMod 446364439)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (5722621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (5722621, 1)] : List FactorBlock).map factorBlockValue).prod) = 446364439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_13
      · exact prime_oneHundredNineteenDM_5722621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (12 : ZMod 446364439) ^ 223182219 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (12 : ZMod 446364439) ^ 148788146 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (12 : ZMod 446364439) ^ 34335726 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (12 : ZMod 446364439) ^ 78 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_524485651 : Nat.Prime 524485651 := by
  apply lucas_primality 524485651 (2 : ZMod 524485651)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (13, 1), (277, 1), (971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (13, 1), (277, 1), (971, 1)] : List FactorBlock).map factorBlockValue).prod) = 524485651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_13
      · exact prime_oneHundredNineteenDM_277
      · exact prime_oneHundredNineteenDM_971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 524485651) ^ 262242825 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 524485651) ^ 174828550 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 524485651) ^ 104897130 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 524485651) ^ 40345050 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 524485651) ^ 1893450 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 524485651) ^ 540150 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_541996177 : Nat.Prime 541996177 := by
  apply lucas_primality 541996177 (5 : ZMod 541996177)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (17, 1), (664211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (17, 1), (664211, 1)] : List FactorBlock).map factorBlockValue).prod) = 541996177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_17
      · exact prime_oneHundredNineteenDM_664211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 541996177) ^ 270998088 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 541996177) ^ 180665392 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 541996177) ^ 31882128 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 541996177) ^ 816 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_597438929 : Nat.Prime 597438929 := by
  apply lucas_primality 597438929 (3 : ZMod 597438929)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (37339933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (37339933, 1)] : List FactorBlock).map factorBlockValue).prod) = 597438929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_37339933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 597438929) ^ 298719464 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 597438929) ^ 16 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_613982357 : Nat.Prime 613982357 := by
  apply lucas_primality 613982357 (2 : ZMod 613982357)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (449, 1), (26297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (449, 1), (26297, 1)] : List FactorBlock).map factorBlockValue).prod) = 613982357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_13
      · exact prime_oneHundredNineteenDM_449
      · exact prime_oneHundredNineteenDM_26297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 613982357) ^ 306991178 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 613982357) ^ 47229412 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 613982357) ^ 1367444 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 613982357) ^ 23348 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_657366109 : Nat.Prime 657366109 := by
  apply lucas_primality 657366109 (10 : ZMod 657366109)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (167, 1), (46861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (167, 1), (46861, 1)] : List FactorBlock).map factorBlockValue).prod) = 657366109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_167
      · exact prime_oneHundredNineteenDM_46861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 657366109) ^ 328683054 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (10 : ZMod 657366109) ^ 219122036 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (10 : ZMod 657366109) ^ 93909444 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (10 : ZMod 657366109) ^ 3936324 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (10 : ZMod 657366109) ^ 14028 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_674949883 : Nat.Prime 674949883 := by
  apply lucas_primality 674949883 (11 : ZMod 674949883)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (127, 1), (46619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (127, 1), (46619, 1)] : List FactorBlock).map factorBlockValue).prod) = 674949883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_19
      · exact prime_oneHundredNineteenDM_127
      · exact prime_oneHundredNineteenDM_46619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 674949883) ^ 337474941 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (11 : ZMod 674949883) ^ 224983294 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (11 : ZMod 674949883) ^ 35523678 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (11 : ZMod 674949883) ^ 5314566 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (11 : ZMod 674949883) ^ 14478 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_689068049 : Nat.Prime 689068049 := by
  apply lucas_primality 689068049 (3 : ZMod 689068049)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (727, 1), (59239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (727, 1), (59239, 1)] : List FactorBlock).map factorBlockValue).prod) = 689068049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_727
      · exact prime_oneHundredNineteenDM_59239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 689068049) ^ 344534024 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 689068049) ^ 947824 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 689068049) ^ 11632 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_713076587 : Nat.Prime 713076587 := by
  apply lucas_primality 713076587 (2 : ZMod 713076587)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (356538293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (356538293, 1)] : List FactorBlock).map factorBlockValue).prod) = 713076587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_356538293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 713076587) ^ 356538293 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 713076587) ^ 2 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_17203
      · exact prime_oneHundredNineteenDM_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_732506743 : Nat.Prime 732506743 := by
  apply lucas_primality 732506743 (19 : ZMod 732506743)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (101, 1), (36629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (101, 1), (36629, 1)] : List FactorBlock).map factorBlockValue).prod) = 732506743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_11
      · exact prime_oneHundredNineteenDM_101
      · exact prime_oneHundredNineteenDM_36629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 732506743) ^ 366253371 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (19 : ZMod 732506743) ^ 244168914 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (19 : ZMod 732506743) ^ 66591522 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (19 : ZMod 732506743) ^ 7252542 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (19 : ZMod 732506743) ^ 19998 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_740848501 : Nat.Prime 740848501 := by
  apply lucas_primality 740848501 (6 : ZMod 740848501)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 3), (7, 1), (29, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 3), (7, 1), (29, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) = 740848501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_29
      · exact prime_oneHundredNineteenDM_811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 740848501) ^ 370424250 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 740848501) ^ 246949500 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 740848501) ^ 148169700 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 740848501) ^ 105835500 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 740848501) ^ 25546500 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 740848501) ^ 913500 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_774734657 : Nat.Prime 774734657 := by
  apply lucas_primality 774734657 (3 : ZMod 774734657)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (227, 1), (53327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (227, 1), (53327, 1)] : List FactorBlock).map factorBlockValue).prod) = 774734657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_227
      · exact prime_oneHundredNineteenDM_53327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 774734657) ^ 387367328 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 774734657) ^ 3412928 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 774734657) ^ 14528 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_795189341 : Nat.Prime 795189341 := by
  apply lucas_primality 795189341 (2 : ZMod 795189341)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (3614497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (3614497, 1)] : List FactorBlock).map factorBlockValue).prod) = 795189341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_11
      · exact prime_oneHundredNineteenDM_3614497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 795189341) ^ 397594670 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 795189341) ^ 159037868 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 795189341) ^ 72289940 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 795189341) ^ 220 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_810301391 : Nat.Prime 810301391 := by
  apply lucas_primality 810301391 (7 : ZMod 810301391)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (89, 1), (910451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (89, 1), (910451, 1)] : List FactorBlock).map factorBlockValue).prod) = 810301391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_89
      · exact prime_oneHundredNineteenDM_910451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 810301391) ^ 405150695 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 810301391) ^ 162060278 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 810301391) ^ 9104510 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 810301391) ^ 890 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_935540951 : Nat.Prime 935540951 := by
  apply lucas_primality 935540951 (7 : ZMod 935540951)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (18710819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (18710819, 1)] : List FactorBlock).map factorBlockValue).prod) = 935540951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_18710819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 935540951) ^ 467770475 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 935540951) ^ 187108190 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 935540951) ^ 50 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_987817013 : Nat.Prime 987817013 := by
  apply lucas_primality 987817013 (2 : ZMod 987817013)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (13, 1), (2713783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (13, 1), (2713783, 1)] : List FactorBlock).map factorBlockValue).prod) = 987817013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_13
      · exact prime_oneHundredNineteenDM_2713783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 987817013) ^ 493908506 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 987817013) ^ 141116716 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 987817013) ^ 75985924 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 987817013) ^ 364 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_1057690939 : Nat.Prime 1057690939 := by
  apply lucas_primality 1057690939 (2 : ZMod 1057690939)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (10369519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (10369519, 1)] : List FactorBlock).map factorBlockValue).prod) = 1057690939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_17
      · exact prime_oneHundredNineteenDM_10369519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1057690939) ^ 528845469 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1057690939) ^ 352563646 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1057690939) ^ 62217114 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1057690939) ^ 102 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_1083280327 : Nat.Prime 1083280327 := by
  apply lucas_primality 1083280327 (3 : ZMod 1083280327)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (29, 2), (11299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (29, 2), (11299, 1)] : List FactorBlock).map factorBlockValue).prod) = 1083280327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_19
      · exact prime_oneHundredNineteenDM_29
      · exact prime_oneHundredNineteenDM_11299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1083280327) ^ 541640163 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1083280327) ^ 361093442 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1083280327) ^ 57014754 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1083280327) ^ 37354494 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1083280327) ^ 95874 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_1200946841 : Nat.Prime 1200946841 := by
  apply lucas_primality 1200946841 (7 : ZMod 1200946841)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (23, 1), (29, 1), (45013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (23, 1), (29, 1), (45013, 1)] : List FactorBlock).map factorBlockValue).prod) = 1200946841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_23
      · exact prime_oneHundredNineteenDM_29
      · exact prime_oneHundredNineteenDM_45013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1200946841) ^ 600473420 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1200946841) ^ 240189368 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1200946841) ^ 52215080 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1200946841) ^ 41411960 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1200946841) ^ 26680 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_1378136099 : Nat.Prime 1378136099 := by
  apply lucas_primality 1378136099 (2 : ZMod 1378136099)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (689068049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (689068049, 1)] : List FactorBlock).map factorBlockValue).prod) = 1378136099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_689068049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1378136099) ^ 689068049 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1378136099) ^ 2 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_1433514931 : Nat.Prime 1433514931 := by
  apply lucas_primality 1433514931 (7 : ZMod 1433514931)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (47783831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (47783831, 1)] : List FactorBlock).map factorBlockValue).prod) = 1433514931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_47783831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1433514931) ^ 716757465 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1433514931) ^ 477838310 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1433514931) ^ 286702986 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1433514931) ^ 30 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_1871081903 : Nat.Prime 1871081903 := by
  apply lucas_primality 1871081903 (5 : ZMod 1871081903)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (935540951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (935540951, 1)] : List FactorBlock).map factorBlockValue).prod) = 1871081903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_935540951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1871081903) ^ 935540951 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1871081903) ^ 2 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_1954012253 : Nat.Prime 1954012253 := by
  apply lucas_primality 1954012253 (2 : ZMod 1954012253)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (9857, 1), (49559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (9857, 1), (49559, 1)] : List FactorBlock).map factorBlockValue).prod) = 1954012253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_9857
      · exact prime_oneHundredNineteenDM_49559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1954012253) ^ 977006126 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1954012253) ^ 198236 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1954012253) ^ 39428 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_2091807901 : Nat.Prime 2091807901 := by
  apply lucas_primality 2091807901 (11 : ZMod 2091807901)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (7, 1), (13, 1), (25541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (7, 1), (13, 1), (25541, 1)] : List FactorBlock).map factorBlockValue).prod) = 2091807901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_13
      · exact prime_oneHundredNineteenDM_25541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2091807901) ^ 1045903950 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (11 : ZMod 2091807901) ^ 697269300 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (11 : ZMod 2091807901) ^ 418361580 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (11 : ZMod 2091807901) ^ 298829700 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (11 : ZMod 2091807901) ^ 160908300 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (11 : ZMod 2091807901) ^ 81900 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_2201703901 : Nat.Prime 2201703901 := by
  apply lucas_primality 2201703901 (7 : ZMod 2201703901)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (11, 2), (131, 1), (463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (11, 2), (131, 1), (463, 1)] : List FactorBlock).map factorBlockValue).prod) = 2201703901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_11
      · exact prime_oneHundredNineteenDM_131
      · exact prime_oneHundredNineteenDM_463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2201703901) ^ 1100851950 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 2201703901) ^ 733901300 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 2201703901) ^ 440340780 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 2201703901) ^ 200154900 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 2201703901) ^ 16806900 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 2201703901) ^ 4755300 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_2224815731 : Nat.Prime 2224815731 := by
  apply lucas_primality 2224815731 (2 : ZMod 2224815731)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (881, 1), (252533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (881, 1), (252533, 1)] : List FactorBlock).map factorBlockValue).prod) = 2224815731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_881
      · exact prime_oneHundredNineteenDM_252533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2224815731) ^ 1112407865 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2224815731) ^ 444963146 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2224815731) ^ 2525330 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2224815731) ^ 8810 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_2338689173 : Nat.Prime 2338689173 := by
  apply lucas_primality 2338689173 (2 : ZMod 2338689173)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (6653, 1), (87881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (6653, 1), (87881, 1)] : List FactorBlock).map factorBlockValue).prod) = 2338689173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_6653
      · exact prime_oneHundredNineteenDM_87881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2338689173) ^ 1169344586 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2338689173) ^ 351524 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2338689173) ^ 26612 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_2431500893 : Nat.Prime 2431500893 := by
  apply lucas_primality 2431500893 (2 : ZMod 2431500893)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7867, 1), (77269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7867, 1), (77269, 1)] : List FactorBlock).map factorBlockValue).prod) = 2431500893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_7867
      · exact prime_oneHundredNineteenDM_77269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2431500893) ^ 1215750446 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2431500893) ^ 309076 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2431500893) ^ 31468 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_2699799533 : Nat.Prime 2699799533 := by
  apply lucas_primality 2699799533 (2 : ZMod 2699799533)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (674949883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (674949883, 1)] : List FactorBlock).map factorBlockValue).prod) = 2699799533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_674949883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 2699799533) ^ 1349899766 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2699799533) ^ 4 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_2842933297 : Nat.Prime 2842933297 := by
  apply lucas_primality 2842933297 (5 : ZMod 2842933297)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (619, 1), (13669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (619, 1), (13669, 1)] : List FactorBlock).map factorBlockValue).prod) = 2842933297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_619
      · exact prime_oneHundredNineteenDM_13669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2842933297) ^ 1421466648 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 2842933297) ^ 947644432 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 2842933297) ^ 406133328 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 2842933297) ^ 4592784 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 2842933297) ^ 207984 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_2862326239 : Nat.Prime 2862326239 := by
  apply lucas_primality 2862326239 (3 : ZMod 2862326239)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5573, 1), (85601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5573, 1), (85601, 1)] : List FactorBlock).map factorBlockValue).prod) = 2862326239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5573
      · exact prime_oneHundredNineteenDM_85601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2862326239) ^ 1431163119 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2862326239) ^ 954108746 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2862326239) ^ 513606 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2862326239) ^ 33438 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_3091855847 : Nat.Prime 3091855847 := by
  apply lucas_primality 3091855847 (5 : ZMod 3091855847)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2591, 1), (596653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2591, 1), (596653, 1)] : List FactorBlock).map factorBlockValue).prod) = 3091855847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_2591
      · exact prime_oneHundredNineteenDM_596653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3091855847) ^ 1545927923 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 3091855847) ^ 1193306 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 3091855847) ^ 5182 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_3146913907 : Nat.Prime 3146913907 := by
  apply lucas_primality 3146913907 (3 : ZMod 3146913907)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (524485651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (524485651, 1)] : List FactorBlock).map factorBlockValue).prod) = 3146913907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_524485651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3146913907) ^ 1573456953 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 3146913907) ^ 1048971302 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 3146913907) ^ 6 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_3378878819 : Nat.Prime 3378878819 := by
  apply lucas_primality 3378878819 (2 : ZMod 3378878819)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1051, 1), (229637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1051, 1), (229637, 1)] : List FactorBlock).map factorBlockValue).prod) = 3378878819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_1051
      · exact prime_oneHundredNineteenDM_229637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3378878819) ^ 1689439409 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3378878819) ^ 482696974 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3378878819) ^ 3214918 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3378878819) ^ 14714 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_3835353553 : Nat.Prime 3835353553 := by
  apply lucas_primality 3835353553 (5 : ZMod 3835353553)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (79903199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (79903199, 1)] : List FactorBlock).map factorBlockValue).prod) = 3835353553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_79903199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3835353553) ^ 1917676776 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 3835353553) ^ 1278451184 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 3835353553) ^ 48 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_4041774067 : Nat.Prime 4041774067 := by
  apply lucas_primality 4041774067 (2 : ZMod 4041774067)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (61239001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (61239001, 1)] : List FactorBlock).map factorBlockValue).prod) = 4041774067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_11
      · exact prime_oneHundredNineteenDM_61239001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4041774067) ^ 2020887033 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4041774067) ^ 1347258022 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4041774067) ^ 367434006 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4041774067) ^ 66 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_4053126731 : Nat.Prime 4053126731 := by
  apply lucas_primality 4053126731 (2 : ZMod 4053126731)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (405312673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (405312673, 1)] : List FactorBlock).map factorBlockValue).prod) = 4053126731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_405312673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4053126731) ^ 2026563365 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4053126731) ^ 810625346 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4053126731) ^ 10 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_4952692709 : Nat.Prime 4952692709 := by
  apply lucas_primality 4952692709 (2 : ZMod 4952692709)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3467, 1), (357131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3467, 1), (357131, 1)] : List FactorBlock).map factorBlockValue).prod) = 4952692709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3467
      · exact prime_oneHundredNineteenDM_357131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4952692709) ^ 2476346354 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4952692709) ^ 1428524 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4952692709) ^ 13868 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_5126804671 : Nat.Prime 5126804671 := by
  apply lucas_primality 5126804671 (7 : ZMod 5126804671)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (1823, 1), (7211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (1823, 1), (7211, 1)] : List FactorBlock).map factorBlockValue).prod) = 5126804671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_13
      · exact prime_oneHundredNineteenDM_1823
      · exact prime_oneHundredNineteenDM_7211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 5126804671) ^ 2563402335 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 5126804671) ^ 1708934890 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 5126804671) ^ 1025360934 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 5126804671) ^ 394369590 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 5126804671) ^ 2812290 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 5126804671) ^ 710970 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_5161889773 : Nat.Prime 5161889773 := by
  apply lucas_primality 5161889773 (5 : ZMod 5161889773)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (11029679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (11029679, 1)] : List FactorBlock).map factorBlockValue).prod) = 5161889773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_13
      · exact prime_oneHundredNineteenDM_11029679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 5161889773) ^ 2580944886 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 5161889773) ^ 1720629924 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 5161889773) ^ 397068444 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 5161889773) ^ 468 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_5244488141 : Nat.Prime 5244488141 := by
  apply lucas_primality 5244488141 (2 : ZMod 5244488141)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (262224407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (262224407, 1)] : List FactorBlock).map factorBlockValue).prod) = 5244488141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_262224407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5244488141) ^ 2622244070 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 5244488141) ^ 1048897628 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 5244488141) ^ 20 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_31
      · exact prime_oneHundredNineteenDM_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_6117141491 : Nat.Prime 6117141491 := by
  apply lucas_primality 6117141491 (2 : ZMod 6117141491)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (331, 1), (1321, 1), (1399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (331, 1), (1321, 1), (1399, 1)] : List FactorBlock).map factorBlockValue).prod) = 6117141491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_331
      · exact prime_oneHundredNineteenDM_1321
      · exact prime_oneHundredNineteenDM_1399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6117141491) ^ 3058570745 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 6117141491) ^ 1223428298 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 6117141491) ^ 18480790 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 6117141491) ^ 4630690 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 6117141491) ^ 4372510 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_6393737663 : Nat.Prime 6393737663 := by
  apply lucas_primality 6393737663 (5 : ZMod 6393737663)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (23, 1), (31, 1), (311, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (23, 1), (31, 1), (311, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) = 6393737663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_13
      · exact prime_oneHundredNineteenDM_23
      · exact prime_oneHundredNineteenDM_31
      · exact prime_oneHundredNineteenDM_311
      · exact prime_oneHundredNineteenDM_1109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6393737663) ^ 3196868831 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 491825974 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 277988594 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 206249602 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 20558642 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 5765318 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_6757757639 : Nat.Prime 6757757639 := by
  apply lucas_primality 6757757639 (23 : ZMod 6757757639)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3378878819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3378878819, 1)] : List FactorBlock).map factorBlockValue).prod) = 6757757639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3378878819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (23 : ZMod 6757757639) ^ 3378878819 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (23 : ZMod 6757757639) ^ 2 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_6873567479 : Nat.Prime 6873567479 := by
  apply lucas_primality 6873567479 (7 : ZMod 6873567479)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (83, 1), (1119109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (83, 1), (1119109, 1)] : List FactorBlock).map factorBlockValue).prod) = 6873567479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_37
      · exact prime_oneHundredNineteenDM_83
      · exact prime_oneHundredNineteenDM_1119109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 6873567479) ^ 3436783739 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 6873567479) ^ 185772094 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 6873567479) ^ 82814066 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 6873567479) ^ 6142 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_6988005883 : Nat.Prime 6988005883 := by
  apply lucas_primality 6988005883 (3 : ZMod 6988005883)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (13, 1), (2714843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (13, 1), (2714843, 1)] : List FactorBlock).map factorBlockValue).prod) = 6988005883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_11
      · exact prime_oneHundredNineteenDM_13
      · exact prime_oneHundredNineteenDM_2714843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6988005883) ^ 3494002941 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 6988005883) ^ 2329335294 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 6988005883) ^ 635273262 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 6988005883) ^ 537538914 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 6988005883) ^ 2574 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_7907540131 : Nat.Prime 7907540131 := by
  apply lucas_primality 7907540131 (2 : ZMod 7907540131)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 2), (1201, 1), (1493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 2), (1201, 1), (1493, 1)] : List FactorBlock).map factorBlockValue).prod) = 7907540131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_1201
      · exact prime_oneHundredNineteenDM_1493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7907540131) ^ 3953770065 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 7907540131) ^ 2635846710 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 7907540131) ^ 1581508026 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 7907540131) ^ 1129648590 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 7907540131) ^ 6584130 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 7907540131) ^ 5296410 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_7911211493 : Nat.Prime 7911211493 := by
  apply lucas_primality 7911211493 (2 : ZMod 7911211493)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (107, 1), (353, 1), (52363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (107, 1), (353, 1), (52363, 1)] : List FactorBlock).map factorBlockValue).prod) = 7911211493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_107
      · exact prime_oneHundredNineteenDM_353
      · exact prime_oneHundredNineteenDM_52363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7911211493) ^ 3955605746 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 7911211493) ^ 73936556 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 7911211493) ^ 22411364 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 7911211493) ^ 151084 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_8104039883 : Nat.Prime 8104039883 := by
  apply lucas_primality 8104039883 (2 : ZMod 8104039883)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3271, 1), (1238771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3271, 1), (1238771, 1)] : List FactorBlock).map factorBlockValue).prod) = 8104039883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3271
      · exact prime_oneHundredNineteenDM_1238771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 8104039883) ^ 4052019941 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 8104039883) ^ 2477542 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 8104039883) ^ 6542 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_8163547831 : Nat.Prime 8163547831 := by
  apply lucas_primality 8163547831 (29 : ZMod 8163547831)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (90706087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (90706087, 1)] : List FactorBlock).map factorBlockValue).prod) = 8163547831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_90706087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (29 : ZMod 8163547831) ^ 4081773915 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (29 : ZMod 8163547831) ^ 2721182610 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (29 : ZMod 8163547831) ^ 1632709566 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (29 : ZMod 8163547831) ^ 90 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_8537789053 : Nat.Prime 8537789053 := by
  apply lucas_primality 8537789053 (2 : ZMod 8537789053)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (18243139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (18243139, 1)] : List FactorBlock).map factorBlockValue).prod) = 8537789053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_13
      · exact prime_oneHundredNineteenDM_18243139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8537789053) ^ 4268894526 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 8537789053) ^ 2845929684 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 8537789053) ^ 656753004 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 8537789053) ^ 468 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_11032773581 : Nat.Prime 11032773581 := by
  apply lucas_primality 11032773581 (2 : ZMod 11032773581)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1049, 1), (525871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1049, 1), (525871, 1)] : List FactorBlock).map factorBlockValue).prod) = 11032773581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_1049
      · exact prime_oneHundredNineteenDM_525871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11032773581) ^ 5516386790 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 11032773581) ^ 2206554716 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 11032773581) ^ 10517420 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 11032773581) ^ 20980 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_11853576017 : Nat.Prime 11853576017 := by
  apply lucas_primality 11853576017 (3 : ZMod 11853576017)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (740848501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (740848501, 1)] : List FactorBlock).map factorBlockValue).prod) = 11853576017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_740848501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 11853576017) ^ 5926788008 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 11853576017) ^ 16 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_11947853651 : Nat.Prime 11947853651 := by
  apply lucas_primality 11947853651 (2 : ZMod 11947853651)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (238957073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (238957073, 1)] : List FactorBlock).map factorBlockValue).prod) = 11947853651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_238957073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11947853651) ^ 5973926825 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 11947853651) ^ 2389570730 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 11947853651) ^ 50 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_16934176229 : Nat.Prime 16934176229 := by
  apply lucas_primality 16934176229 (2 : ZMod 16934176229)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (6521, 1), (649217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (6521, 1), (649217, 1)] : List FactorBlock).map factorBlockValue).prod) = 16934176229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_6521
      · exact prime_oneHundredNineteenDM_649217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 16934176229) ^ 8467088114 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 16934176229) ^ 2596868 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 16934176229) ^ 26084 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_17479427137 : Nat.Prime 17479427137 := by
  apply lucas_primality 17479427137 (10 : ZMod 17479427137)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (53, 1), (433, 1), (3967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (53, 1), (433, 1), (3967, 1)] : List FactorBlock).map factorBlockValue).prod) = 17479427137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_53
      · exact prime_oneHundredNineteenDM_433
      · exact prime_oneHundredNineteenDM_3967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 17479427137) ^ 8739713568 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (10 : ZMod 17479427137) ^ 5826475712 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (10 : ZMod 17479427137) ^ 329800512 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (10 : ZMod 17479427137) ^ 40368192 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (10 : ZMod 17479427137) ^ 4406208 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_24250644403 : Nat.Prime 24250644403 := by
  apply lucas_primality 24250644403 (2 : ZMod 24250644403)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4041774067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4041774067, 1)] : List FactorBlock).map factorBlockValue).prod) = 24250644403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_4041774067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 24250644403) ^ 12125322201 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 24250644403) ^ 8083548134 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 24250644403) ^ 6 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_24469118563 : Nat.Prime 24469118563 := by
  apply lucas_primality 24469118563 (2 : ZMod 24469118563)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (79, 1), (7374659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (79, 1), (7374659, 1)] : List FactorBlock).map factorBlockValue).prod) = 24469118563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_79
      · exact prime_oneHundredNineteenDM_7374659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24469118563) ^ 12234559281 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 24469118563) ^ 8156372854 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 24469118563) ^ 3495588366 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 24469118563) ^ 309735678 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 24469118563) ^ 3318 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_28428157897 : Nat.Prime 28428157897 := by
  apply lucas_primality 28428157897 (5 : ZMod 28428157897)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2179, 1), (543601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2179, 1), (543601, 1)] : List FactorBlock).map factorBlockValue).prod) = 28428157897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_2179
      · exact prime_oneHundredNineteenDM_543601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 28428157897) ^ 14214078948 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 28428157897) ^ 9476052632 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 28428157897) ^ 13046424 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 28428157897) ^ 52296 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_28675006027 : Nat.Prime 28675006027 := by
  apply lucas_primality 28675006027 (3 : ZMod 28675006027)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61, 1), (78347011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61, 1), (78347011, 1)] : List FactorBlock).map factorBlockValue).prod) = 28675006027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_61
      · exact prime_oneHundredNineteenDM_78347011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 28675006027) ^ 14337503013 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 28675006027) ^ 9558335342 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 28675006027) ^ 470082066 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 28675006027) ^ 366 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_29267793559 : Nat.Prime 29267793559 := by
  apply lucas_primality 29267793559 (7 : ZMod 29267793559)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (541996177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (541996177, 1)] : List FactorBlock).map factorBlockValue).prod) = 29267793559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_541996177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 29267793559) ^ 14633896779 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 29267793559) ^ 9755931186 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 29267793559) ^ 54 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_29816588057 : Nat.Prime 29816588057 := by
  apply lucas_primality 29816588057 (3 : ZMod 29816588057)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (40433, 1), (92179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (40433, 1), (92179, 1)] : List FactorBlock).map factorBlockValue).prod) = 29816588057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_40433
      · exact prime_oneHundredNineteenDM_92179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 29816588057) ^ 14908294028 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 29816588057) ^ 737432 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 29816588057) ^ 323464 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_31368597763 : Nat.Prime 31368597763 := by
  apply lucas_primality 31368597763 (2 : ZMod 31368597763)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (479, 1), (10914613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (479, 1), (10914613, 1)] : List FactorBlock).map factorBlockValue).prod) = 31368597763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_479
      · exact prime_oneHundredNineteenDM_10914613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 31368597763) ^ 15684298881 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 31368597763) ^ 10456199254 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 31368597763) ^ 65487678 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 31368597763) ^ 2874 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_31789660873 : Nat.Prime 31789660873 := by
  apply lucas_primality 31789660873 (5 : ZMod 31789660873)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1831, 1), (723413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1831, 1), (723413, 1)] : List FactorBlock).map factorBlockValue).prod) = 31789660873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_1831
      · exact prime_oneHundredNineteenDM_723413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 31789660873) ^ 15894830436 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 31789660873) ^ 10596553624 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 31789660873) ^ 17361912 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 31789660873) ^ 43944 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_32135038499 : Nat.Prime 32135038499 := by
  apply lucas_primality 32135038499 (2 : ZMod 32135038499)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (101, 1), (821, 1), (5237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (101, 1), (821, 1), (5237, 1)] : List FactorBlock).map factorBlockValue).prod) = 32135038499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_37
      · exact prime_oneHundredNineteenDM_101
      · exact prime_oneHundredNineteenDM_821
      · exact prime_oneHundredNineteenDM_5237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 32135038499) ^ 16067519249 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 32135038499) ^ 868514554 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 32135038499) ^ 318168698 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 32135038499) ^ 39141338 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 32135038499) ^ 6136154 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_33883770383 : Nat.Prime 33883770383 := by
  apply lucas_primality 33883770383 (5 : ZMod 33883770383)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (11, 1), (31432069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (11, 1), (31432069, 1)] : List FactorBlock).map factorBlockValue).prod) = 33883770383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_11
      · exact prime_oneHundredNineteenDM_31432069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 33883770383) ^ 16941885191 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 33883770383) ^ 4840538626 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 33883770383) ^ 3080342762 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 33883770383) ^ 1078 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_36554796541 : Nat.Prime 36554796541 := by
  apply lucas_primality 36554796541 (2 : ZMod 36554796541)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (19, 1), (23, 1), (541, 1), (859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (19, 1), (23, 1), (541, 1), (859, 1)] : List FactorBlock).map factorBlockValue).prod) = 36554796541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_19
      · exact prime_oneHundredNineteenDM_23
      · exact prime_oneHundredNineteenDM_541
      · exact prime_oneHundredNineteenDM_859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 36554796541) ^ 18277398270 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 36554796541) ^ 12184932180 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 36554796541) ^ 7310959308 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 36554796541) ^ 1923936660 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 36554796541) ^ 1589338980 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 36554796541) ^ 67568940 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 36554796541) ^ 42555060 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_38125454137 : Nat.Prime 38125454137 := by
  apply lucas_primality 38125454137 (15 : ZMod 38125454137)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (11, 1), (2447, 1), (8431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (11, 1), (2447, 1), (8431, 1)] : List FactorBlock).map factorBlockValue).prod) = 38125454137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_11
      · exact prime_oneHundredNineteenDM_2447
      · exact prime_oneHundredNineteenDM_8431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 38125454137) ^ 19062727068 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (15 : ZMod 38125454137) ^ 12708484712 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (15 : ZMod 38125454137) ^ 5446493448 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (15 : ZMod 38125454137) ^ 3465950376 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (15 : ZMod 38125454137) ^ 15580488 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (15 : ZMod 38125454137) ^ 4522056 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_45636734023 : Nat.Prime 45636734023 := by
  apply lucas_primality 45636734023 (6 : ZMod 45636734023)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (17, 1), (40674451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (17, 1), (40674451, 1)] : List FactorBlock).map factorBlockValue).prod) = 45636734023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_11
      · exact prime_oneHundredNineteenDM_17
      · exact prime_oneHundredNineteenDM_40674451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 45636734023) ^ 22818367011 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 15212244674 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 4148794002 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 2684513766 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 1122 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_46350616811 : Nat.Prime 46350616811 := by
  apply lucas_primality 46350616811 (2 : ZMod 46350616811)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1669, 1), (2777149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1669, 1), (2777149, 1)] : List FactorBlock).map factorBlockValue).prod) = 46350616811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_1669
      · exact prime_oneHundredNineteenDM_2777149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 46350616811) ^ 23175308405 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 46350616811) ^ 9270123362 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 46350616811) ^ 27771490 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 46350616811) ^ 16690 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_48437485823 : Nat.Prime 48437485823 := by
  apply lucas_primality 48437485823 (5 : ZMod 48437485823)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (2201703901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (2201703901, 1)] : List FactorBlock).map factorBlockValue).prod) = 48437485823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_11
      · exact prime_oneHundredNineteenDM_2201703901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 48437485823) ^ 24218742911 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 48437485823) ^ 4403407802 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 48437485823) ^ 22 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_64486793911 : Nat.Prime 64486793911 := by
  apply lucas_primality 64486793911 (11 : ZMod 64486793911)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (11, 2), (2537851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (11, 2), (2537851, 1)] : List FactorBlock).map factorBlockValue).prod) = 64486793911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_11
      · exact prime_oneHundredNineteenDM_2537851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 64486793911) ^ 32243396955 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (11 : ZMod 64486793911) ^ 21495597970 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (11 : ZMod 64486793911) ^ 12897358782 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (11 : ZMod 64486793911) ^ 9212399130 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (11 : ZMod 64486793911) ^ 5862435810 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (11 : ZMod 64486793911) ^ 25410 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_67801386329 : Nat.Prime 67801386329 := by
  apply lucas_primality 67801386329 (3 : ZMod 67801386329)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (3181, 1), (204947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (3181, 1), (204947, 1)] : List FactorBlock).map factorBlockValue).prod) = 67801386329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_13
      · exact prime_oneHundredNineteenDM_3181
      · exact prime_oneHundredNineteenDM_204947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 67801386329) ^ 33900693164 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 67801386329) ^ 5215491256 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 67801386329) ^ 21314488 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 67801386329) ^ 330824 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_69901258927 : Nat.Prime 69901258927 := by
  apply lucas_primality 69901258927 (3 : ZMod 69901258927)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1307, 1), (8913703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1307, 1), (8913703, 1)] : List FactorBlock).map factorBlockValue).prod) = 69901258927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_1307
      · exact prime_oneHundredNineteenDM_8913703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 69901258927) ^ 34950629463 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 69901258927) ^ 23300419642 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 69901258927) ^ 53482218 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 69901258927) ^ 7842 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_81968474141 : Nat.Prime 81968474141 := by
  apply lucas_primality 81968474141 (2 : ZMod 81968474141)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (17293, 1), (33857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (17293, 1), (33857, 1)] : List FactorBlock).map factorBlockValue).prod) = 81968474141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_17293
      · exact prime_oneHundredNineteenDM_33857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 81968474141) ^ 40984237070 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 81968474141) ^ 16393694828 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 81968474141) ^ 11709782020 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 81968474141) ^ 4739980 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 81968474141) ^ 2421020 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_121175790187 : Nat.Prime 121175790187 := by
  apply lucas_primality 121175790187 (2 : ZMod 121175790187)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (17, 1), (107999813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (17, 1), (107999813, 1)] : List FactorBlock).map factorBlockValue).prod) = 121175790187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_11
      · exact prime_oneHundredNineteenDM_17
      · exact prime_oneHundredNineteenDM_107999813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 121175790187) ^ 60587895093 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 121175790187) ^ 40391930062 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 121175790187) ^ 11015980926 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 121175790187) ^ 7127987658 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 121175790187) ^ 1122 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_123789818377 : Nat.Prime 123789818377 := by
  apply lucas_primality 123789818377 (15 : ZMod 123789818377)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (7, 2), (11695939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (7, 2), (11695939, 1)] : List FactorBlock).map factorBlockValue).prod) = 123789818377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_11695939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 123789818377) ^ 61894909188 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (15 : ZMod 123789818377) ^ 41263272792 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (15 : ZMod 123789818377) ^ 17684259768 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (15 : ZMod 123789818377) ^ 10584 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_155440836073 : Nat.Prime 155440836073 := by
  apply lucas_primality 155440836073 (5 : ZMod 155440836073)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (89, 1), (373, 1), (65033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (89, 1), (373, 1), (65033, 1)] : List FactorBlock).map factorBlockValue).prod) = 155440836073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_89
      · exact prime_oneHundredNineteenDM_373
      · exact prime_oneHundredNineteenDM_65033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 155440836073) ^ 77720418036 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 51813612024 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 1746526248 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 416731464 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 2390184 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_158224229861 : Nat.Prime 158224229861 := by
  apply lucas_primality 158224229861 (2 : ZMod 158224229861)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7911211493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7911211493, 1)] : List FactorBlock).map factorBlockValue).prod) = 158224229861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_7911211493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 158224229861) ^ 79112114930 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 158224229861) ^ 31644845972 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 158224229861) ^ 20 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_159073273291 : Nat.Prime 159073273291 := by
  apply lucas_primality 159073273291 (2 : ZMod 159073273291)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (311908379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (311908379, 1)] : List FactorBlock).map factorBlockValue).prod) = 159073273291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_17
      · exact prime_oneHundredNineteenDM_311908379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 159073273291) ^ 79536636645 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 159073273291) ^ 53024424430 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 159073273291) ^ 31814654658 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 159073273291) ^ 9357251370 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 159073273291) ^ 510 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_178108948141 : Nat.Prime 178108948141 := by
  apply lucas_primality 178108948141 (2 : ZMod 178108948141)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (31, 1), (95757499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (31, 1), (95757499, 1)] : List FactorBlock).map factorBlockValue).prod) = 178108948141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_31
      · exact prime_oneHundredNineteenDM_95757499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 178108948141) ^ 89054474070 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 178108948141) ^ 59369649380 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 178108948141) ^ 35621789628 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 178108948141) ^ 5745449940 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 178108948141) ^ 1860 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_184564968157 : Nat.Prime 184564968157 := by
  apply lucas_primality 184564968157 (2 : ZMod 184564968157)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5126804671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5126804671, 1)] : List FactorBlock).map factorBlockValue).prod) = 184564968157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5126804671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 184564968157) ^ 92282484078 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 184564968157) ^ 61521656052 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 184564968157) ^ 36 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_228171525083 : Nat.Prime 228171525083 := by
  apply lucas_primality 228171525083 (2 : ZMod 228171525083)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (80831, 1), (1411411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (80831, 1), (1411411, 1)] : List FactorBlock).map factorBlockValue).prod) = 228171525083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_80831
      · exact prime_oneHundredNineteenDM_1411411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 228171525083) ^ 114085762541 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 228171525083) ^ 2822822 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 228171525083) ^ 161662 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_233717500609 : Nat.Prime 233717500609 := by
  apply lucas_primality 233717500609 (7 : ZMod 233717500609)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (331, 1), (3677579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (331, 1), (3677579, 1)] : List FactorBlock).map factorBlockValue).prod) = 233717500609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_331
      · exact prime_oneHundredNineteenDM_3677579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 233717500609) ^ 116858750304 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 233717500609) ^ 77905833536 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 233717500609) ^ 706095168 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 233717500609) ^ 63552 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_262269881617 : Nat.Prime 262269881617 := by
  apply lucas_primality 262269881617 (10 : ZMod 262269881617)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (61, 1), (1321, 1), (67807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (61, 1), (1321, 1), (67807, 1)] : List FactorBlock).map factorBlockValue).prod) = 262269881617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_61
      · exact prime_oneHundredNineteenDM_1321
      · exact prime_oneHundredNineteenDM_67807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 262269881617) ^ 131134940808 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (10 : ZMod 262269881617) ^ 87423293872 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (10 : ZMod 262269881617) ^ 4299506256 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (10 : ZMod 262269881617) ^ 198538896 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (10 : ZMod 262269881617) ^ 3867888 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_325603473989 : Nat.Prime 325603473989 := by
  apply lucas_primality 325603473989 (3 : ZMod 325603473989)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (311, 1), (20133779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (311, 1), (20133779, 1)] : List FactorBlock).map factorBlockValue).prod) = 325603473989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_13
      · exact prime_oneHundredNineteenDM_311
      · exact prime_oneHundredNineteenDM_20133779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 325603473989) ^ 162801736994 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 325603473989) ^ 25046421076 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 325603473989) ^ 1046956508 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 325603473989) ^ 16172 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_343588771969 : Nat.Prime 343588771969 := by
  apply lucas_primality 343588771969 (31 : ZMod 343588771969)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (13, 1), (3931, 1), (17509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (13, 1), (3931, 1), (17509, 1)] : List FactorBlock).map factorBlockValue).prod) = 343588771969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_13
      · exact prime_oneHundredNineteenDM_3931
      · exact prime_oneHundredNineteenDM_17509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 343588771969) ^ 171794385984 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 114529590656 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 26429905536 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 87404928 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 19623552 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_454004135993 : Nat.Prime 454004135993 := by
  apply lucas_primality 454004135993 (3 : ZMod 454004135993)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (3187, 1), (1618807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (3187, 1), (1618807, 1)] : List FactorBlock).map factorBlockValue).prod) = 454004135993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_11
      · exact prime_oneHundredNineteenDM_3187
      · exact prime_oneHundredNineteenDM_1618807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 454004135993) ^ 227002067996 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 454004135993) ^ 41273103272 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 454004135993) ^ 142455016 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 454004135993) ^ 280456 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_470630547421 : Nat.Prime 470630547421 := by
  apply lucas_primality 470630547421 (10 : ZMod 470630547421)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (713076587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (713076587, 1)] : List FactorBlock).map factorBlockValue).prod) = 470630547421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_11
      · exact prime_oneHundredNineteenDM_713076587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 470630547421) ^ 235315273710 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (10 : ZMod 470630547421) ^ 156876849140 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (10 : ZMod 470630547421) ^ 94126109484 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (10 : ZMod 470630547421) ^ 42784595220 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (10 : ZMod 470630547421) ^ 660 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_510047838721 : Nat.Prime 510047838721 := by
  apply lucas_primality 510047838721 (13 : ZMod 510047838721)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 2), (5, 1), (7, 1), (3162499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 2), (5, 1), (7, 1), (3162499, 1)] : List FactorBlock).map factorBlockValue).prod) = 510047838721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_3162499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 510047838721) ^ 255023919360 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (13 : ZMod 510047838721) ^ 170015946240 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (13 : ZMod 510047838721) ^ 102009567744 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (13 : ZMod 510047838721) ^ 72863976960 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (13 : ZMod 510047838721) ^ 161280 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_528792879631 : Nat.Prime 528792879631 := by
  apply lucas_primality 528792879631 (3 : ZMod 528792879631)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (59473, 1), (296377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (59473, 1), (296377, 1)] : List FactorBlock).map factorBlockValue).prod) = 528792879631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_59473
      · exact prime_oneHundredNineteenDM_296377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 528792879631) ^ 264396439815 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 528792879631) ^ 176264293210 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 528792879631) ^ 105758575926 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 528792879631) ^ 8891310 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 528792879631) ^ 1784190 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_908008271987 : Nat.Prime 908008271987 := by
  apply lucas_primality 908008271987 (2 : ZMod 908008271987)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (454004135993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (454004135993, 1)] : List FactorBlock).map factorBlockValue).prod) = 908008271987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_454004135993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 908008271987) ^ 454004135993 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 908008271987) ^ 2 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_929643341663 : Nat.Prime 929643341663 := by
  apply lucas_primality 929643341663 (5 : ZMod 929643341663)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (47111, 1), (1409503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (47111, 1), (1409503, 1)] : List FactorBlock).map factorBlockValue).prod) = 929643341663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_47111
      · exact prime_oneHundredNineteenDM_1409503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 929643341663) ^ 464821670831 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 929643341663) ^ 132806191666 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 929643341663) ^ 19733042 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 929643341663) ^ 659554 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_1070359359989 : Nat.Prime 1070359359989 := by
  apply lucas_primality 1070359359989 (2 : ZMod 1070359359989)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (1231, 1), (4625021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (1231, 1), (4625021, 1)] : List FactorBlock).map factorBlockValue).prod) = 1070359359989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_47
      · exact prime_oneHundredNineteenDM_1231
      · exact prime_oneHundredNineteenDM_4625021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1070359359989) ^ 535179679994 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1070359359989) ^ 22773603404 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1070359359989) ^ 869503948 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1070359359989) ^ 231428 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_1573619289703 : Nat.Prime 1573619289703 := by
  apply lucas_primality 1573619289703 (13 : ZMod 1573619289703)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (262269881617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (262269881617, 1)] : List FactorBlock).map factorBlockValue).prod) = 1573619289703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_262269881617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 1573619289703) ^ 786809644851 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (13 : ZMod 1573619289703) ^ 524539763234 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (13 : ZMod 1573619289703) ^ 6 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_1662919566157 : Nat.Prime 1662919566157 := by
  apply lucas_primality 1662919566157 (2 : ZMod 1662919566157)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (2897, 1), (15944843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (2897, 1), (15944843, 1)] : List FactorBlock).map factorBlockValue).prod) = 1662919566157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_2897
      · exact prime_oneHundredNineteenDM_15944843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1662919566157) ^ 831459783078 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1662919566157) ^ 554306522052 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1662919566157) ^ 574014348 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1662919566157) ^ 104292 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_1694188519151 : Nat.Prime 1694188519151 := by
  apply lucas_primality 1694188519151 (7 : ZMod 1694188519151)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (33883770383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (33883770383, 1)] : List FactorBlock).map factorBlockValue).prod) = 1694188519151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_33883770383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1694188519151) ^ 847094259575 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1694188519151) ^ 338837703830 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1694188519151) ^ 50 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_1714850334569 : Nat.Prime 1714850334569 := by
  apply lucas_primality 1714850334569 (3 : ZMod 1714850334569)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (31, 1), (987817013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (31, 1), (987817013, 1)] : List FactorBlock).map factorBlockValue).prod) = 1714850334569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_31
      · exact prime_oneHundredNineteenDM_987817013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1714850334569) ^ 857425167284 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1714850334569) ^ 244978619224 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1714850334569) ^ 55317752728 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1714850334569) ^ 1736 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_2033386944349 : Nat.Prime 2033386944349 := by
  apply lucas_primality 2033386944349 (2 : ZMod 2033386944349)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (73, 1), (122169367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (73, 1), (122169367, 1)] : List FactorBlock).map factorBlockValue).prod) = 2033386944349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_19
      · exact prime_oneHundredNineteenDM_73
      · exact prime_oneHundredNineteenDM_122169367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2033386944349) ^ 1016693472174 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2033386944349) ^ 677795648116 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2033386944349) ^ 107020365492 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2033386944349) ^ 27854615676 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2033386944349) ^ 16644 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_2047758613933 : Nat.Prime 2047758613933 := by
  apply lucas_primality 2047758613933 (6 : ZMod 2047758613933)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (6481, 1), (26330281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (6481, 1), (26330281, 1)] : List FactorBlock).map factorBlockValue).prod) = 2047758613933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_6481
      · exact prime_oneHundredNineteenDM_26330281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 2047758613933) ^ 1023879306966 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 2047758613933) ^ 682586204644 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 2047758613933) ^ 315963372 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 2047758613933) ^ 77772 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_2054790765803 : Nat.Prime 2054790765803 := by
  apply lucas_primality 2054790765803 (2 : ZMod 2054790765803)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (351653, 1), (2921617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (351653, 1), (2921617, 1)] : List FactorBlock).map factorBlockValue).prod) = 2054790765803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_351653
      · exact prime_oneHundredNineteenDM_2921617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2054790765803) ^ 1027395382901 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2054790765803) ^ 5843234 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2054790765803) ^ 703306 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_2269179614687 : Nat.Prime 2269179614687 := by
  apply lucas_primality 2269179614687 (5 : ZMod 2269179614687)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (16934176229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (16934176229, 1)] : List FactorBlock).map factorBlockValue).prod) = 2269179614687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_67
      · exact prime_oneHundredNineteenDM_16934176229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2269179614687) ^ 1134589807343 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 2269179614687) ^ 33868352458 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 2269179614687) ^ 134 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_2527947581639 : Nat.Prime 2527947581639 := by
  apply lucas_primality 2527947581639 (7 : ZMod 2527947581639)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (9467, 1), (133513657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (9467, 1), (133513657, 1)] : List FactorBlock).map factorBlockValue).prod) = 2527947581639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_9467
      · exact prime_oneHundredNineteenDM_133513657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 2527947581639) ^ 1263973790819 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 2527947581639) ^ 267027314 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 2527947581639) ^ 18934 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_2867484876241 : Nat.Prime 2867484876241 := by
  apply lucas_primality 2867484876241 (7 : ZMod 2867484876241)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (11947853651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (11947853651, 1)] : List FactorBlock).map factorBlockValue).prod) = 2867484876241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_11947853651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2867484876241) ^ 1433742438120 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 2867484876241) ^ 955828292080 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 2867484876241) ^ 573496975248 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 2867484876241) ^ 240 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_3275850185743 : Nat.Prime 3275850185743 := by
  apply lucas_primality 3275850185743 (3 : ZMod 3275850185743)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5569, 1), (98038253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5569, 1), (98038253, 1)] : List FactorBlock).map factorBlockValue).prod) = 3275850185743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5569
      · exact prime_oneHundredNineteenDM_98038253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3275850185743) ^ 1637925092871 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 3275850185743) ^ 1091950061914 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 3275850185743) ^ 588229518 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 3275850185743) ^ 33414 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_3429700669139 : Nat.Prime 3429700669139 := by
  apply lucas_primality 3429700669139 (2 : ZMod 3429700669139)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1714850334569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1714850334569, 1)] : List FactorBlock).map factorBlockValue).prod) = 3429700669139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_1714850334569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 3429700669139) ^ 1714850334569 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3429700669139) ^ 2 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_3889939143841 : Nat.Prime 3889939143841 := by
  apply lucas_primality 3889939143841 (17 : ZMod 3889939143841)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (8104039883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (8104039883, 1)] : List FactorBlock).map factorBlockValue).prod) = 3889939143841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_8104039883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 3889939143841) ^ 1944969571920 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (17 : ZMod 3889939143841) ^ 1296646381280 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (17 : ZMod 3889939143841) ^ 777987828768 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (17 : ZMod 3889939143841) ^ 480 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_3926291898239 : Nat.Prime 3926291898239 := by
  apply lucas_primality 3926291898239 (7 : ZMod 3926291898239)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (649507, 1), (3022517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (649507, 1), (3022517, 1)] : List FactorBlock).map factorBlockValue).prod) = 3926291898239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_649507
      · exact prime_oneHundredNineteenDM_3022517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 3926291898239) ^ 1963145949119 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 3926291898239) ^ 6045034 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 3926291898239) ^ 1299014 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_4041154484167 : Nat.Prime 4041154484167 := by
  apply lucas_primality 4041154484167 (3 : ZMod 4041154484167)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (277, 1), (2431500893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (277, 1), (2431500893, 1)] : List FactorBlock).map factorBlockValue).prod) = 4041154484167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_277
      · exact prime_oneHundredNineteenDM_2431500893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4041154484167) ^ 2020577242083 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 4041154484167) ^ 1347051494722 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 4041154484167) ^ 14589005358 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 4041154484167) ^ 1662 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_4285064009893 : Nat.Prime 4285064009893 := by
  apply lucas_primality 4285064009893 (2 : ZMod 4285064009893)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (89, 1), (3187, 1), (1258937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (89, 1), (3187, 1), (1258937, 1)] : List FactorBlock).map factorBlockValue).prod) = 4285064009893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_89
      · exact prime_oneHundredNineteenDM_3187
      · exact prime_oneHundredNineteenDM_1258937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4285064009893) ^ 2142532004946 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4285064009893) ^ 1428354669964 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4285064009893) ^ 48146786628 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4285064009893) ^ 1344544716 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4285064009893) ^ 3403716 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_4285489367539 : Nat.Prime 4285489367539 := by
  apply lucas_primality 4285489367539 (2 : ZMod 4285489367539)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (61, 1), (349, 1), (11183369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (61, 1), (349, 1), (11183369, 1)] : List FactorBlock).map factorBlockValue).prod) = 4285489367539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_61
      · exact prime_oneHundredNineteenDM_349
      · exact prime_oneHundredNineteenDM_11183369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4285489367539) ^ 2142744683769 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4285489367539) ^ 1428496455846 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4285489367539) ^ 70253924058 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4285489367539) ^ 12279339162 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4285489367539) ^ 383202 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_4667461964617 : Nat.Prime 4667461964617 := by
  apply lucas_primality 4667461964617 (5 : ZMod 4667461964617)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (59, 1), (197, 1), (1521103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (59, 1), (197, 1), (1521103, 1)] : List FactorBlock).map factorBlockValue).prod) = 4667461964617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_11
      · exact prime_oneHundredNineteenDM_59
      · exact prime_oneHundredNineteenDM_197
      · exact prime_oneHundredNineteenDM_1521103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4667461964617) ^ 2333730982308 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 4667461964617) ^ 1555820654872 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 4667461964617) ^ 424314724056 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 4667461964617) ^ 79109524824 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 4667461964617) ^ 23692700328 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 4667461964617) ^ 3068472 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_5919507744571 : Nat.Prime 5919507744571 := by
  apply lucas_primality 5919507744571 (3 : ZMod 5919507744571)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (101, 1), (93030139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (101, 1), (93030139, 1)] : List FactorBlock).map factorBlockValue).prod) = 5919507744571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_101
      · exact prime_oneHundredNineteenDM_93030139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5919507744571) ^ 2959753872285 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 5919507744571) ^ 1973169248190 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 5919507744571) ^ 1183901548914 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 5919507744571) ^ 845643963510 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 5919507744571) ^ 58608987570 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 5919507744571) ^ 63630 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_5996270350439 : Nat.Prime 5996270350439 := by
  apply lucas_primality 5996270350439 (13 : ZMod 5996270350439)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (15473, 1), (2729093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (15473, 1), (2729093, 1)] : List FactorBlock).map factorBlockValue).prod) = 5996270350439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_71
      · exact prime_oneHundredNineteenDM_15473
      · exact prime_oneHundredNineteenDM_2729093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 5996270350439) ^ 2998135175219 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (13 : ZMod 5996270350439) ^ 84454511978 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (13 : ZMod 5996270350439) ^ 387531206 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (13 : ZMod 5996270350439) ^ 2197166 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_6880433178221 : Nat.Prime 6880433178221 := by
  apply lucas_primality 6880433178221 (2 : ZMod 6880433178221)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (179, 1), (4177, 1), (65731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (179, 1), (4177, 1), (65731, 1)] : List FactorBlock).map factorBlockValue).prod) = 6880433178221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_179
      · exact prime_oneHundredNineteenDM_4177
      · exact prime_oneHundredNineteenDM_65731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6880433178221) ^ 3440216589110 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 6880433178221) ^ 1376086635644 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 6880433178221) ^ 982919025460 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 6880433178221) ^ 38438174180 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 6880433178221) ^ 1647218860 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 6880433178221) ^ 104675620 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_7096647417623 : Nat.Prime 7096647417623 := by
  apply lucas_primality 7096647417623 (5 : ZMod 7096647417623)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (29, 1), (17479427137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (29, 1), (17479427137, 1)] : List FactorBlock).map factorBlockValue).prod) = 7096647417623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_29
      · exact prime_oneHundredNineteenDM_17479427137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7096647417623) ^ 3548323708811 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 7096647417623) ^ 1013806773946 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 7096647417623) ^ 244711979918 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 7096647417623) ^ 406 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_7666832210951 : Nat.Prime 7666832210951 := by
  apply lucas_primality 7666832210951 (7 : ZMod 7666832210951)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (11, 1), (61, 1), (228519589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (11, 1), (61, 1), (228519589, 1)] : List FactorBlock).map factorBlockValue).prod) = 7666832210951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_11
      · exact prime_oneHundredNineteenDM_61
      · exact prime_oneHundredNineteenDM_228519589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 7666832210951) ^ 3833416105475 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 7666832210951) ^ 1533366442190 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 7666832210951) ^ 696984746450 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 7666832210951) ^ 125685773950 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 7666832210951) ^ 33550 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_8272997230081 : Nat.Prime 8272997230081 := by
  apply lucas_primality 8272997230081 (14 : ZMod 8272997230081)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 1), (5, 1), (11, 1), (53, 1), (283, 1), (6529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 1), (5, 1), (11, 1), (53, 1), (283, 1), (6529, 1)] : List FactorBlock).map factorBlockValue).prod) = 8272997230081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_11
      · exact prime_oneHundredNineteenDM_53
      · exact prime_oneHundredNineteenDM_283
      · exact prime_oneHundredNineteenDM_6529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 8272997230081) ^ 4136498615040 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (14 : ZMod 8272997230081) ^ 2757665743360 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (14 : ZMod 8272997230081) ^ 1654599446016 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (14 : ZMod 8272997230081) ^ 752090657280 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (14 : ZMod 8272997230081) ^ 156094287360 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (14 : ZMod 8272997230081) ^ 29233205760 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (14 : ZMod 8272997230081) ^ 1267115520 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_9890071056629 : Nat.Prime 9890071056629 := by
  apply lucas_primality 9890071056629 (2 : ZMod 9890071056629)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (17, 1), (19, 1), (53, 1), (163, 1), (126583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (17, 1), (19, 1), (53, 1), (163, 1), (126583, 1)] : List FactorBlock).map factorBlockValue).prod) = 9890071056629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_17
      · exact prime_oneHundredNineteenDM_19
      · exact prime_oneHundredNineteenDM_53
      · exact prime_oneHundredNineteenDM_163
      · exact prime_oneHundredNineteenDM_126583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9890071056629) ^ 4945035528314 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 9890071056629) ^ 1412867293804 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 9890071056629) ^ 581768885684 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 9890071056629) ^ 520530055612 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 9890071056629) ^ 186605114276 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 9890071056629) ^ 60675282556 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 9890071056629) ^ 78131116 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_10286236220731 : Nat.Prime 10286236220731 := by
  apply lucas_primality 10286236220731 (2 : ZMod 10286236220731)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (127, 1), (2699799533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (127, 1), (2699799533, 1)] : List FactorBlock).map factorBlockValue).prod) = 10286236220731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_127
      · exact prime_oneHundredNineteenDM_2699799533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10286236220731) ^ 5143118110365 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 10286236220731) ^ 3428745406910 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 10286236220731) ^ 2057247244146 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 10286236220731) ^ 80993985990 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 10286236220731) ^ 3810 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_10536894547169 : Nat.Prime 10536894547169 := by
  apply lucas_primality 10536894547169 (3 : ZMod 10536894547169)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 1), (17, 1), (389, 1), (4526593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 1), (17, 1), (389, 1), (4526593, 1)] : List FactorBlock).map factorBlockValue).prod) = 10536894547169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_11
      · exact prime_oneHundredNineteenDM_17
      · exact prime_oneHundredNineteenDM_389
      · exact prime_oneHundredNineteenDM_4526593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10536894547169) ^ 5268447273584 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 10536894547169) ^ 957899504288 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 10536894547169) ^ 619817326304 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 10536894547169) ^ 27087132512 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 10536894547169) ^ 2327776 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_12975558633731 : Nat.Prime 12975558633731 := by
  apply lucas_primality 12975558633731 (2 : ZMod 12975558633731)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (11, 1), (691, 1), (24386939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (11, 1), (691, 1), (24386939, 1)] : List FactorBlock).map factorBlockValue).prod) = 12975558633731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_11
      · exact prime_oneHundredNineteenDM_691
      · exact prime_oneHundredNineteenDM_24386939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12975558633731) ^ 6487779316865 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 12975558633731) ^ 2595111726746 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 12975558633731) ^ 1853651233390 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 12975558633731) ^ 1179596239430 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 12975558633731) ^ 18777943030 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 12975558633731) ^ 532070 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_13044008409863 : Nat.Prime 13044008409863 := by
  apply lucas_primality 13044008409863 (5 : ZMod 13044008409863)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (159073273291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (159073273291, 1)] : List FactorBlock).map factorBlockValue).prod) = 13044008409863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_41
      · exact prime_oneHundredNineteenDM_159073273291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 13044008409863) ^ 6522004204931 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 13044008409863) ^ 318146546582 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 13044008409863) ^ 82 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_17160791887493 : Nat.Prime 17160791887493 := by
  apply lucas_primality 17160791887493 (2 : ZMod 17160791887493)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (61, 1), (6393737663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (61, 1), (6393737663, 1)] : List FactorBlock).map factorBlockValue).prod) = 17160791887493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_11
      · exact prime_oneHundredNineteenDM_61
      · exact prime_oneHundredNineteenDM_6393737663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17160791887493) ^ 8580395943746 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 17160791887493) ^ 1560071989772 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 17160791887493) ^ 281324457172 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 17160791887493) ^ 2684 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_30108756328351 : Nat.Prime 30108756328351 := by
  apply lucas_primality 30108756328351 (7 : ZMod 30108756328351)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (7, 1), (28675006027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (7, 1), (28675006027, 1)] : List FactorBlock).map factorBlockValue).prod) = 30108756328351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_28675006027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 30108756328351) ^ 15054378164175 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 30108756328351) ^ 10036252109450 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 30108756328351) ^ 6021751265670 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 30108756328351) ^ 4301250904050 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 30108756328351) ^ 1050 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_40269623570651 : Nat.Prime 40269623570651 := by
  apply lucas_primality 40269623570651 (2 : ZMod 40269623570651)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (73, 1), (11032773581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (73, 1), (11032773581, 1)] : List FactorBlock).map factorBlockValue).prod) = 40269623570651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_73
      · exact prime_oneHundredNineteenDM_11032773581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40269623570651) ^ 20134811785325 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 40269623570651) ^ 8053924714130 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 40269623570651) ^ 551638679050 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 40269623570651) ^ 3650 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_40604292994541 : Nat.Prime 40604292994541 := by
  apply lucas_primality 40604292994541 (10 : ZMod 40604292994541)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (184564968157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (184564968157, 1)] : List FactorBlock).map factorBlockValue).prod) = 40604292994541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_11
      · exact prime_oneHundredNineteenDM_184564968157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 40604292994541) ^ 20302146497270 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (10 : ZMod 40604292994541) ^ 8120858598908 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (10 : ZMod 40604292994541) ^ 3691299363140 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (10 : ZMod 40604292994541) ^ 220 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_59808758887459 : Nat.Prime 59808758887459 := by
  apply lucas_primality 59808758887459 (7 : ZMod 59808758887459)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (158224229861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (158224229861, 1)] : List FactorBlock).map factorBlockValue).prod) = 59808758887459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_158224229861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 59808758887459) ^ 29904379443729 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 59808758887459) ^ 19936252962486 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 59808758887459) ^ 8544108412494 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 59808758887459) ^ 378 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_62703246890527 : Nat.Prime 62703246890527 := by
  apply lucas_primality 62703246890527 (5 : ZMod 62703246890527)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (17, 1), (379, 1), (147454477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (17, 1), (379, 1), (147454477, 1)] : List FactorBlock).map factorBlockValue).prod) = 62703246890527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_11
      · exact prime_oneHundredNineteenDM_17
      · exact prime_oneHundredNineteenDM_379
      · exact prime_oneHundredNineteenDM_147454477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 62703246890527) ^ 31351623445263 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 62703246890527) ^ 20901082296842 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 62703246890527) ^ 5700295171866 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 62703246890527) ^ 3688426287678 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 62703246890527) ^ 165443923194 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 62703246890527) ^ 425238 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_87133079836741 : Nat.Prime 87133079836741 := by
  apply lucas_primality 87133079836741 (6 : ZMod 87133079836741)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (73, 1), (137, 1), (20743897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (73, 1), (137, 1), (20743897, 1)] : List FactorBlock).map factorBlockValue).prod) = 87133079836741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_73
      · exact prime_oneHundredNineteenDM_137
      · exact prime_oneHundredNineteenDM_20743897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 87133079836741) ^ 43566539918370 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 87133079836741) ^ 29044359945580 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 87133079836741) ^ 17426615967348 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 87133079836741) ^ 12447582833820 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 87133079836741) ^ 1193603833380 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 87133079836741) ^ 636007882020 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 87133079836741) ^ 4200420 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_95102248871501 : Nat.Prime 95102248871501 := by
  apply lucas_primality 95102248871501 (2 : ZMod 95102248871501)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 3), (13, 1), (1103, 1), (2689, 1), (4933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 3), (13, 1), (1103, 1), (2689, 1), (4933, 1)] : List FactorBlock).map factorBlockValue).prod) = 95102248871501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_13
      · exact prime_oneHundredNineteenDM_1103
      · exact prime_oneHundredNineteenDM_2689
      · exact prime_oneHundredNineteenDM_4933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 95102248871501) ^ 47551124435750 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 95102248871501) ^ 19020449774300 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 95102248871501) ^ 7315557605500 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 95102248871501) ^ 86221440500 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 95102248871501) ^ 35367143500 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 95102248871501) ^ 19278785500 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_99821153922769 : Nat.Prime 99821153922769 := by
  apply lucas_primality 99821153922769 (7 : ZMod 99821153922769)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (503, 1), (1378136099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (503, 1), (1378136099, 1)] : List FactorBlock).map factorBlockValue).prod) = 99821153922769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_503
      · exact prime_oneHundredNineteenDM_1378136099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 99821153922769) ^ 49910576961384 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 99821153922769) ^ 33273717974256 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 99821153922769) ^ 198451598256 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 99821153922769) ^ 72432 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_103871723856029 : Nat.Prime 103871723856029 := by
  apply lucas_primality 103871723856029 (2 : ZMod 103871723856029)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (383, 1), (67801386329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (383, 1), (67801386329, 1)] : List FactorBlock).map factorBlockValue).prod) = 103871723856029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_383
      · exact prime_oneHundredNineteenDM_67801386329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 103871723856029) ^ 51935861928014 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 103871723856029) ^ 271205545316 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 103871723856029) ^ 1532 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_103894151639963 : Nat.Prime 103894151639963 := by
  apply lucas_primality 103894151639963 (2 : ZMod 103894151639963)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (163, 1), (431, 1), (443, 1), (23509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (163, 1), (431, 1), (443, 1), (23509, 1)] : List FactorBlock).map factorBlockValue).prod) = 103894151639963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_71
      · exact prime_oneHundredNineteenDM_163
      · exact prime_oneHundredNineteenDM_431
      · exact prime_oneHundredNineteenDM_443
      · exact prime_oneHundredNineteenDM_23509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 103894151639963) ^ 51947075819981 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 103894151639963) ^ 1463297910422 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 103894151639963) ^ 637387433374 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 103894151639963) ^ 241053716102 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 103894151639963) ^ 234524044334 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 103894151639963) ^ 4419335218 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_190204497743003 : Nat.Prime 190204497743003 := by
  apply lucas_primality 190204497743003 (2 : ZMod 190204497743003)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (95102248871501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (95102248871501, 1)] : List FactorBlock).map factorBlockValue).prod) = 190204497743003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_95102248871501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 190204497743003) ^ 95102248871501 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 190204497743003) ^ 2 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_414066027480449 : Nat.Prime 414066027480449 := by
  apply lucas_primality 414066027480449 (6 : ZMod 414066027480449)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (7, 1), (139, 1), (49369, 1), (67343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (7, 1), (139, 1), (49369, 1), (67343, 1)] : List FactorBlock).map factorBlockValue).prod) = 414066027480449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_139
      · exact prime_oneHundredNineteenDM_49369
      · exact prime_oneHundredNineteenDM_67343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 414066027480449) ^ 207033013740224 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 414066027480449) ^ 59152289640064 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 414066027480449) ^ 2978892284032 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 414066027480449) ^ 8387166592 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 414066027480449) ^ 6148612736 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_605401060944023 : Nat.Prime 605401060944023 := by
  apply lucas_primality 605401060944023 (5 : ZMod 605401060944023)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (701, 1), (9769, 1), (6314617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (701, 1), (9769, 1), (6314617, 1)] : List FactorBlock).map factorBlockValue).prod) = 605401060944023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_701
      · exact prime_oneHundredNineteenDM_9769
      · exact prime_oneHundredNineteenDM_6314617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 605401060944023) ^ 302700530472011 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 86485865849146 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 863624908622 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 61971651238 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 95872966 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_777594629002747 : Nat.Prime 777594629002747 := by
  apply lucas_primality 777594629002747 (2 : ZMod 777594629002747)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (9491, 1), (440482171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (9491, 1), (440482171, 1)] : List FactorBlock).map factorBlockValue).prod) = 777594629002747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_31
      · exact prime_oneHundredNineteenDM_9491
      · exact prime_oneHundredNineteenDM_440482171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 777594629002747) ^ 388797314501373 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 777594629002747) ^ 259198209667582 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 777594629002747) ^ 25083697709766 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 777594629002747) ^ 81929683806 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 777594629002747) ^ 1765326 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_866934580455847 : Nat.Prime 866934580455847 := by
  apply lucas_primality 866934580455847 (3 : ZMod 866934580455847)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (6880433178221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (6880433178221, 1)] : List FactorBlock).map factorBlockValue).prod) = 866934580455847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_6880433178221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 866934580455847) ^ 433467290227923 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 866934580455847) ^ 288978193485282 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 866934580455847) ^ 123847797207978 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 866934580455847) ^ 126 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_868948366147837 : Nat.Prime 868948366147837 := by
  apply lucas_primality 868948366147837 (2 : ZMod 868948366147837)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (12479, 1), (446364439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (12479, 1), (446364439, 1)] : List FactorBlock).map factorBlockValue).prod) = 868948366147837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_13
      · exact prime_oneHundredNineteenDM_12479
      · exact prime_oneHundredNineteenDM_446364439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 868948366147837) ^ 434474183073918 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 868948366147837) ^ 289649455382612 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 868948366147837) ^ 66842182011372 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 868948366147837) ^ 69632852484 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 868948366147837) ^ 1946724 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_1208088707119531 : Nat.Prime 1208088707119531 := by
  apply lucas_primality 1208088707119531 (2 : ZMod 1208088707119531)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (40269623570651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (40269623570651, 1)] : List FactorBlock).map factorBlockValue).prod) = 1208088707119531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_40269623570651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1208088707119531) ^ 604044353559765 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1208088707119531) ^ 402696235706510 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1208088707119531) ^ 241617741423906 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1208088707119531) ^ 30 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_1319175671645527 : Nat.Prime 1319175671645527 := by
  apply lucas_primality 1319175671645527 (3 : ZMod 1319175671645527)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (107, 1), (2054790765803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (107, 1), (2054790765803, 1)] : List FactorBlock).map factorBlockValue).prod) = 1319175671645527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_107
      · exact prime_oneHundredNineteenDM_2054790765803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1319175671645527) ^ 659587835822763 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1319175671645527) ^ 439725223881842 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1319175671645527) ^ 12328744594818 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1319175671645527) ^ 642 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_1412201054819831 : Nat.Prime 1412201054819831 := by
  apply lucas_primality 1412201054819831 (19 : ZMod 1412201054819831)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (43, 1), (518863, 1), (575417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (43, 1), (518863, 1), (575417, 1)] : List FactorBlock).map factorBlockValue).prod) = 1412201054819831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_11
      · exact prime_oneHundredNineteenDM_43
      · exact prime_oneHundredNineteenDM_518863
      · exact prime_oneHundredNineteenDM_575417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 1412201054819831) ^ 706100527409915 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (19 : ZMod 1412201054819831) ^ 282440210963966 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (19 : ZMod 1412201054819831) ^ 128381914074530 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (19 : ZMod 1412201054819831) ^ 32841884995810 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (19 : ZMod 1412201054819831) ^ 2721722410 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (19 : ZMod 1412201054819831) ^ 2454221990 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_1630328022651197 : Nat.Prime 1630328022651197 := by
  apply lucas_primality 1630328022651197 (2 : ZMod 1630328022651197)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (1201, 1), (1663, 1), (2659, 1), (6977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (1201, 1), (1663, 1), (2659, 1), (6977, 1)] : List FactorBlock).map factorBlockValue).prod) = 1630328022651197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_11
      · exact prime_oneHundredNineteenDM_1201
      · exact prime_oneHundredNineteenDM_1663
      · exact prime_oneHundredNineteenDM_2659
      · exact prime_oneHundredNineteenDM_6977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1630328022651197) ^ 815164011325598 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1630328022651197) ^ 148211638422836 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1630328022651197) ^ 1357475455996 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1630328022651197) ^ 980353591492 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1630328022651197) ^ 613135773844 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1630328022651197) ^ 233671781948 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_1912574647167469 : Nat.Prime 1912574647167469 := by
  apply lucas_primality 1912574647167469 (2 : ZMod 1912574647167469)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (523, 1), (29347, 1), (10384169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (523, 1), (29347, 1), (10384169, 1)] : List FactorBlock).map factorBlockValue).prod) = 1912574647167469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_523
      · exact prime_oneHundredNineteenDM_29347
      · exact prime_oneHundredNineteenDM_10384169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1912574647167469) ^ 956287323583734 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1912574647167469) ^ 637524882389156 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1912574647167469) ^ 3656930491716 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1912574647167469) ^ 65171044644 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1912574647167469) ^ 184181772 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_2642915032645219 : Nat.Prime 2642915032645219 := by
  apply lucas_primality 2642915032645219 (2 : ZMod 2642915032645219)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (109, 1), (4041154484167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (109, 1), (4041154484167, 1)] : List FactorBlock).map factorBlockValue).prod) = 2642915032645219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_109
      · exact prime_oneHundredNineteenDM_4041154484167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2642915032645219) ^ 1321457516322609 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2642915032645219) ^ 880971677548406 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2642915032645219) ^ 24246926905002 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2642915032645219) ^ 654 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_3208694665773523 : Nat.Prime 3208694665773523 := by
  apply lucas_primality 3208694665773523 (3 : ZMod 3208694665773523)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (571, 1), (7717, 1), (121364741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (571, 1), (7717, 1), (121364741, 1)] : List FactorBlock).map factorBlockValue).prod) = 3208694665773523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_571
      · exact prime_oneHundredNineteenDM_7717
      · exact prime_oneHundredNineteenDM_121364741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3208694665773523) ^ 1604347332886761 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 3208694665773523) ^ 1069564888591174 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 3208694665773523) ^ 5619430237782 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 3208694665773523) ^ 415795602666 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 3208694665773523) ^ 26438442 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_3991077561580867 : Nat.Prime 3991077561580867 := by
  apply lucas_primality 3991077561580867 (2 : ZMod 3991077561580867)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (19, 1), (3889939143841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (19, 1), (3889939143841, 1)] : List FactorBlock).map factorBlockValue).prod) = 3991077561580867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_19
      · exact prime_oneHundredNineteenDM_3889939143841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3991077561580867) ^ 1995538780790433 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3991077561580867) ^ 1330359187193622 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3991077561580867) ^ 210056713767414 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3991077561580867) ^ 1026 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_4103431729145351 : Nat.Prime 4103431729145351 := by
  apply lucas_primality 4103431729145351 (11 : ZMod 4103431729145351)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (17, 1), (19, 1), (79, 1), (269, 1), (1708037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (17, 1), (19, 1), (79, 1), (269, 1), (1708037, 1)] : List FactorBlock).map factorBlockValue).prod) = 4103431729145351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_17
      · exact prime_oneHundredNineteenDM_19
      · exact prime_oneHundredNineteenDM_79
      · exact prime_oneHundredNineteenDM_269
      · exact prime_oneHundredNineteenDM_1708037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 4103431729145351) ^ 2051715864572675 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (11 : ZMod 4103431729145351) ^ 820686345829070 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (11 : ZMod 4103431729145351) ^ 586204532735050 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (11 : ZMod 4103431729145351) ^ 241378337008550 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (11 : ZMod 4103431729145351) ^ 215970091007650 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (11 : ZMod 4103431729145351) ^ 51942173786650 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (11 : ZMod 4103431729145351) ^ 15254393045150 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (11 : ZMod 4103431729145351) ^ 2402425550 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_4206045951343529 : Nat.Prime 4206045951343529 := by
  apply lucas_primality 4206045951343529 (3 : ZMod 4206045951343529)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1628171, 1), (322911871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1628171, 1), (322911871, 1)] : List FactorBlock).map factorBlockValue).prod) = 4206045951343529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_1628171
      · exact prime_oneHundredNineteenDM_322911871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4206045951343529) ^ 2103022975671764 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 4206045951343529) ^ 2583294968 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 4206045951343529) ^ 13025368 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_4306674366049381 : Nat.Prime 4306674366049381 := by
  apply lucas_primality 4306674366049381 (2 : ZMod 4306674366049381)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 1), (31, 1), (178108948141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 1), (31, 1), (178108948141, 1)] : List FactorBlock).map factorBlockValue).prod) = 4306674366049381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_13
      · exact prime_oneHundredNineteenDM_31
      · exact prime_oneHundredNineteenDM_178108948141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4306674366049381) ^ 2153337183024690 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4306674366049381) ^ 1435558122016460 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4306674366049381) ^ 861334873209876 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4306674366049381) ^ 331282643542260 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4306674366049381) ^ 138924979549980 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4306674366049381) ^ 24180 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_13382175235016897 : Nat.Prime 13382175235016897 := by
  apply lucas_primality 13382175235016897 (3 : ZMod 13382175235016897)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (11, 1), (151433, 1), (17932279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (11, 1), (151433, 1), (17932279, 1)] : List FactorBlock).map factorBlockValue).prod) = 13382175235016897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_11
      · exact prime_oneHundredNineteenDM_151433
      · exact prime_oneHundredNineteenDM_17932279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13382175235016897) ^ 6691087617508448 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 13382175235016897) ^ 1911739319288128 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 13382175235016897) ^ 1216561385001536 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 13382175235016897) ^ 88370270912 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 13382175235016897) ^ 746261824 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_17199000483384449 : Nat.Prime 17199000483384449 := by
  apply lucas_primality 17199000483384449 (3 : ZMod 17199000483384449)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (614279, 1), (218739679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (614279, 1), (218739679, 1)] : List FactorBlock).map factorBlockValue).prod) = 17199000483384449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_614279
      · exact prime_oneHundredNineteenDM_218739679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 17199000483384449) ^ 8599500241692224 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 17199000483384449) ^ 27998678912 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 17199000483384449) ^ 78627712 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_18864898813017137 : Nat.Prime 18864898813017137 := by
  apply lucas_primality 18864898813017137 (3 : ZMod 18864898813017137)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (193, 1), (4649, 1), (119460673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (193, 1), (4649, 1), (119460673, 1)] : List FactorBlock).map factorBlockValue).prod) = 18864898813017137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_11
      · exact prime_oneHundredNineteenDM_193
      · exact prime_oneHundredNineteenDM_4649
      · exact prime_oneHundredNineteenDM_119460673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 18864898813017137) ^ 9432449406508568 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 18864898813017137) ^ 1714990801183376 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 18864898813017137) ^ 97745589704752 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 18864898813017137) ^ 4057840140464 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 18864898813017137) ^ 157917232 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_21288946847504111 : Nat.Prime 21288946847504111 := by
  apply lucas_primality 21288946847504111 (23 : ZMod 21288946847504111)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1163, 1), (12107, 1), (151195171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1163, 1), (12107, 1), (151195171, 1)] : List FactorBlock).map factorBlockValue).prod) = 21288946847504111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_1163
      · exact prime_oneHundredNineteenDM_12107
      · exact prime_oneHundredNineteenDM_151195171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 21288946847504111) ^ 10644473423752055 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (23 : ZMod 21288946847504111) ^ 4257789369500822 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (23 : ZMod 21288946847504111) ^ 18305199352970 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (23 : ZMod 21288946847504111) ^ 1758399838730 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (23 : ZMod 21288946847504111) ^ 140804410 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_22282656120377959 : Nat.Prime 22282656120377959 := by
  apply lucas_primality 22282656120377959 (3 : ZMod 22282656120377959)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (434981, 1), (8537789053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (434981, 1), (8537789053, 1)] : List FactorBlock).map factorBlockValue).prod) = 22282656120377959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_434981
      · exact prime_oneHundredNineteenDM_8537789053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 22282656120377959) ^ 11141328060188979 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 22282656120377959) ^ 7427552040125986 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 22282656120377959) ^ 51226734318 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 22282656120377959) ^ 2609886 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_26020797708646759 : Nat.Prime 26020797708646759 := by
  apply lucas_primality 26020797708646759 (3 : ZMod 26020797708646759)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (79, 1), (241, 1), (247519, 1), (920273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (79, 1), (241, 1), (247519, 1), (920273, 1)] : List FactorBlock).map factorBlockValue).prod) = 26020797708646759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_79
      · exact prime_oneHundredNineteenDM_241
      · exact prime_oneHundredNineteenDM_247519
      · exact prime_oneHundredNineteenDM_920273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 26020797708646759) ^ 13010398854323379 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 26020797708646759) ^ 8673599236215586 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 26020797708646759) ^ 329377186185402 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 26020797708646759) ^ 107970114973638 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 26020797708646759) ^ 105126465882 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 26020797708646759) ^ 28275085446 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_31282141181322133 : Nat.Prime 31282141181322133 := by
  apply lucas_primality 31282141181322133 (6 : ZMod 31282141181322133)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (868948366147837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (868948366147837, 1)] : List FactorBlock).map factorBlockValue).prod) = 31282141181322133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_868948366147837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 31282141181322133) ^ 15641070590661066 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 31282141181322133) ^ 10427380393774044 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 31282141181322133) ^ 36 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_41649823415891969 : Nat.Prime 41649823415891969 := by
  apply lucas_primality 41649823415891969 (3 : ZMod 41649823415891969)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 11), (19, 1), (1070359359989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 11), (19, 1), (1070359359989, 1)] : List FactorBlock).map factorBlockValue).prod) = 41649823415891969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_19
      · exact prime_oneHundredNineteenDM_1070359359989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 41649823415891969) ^ 20824911707945984 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 41649823415891969) ^ 2192095969257472 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 41649823415891969) ^ 38912 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_42534581323081763 : Nat.Prime 42534581323081763 := by
  apply lucas_primality 42534581323081763 (2 : ZMod 42534581323081763)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (55510787, 1), (383119963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (55510787, 1), (383119963, 1)] : List FactorBlock).map factorBlockValue).prod) = 42534581323081763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_55510787
      · exact prime_oneHundredNineteenDM_383119963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 42534581323081763) ^ 21267290661540881 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 42534581323081763) ^ 766239926 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 42534581323081763) ^ 111021574 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_53241274286720537 : Nat.Prime 53241274286720537 := by
  apply lucas_primality 53241274286720537 (3 : ZMod 53241274286720537)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (145829, 1), (45636734023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (145829, 1), (45636734023, 1)] : List FactorBlock).map factorBlockValue).prod) = 53241274286720537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_145829
      · exact prime_oneHundredNineteenDM_45636734023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 53241274286720537) ^ 26620637143360268 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 53241274286720537) ^ 365093872184 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 53241274286720537) ^ 1166632 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_58648223132008073 : Nat.Prime 58648223132008073 := by
  apply lucas_primality 58648223132008073 (3 : ZMod 58648223132008073)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (47, 1), (251, 1), (36554796541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (47, 1), (251, 1), (36554796541, 1)] : List FactorBlock).map factorBlockValue).prod) = 58648223132008073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_17
      · exact prime_oneHundredNineteenDM_47
      · exact prime_oneHundredNineteenDM_251
      · exact prime_oneHundredNineteenDM_36554796541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 58648223132008073) ^ 29324111566004036 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 58648223132008073) ^ 3449895478353416 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 58648223132008073) ^ 1247834534723576 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 58648223132008073) ^ 233658259490072 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 58648223132008073) ^ 1604392 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_71052093012238589 : Nat.Prime 71052093012238589 := by
  apply lucas_primality 71052093012238589 (2 : ZMod 71052093012238589)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (12391237, 1), (1433514931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (12391237, 1), (1433514931, 1)] : List FactorBlock).map factorBlockValue).prod) = 71052093012238589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_12391237
      · exact prime_oneHundredNineteenDM_1433514931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 71052093012238589) ^ 35526046506119294 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 71052093012238589) ^ 5734059724 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 71052093012238589) ^ 49564948 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_86585283623066159 : Nat.Prime 86585283623066159 := by
  apply lucas_primality 86585283623066159 (7 : ZMod 86585283623066159)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (47, 1), (1063, 1), (123789818377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (47, 1), (1063, 1), (123789818377, 1)] : List FactorBlock).map factorBlockValue).prod) = 86585283623066159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_47
      · exact prime_oneHundredNineteenDM_1063
      · exact prime_oneHundredNineteenDM_123789818377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 86585283623066159) ^ 43292641811533079 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 86585283623066159) ^ 12369326231866594 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 86585283623066159) ^ 1842240077086514 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 86585283623066159) ^ 81453700492066 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 86585283623066159) ^ 699454 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_256671378070320569 : Nat.Prime 256671378070320569 := by
  apply lucas_primality 256671378070320569 (3 : ZMod 256671378070320569)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17147257, 1), (1871081903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17147257, 1), (1871081903, 1)] : List FactorBlock).map factorBlockValue).prod) = 256671378070320569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_17147257
      · exact prime_oneHundredNineteenDM_1871081903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 256671378070320569) ^ 128335689035160284 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 256671378070320569) ^ 14968655224 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 256671378070320569) ^ 137178056 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_282340849468204369 : Nat.Prime 282340849468204369 := by
  apply lucas_primality 282340849468204369 (7 : ZMod 282340849468204369)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (79, 1), (8272997230081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (79, 1), (8272997230081, 1)] : List FactorBlock).map factorBlockValue).prod) = 282340849468204369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_79
      · exact prime_oneHundredNineteenDM_8272997230081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 282340849468204369) ^ 141170424734102184 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 282340849468204369) ^ 94113616489401456 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 282340849468204369) ^ 3573934803394992 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 282340849468204369) ^ 34128 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_343207110292651133 : Nat.Prime 343207110292651133 := by
  apply lucas_primality 343207110292651133 (2 : ZMod 343207110292651133)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (41, 1), (373, 1), (510047838721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (41, 1), (373, 1), (510047838721, 1)] : List FactorBlock).map factorBlockValue).prod) = 343207110292651133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_11
      · exact prime_oneHundredNineteenDM_41
      · exact prime_oneHundredNineteenDM_373
      · exact prime_oneHundredNineteenDM_510047838721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 343207110292651133) ^ 171603555146325566 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 343207110292651133) ^ 31200646390241012 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 343207110292651133) ^ 8370905129089052 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 343207110292651133) ^ 920126301052684 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 343207110292651133) ^ 672892 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_353228330158537153 : Nat.Prime 353228330158537153 := by
  apply lucas_primality 353228330158537153 (5 : ZMod 353228330158537153)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (11, 1), (43607, 1), (3835353553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (11, 1), (43607, 1), (3835353553, 1)] : List FactorBlock).map factorBlockValue).prod) = 353228330158537153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_11
      · exact prime_oneHundredNineteenDM_43607
      · exact prime_oneHundredNineteenDM_3835353553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 353228330158537153) ^ 176614165079268576 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 353228330158537153) ^ 117742776719512384 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 353228330158537153) ^ 32111666378048832 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 353228330158537153) ^ 8100266703936 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 353228330158537153) ^ 92097984 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_354889808269035289 : Nat.Prime 354889808269035289 := by
  apply lucas_primality 354889808269035289 (7 : ZMod 354889808269035289)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (6646427, 1), (2224815731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (6646427, 1), (2224815731, 1)] : List FactorBlock).map factorBlockValue).prod) = 354889808269035289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_6646427
      · exact prime_oneHundredNineteenDM_2224815731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 354889808269035289) ^ 177444904134517644 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 354889808269035289) ^ 118296602756345096 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 354889808269035289) ^ 53395577544 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 354889808269035289) ^ 159514248 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_617374214330106637 : Nat.Prime 617374214330106637 := by
  apply lucas_primality 617374214330106637 (5 : ZMod 617374214330106637)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (1319175671645527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (1319175671645527, 1)] : List FactorBlock).map factorBlockValue).prod) = 617374214330106637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_13
      · exact prime_oneHundredNineteenDM_1319175671645527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 617374214330106637) ^ 308687107165053318 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 617374214330106637) ^ 205791404776702212 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 617374214330106637) ^ 47490324179238972 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 617374214330106637) ^ 468 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_807775455430923731 : Nat.Prime 807775455430923731 := by
  apply lucas_primality 807775455430923731 (2 : ZMod 807775455430923731)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (104264789, 1), (774734657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (104264789, 1), (774734657, 1)] : List FactorBlock).map factorBlockValue).prod) = 807775455430923731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_104264789
      · exact prime_oneHundredNineteenDM_774734657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 807775455430923731) ^ 403887727715461865 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 807775455430923731) ^ 161555091086184746 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 807775455430923731) ^ 7747346570 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 807775455430923731) ^ 1042647890 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_895143443271670063 : Nat.Prime 895143443271670063 := by
  apply lucas_primality 895143443271670063 (3 : ZMod 895143443271670063)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (67411, 1), (81968474141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (67411, 1), (81968474141, 1)] : List FactorBlock).map factorBlockValue).prod) = 895143443271670063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_67411
      · exact prime_oneHundredNineteenDM_81968474141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 895143443271670063) ^ 447571721635835031 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 895143443271670063) ^ 298381147757223354 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 895143443271670063) ^ 13278892810842 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 895143443271670063) ^ 10920582 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_1368924715224806567 : Nat.Prime 1368924715224806567 := by
  apply lucas_primality 1368924715224806567 (5 : ZMod 1368924715224806567)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (127, 1), (179, 1), (30108756328351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (127, 1), (179, 1), (30108756328351, 1)] : List FactorBlock).map factorBlockValue).prod) = 1368924715224806567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_127
      · exact prime_oneHundredNineteenDM_179
      · exact prime_oneHundredNineteenDM_30108756328351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1368924715224806567) ^ 684462357612403283 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1368924715224806567) ^ 10778934765549658 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1368924715224806567) ^ 7647624107401154 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1368924715224806567) ^ 45466 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_1518842160892481233 : Nat.Prime 1518842160892481233 := by
  apply lucas_primality 1518842160892481233 (5 : ZMod 1518842160892481233)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (41, 1), (149, 1), (2341, 1), (2767, 1), (799633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (41, 1), (149, 1), (2341, 1), (2767, 1), (799633, 1)] : List FactorBlock).map factorBlockValue).prod) = 1518842160892481233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_41
      · exact prime_oneHundredNineteenDM_149
      · exact prime_oneHundredNineteenDM_2341
      · exact prime_oneHundredNineteenDM_2767
      · exact prime_oneHundredNineteenDM_799633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1518842160892481233) ^ 759421080446240616 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1518842160892481233) ^ 506280720297493744 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1518842160892481233) ^ 37044930753475152 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1518842160892481233) ^ 10193571549613968 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1518842160892481233) ^ 648800581329552 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1518842160892481233) ^ 548912960206896 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1518842160892481233) ^ 1899424061904 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_2483734212240360983 : Nat.Prime 2483734212240360983 := by
  apply lucas_primality 2483734212240360983 (7 : ZMod 2483734212240360983)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (173, 1), (36073, 1), (28428157897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (173, 1), (36073, 1), (28428157897, 1)] : List FactorBlock).map factorBlockValue).prod) = 2483734212240360983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_173
      · exact prime_oneHundredNineteenDM_36073
      · exact prime_oneHundredNineteenDM_28428157897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2483734212240360983) ^ 1241867106120180491 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 2483734212240360983) ^ 354819173177194426 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 2483734212240360983) ^ 14356845157458734 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 2483734212240360983) ^ 68852998426534 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 2483734212240360983) ^ 87368806 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_2656574897467719719 : Nat.Prime 2656574897467719719 := by
  apply lucas_primality 2656574897467719719 (7 : ZMod 2656574897467719719)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (37, 1), (42323, 1), (121175790187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (37, 1), (42323, 1), (121175790187, 1)] : List FactorBlock).map factorBlockValue).prod) = 2656574897467719719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_37
      · exact prime_oneHundredNineteenDM_42323
      · exact prime_oneHundredNineteenDM_121175790187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2656574897467719719) ^ 1328287448733859859 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 2656574897467719719) ^ 379510699638245674 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 2656574897467719719) ^ 71799321553181614 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 2656574897467719719) ^ 62769059316866 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 2656574897467719719) ^ 21923314 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_10780197878953463899 : Nat.Prime 10780197878953463899 := by
  apply lucas_primality 10780197878953463899 (2 : ZMod 10780197878953463899)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (256671378070320569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (256671378070320569, 1)] : List FactorBlock).map factorBlockValue).prod) = 10780197878953463899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_256671378070320569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10780197878953463899) ^ 5390098939476731949 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 10780197878953463899) ^ 3593399292984487966 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 10780197878953463899) ^ 1540028268421923414 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 10780197878953463899) ^ 42 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_17522078748213780197 : Nat.Prime 17522078748213780197 := by
  apply lucas_primality 17522078748213780197 (2 : ZMod 17522078748213780197)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13453541, 1), (325603473989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13453541, 1), (325603473989, 1)] : List FactorBlock).map factorBlockValue).prod) = 17522078748213780197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_13453541
      · exact prime_oneHundredNineteenDM_325603473989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 17522078748213780197) ^ 8761039374106890098 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 17522078748213780197) ^ 1302413895956 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 17522078748213780197) ^ 53814164 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_34511947569701930831 : Nat.Prime 34511947569701930831 := by
  apply lucas_primality 34511947569701930831 (19 : ZMod 34511947569701930831)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (3148109, 1), (64486793911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (3148109, 1), (64486793911, 1)] : List FactorBlock).map factorBlockValue).prod) = 34511947569701930831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_17
      · exact prime_oneHundredNineteenDM_3148109
      · exact prime_oneHundredNineteenDM_64486793911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 34511947569701930831) ^ 17255973784850965415 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (19 : ZMod 34511947569701930831) ^ 6902389513940386166 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (19 : ZMod 34511947569701930831) ^ 2030114562923642990 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (19 : ZMod 34511947569701930831) ^ 10962754964870 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (19 : ZMod 34511947569701930831) ^ 535178530 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_136114172542979742973 : Nat.Prime 136114172542979742973 := by
  apply lucas_primality 136114172542979742973 (5 : ZMod 136114172542979742973)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (91571, 1), (2527947581639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (91571, 1), (2527947581639, 1)] : List FactorBlock).map factorBlockValue).prod) = 136114172542979742973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_91571
      · exact prime_oneHundredNineteenDM_2527947581639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 136114172542979742973) ^ 68057086271489871486 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 136114172542979742973) ^ 45371390847659914324 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 136114172542979742973) ^ 19444881791854248996 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 136114172542979742973) ^ 1486433178003732 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 136114172542979742973) ^ 53843748 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_168286572181422532853 : Nat.Prime 168286572181422532853 := by
  apply lucas_primality 168286572181422532853 (2 : ZMod 168286572181422532853)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (199, 1), (2208071, 1), (1954012253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (199, 1), (2208071, 1), (1954012253, 1)] : List FactorBlock).map factorBlockValue).prod) = 168286572181422532853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_199
      · exact prime_oneHundredNineteenDM_2208071
      · exact prime_oneHundredNineteenDM_1954012253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 168286572181422532853) ^ 84143286090711266426 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 168286572181422532853) ^ 24040938883060361836 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 168286572181422532853) ^ 845661166740816748 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 168286572181422532853) ^ 76214293916012 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 168286572181422532853) ^ 86123601284 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_188497949592909006203 : Nat.Prime 188497949592909006203 := by
  apply lucas_primality 188497949592909006203 (2 : ZMod 188497949592909006203)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (389, 1), (4051, 1), (59808758887459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (389, 1), (4051, 1), (59808758887459, 1)] : List FactorBlock).map factorBlockValue).prod) = 188497949592909006203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_389
      · exact prime_oneHundredNineteenDM_4051
      · exact prime_oneHundredNineteenDM_59808758887459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 188497949592909006203) ^ 94248974796454503101 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 188497949592909006203) ^ 484570564506192818 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 188497949592909006203) ^ 46531214414443102 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 188497949592909006203) ^ 3151678 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_237411658455564283589 : Nat.Prime 237411658455564283589 := by
  apply lucas_primality 237411658455564283589 (2 : ZMod 237411658455564283589)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (73, 1), (79, 1), (605401060944023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (73, 1), (79, 1), (605401060944023, 1)] : List FactorBlock).map factorBlockValue).prod) = 237411658455564283589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_17
      · exact prime_oneHundredNineteenDM_73
      · exact prime_oneHundredNineteenDM_79
      · exact prime_oneHundredNineteenDM_605401060944023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 237411658455564283589) ^ 118705829227782141794 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 13965391673856722564 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 3252214499391291556 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 3005210866526130172 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 392156 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_538548168759442385429 : Nat.Prime 538548168759442385429 := by
  apply lucas_primality 538548168759442385429 (2 : ZMod 538548168759442385429)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (66213193, 1), (2033386944349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (66213193, 1), (2033386944349, 1)] : List FactorBlock).map factorBlockValue).prod) = 538548168759442385429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_66213193
      · exact prime_oneHundredNineteenDM_2033386944349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 538548168759442385429) ^ 269274084379721192714 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 538548168759442385429) ^ 8133547777396 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 538548168759442385429) ^ 264852772 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_660760322542495611959 : Nat.Prime 660760322542495611959 := by
  apply lucas_primality 660760322542495611959 (37 : ZMod 660760322542495611959)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (409, 1), (807775455430923731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (409, 1), (807775455430923731, 1)] : List FactorBlock).map factorBlockValue).prod) = 660760322542495611959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_409
      · exact prime_oneHundredNineteenDM_807775455430923731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (37 : ZMod 660760322542495611959) ^ 330380161271247805979 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (37 : ZMod 660760322542495611959) ^ 1615550910861847462 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (37 : ZMod 660760322542495611959) ^ 818 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_1490987229154148736281 : Nat.Prime 1490987229154148736281 := by
  apply lucas_primality 1490987229154148736281 (3 : ZMod 1490987229154148736281)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (83, 1), (1061, 1), (11069, 1), (12401, 1), (3083581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (83, 1), (1061, 1), (11069, 1), (12401, 1), (3083581, 1)] : List FactorBlock).map factorBlockValue).prod) = 1490987229154148736281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_83
      · exact prime_oneHundredNineteenDM_1061
      · exact prime_oneHundredNineteenDM_11069
      · exact prime_oneHundredNineteenDM_12401
      · exact prime_oneHundredNineteenDM_3083581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1490987229154148736281) ^ 745493614577074368140 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1490987229154148736281) ^ 298197445830829747256 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1490987229154148736281) ^ 17963701556074081160 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1490987229154148736281) ^ 1405266002972807480 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1490987229154148736281) ^ 134699361202832120 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1490987229154148736281) ^ 120231209511664280 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1490987229154148736281) ^ 483524586885880 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_2334900312219571567777 : Nat.Prime 2334900312219571567777 := by
  apply lucas_primality 2334900312219571567777 (5 : ZMod 2334900312219571567777)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (1736981, 1), (4667461964617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (1736981, 1), (4667461964617, 1)] : List FactorBlock).map factorBlockValue).prod) = 2334900312219571567777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_1736981
      · exact prime_oneHundredNineteenDM_4667461964617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2334900312219571567777) ^ 1167450156109785783888 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 2334900312219571567777) ^ 778300104073190522592 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 2334900312219571567777) ^ 1344229045809696 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 2334900312219571567777) ^ 500250528 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_3176075794139636163491 : Nat.Prime 3176075794139636163491 := by
  apply lucas_primality 3176075794139636163491 (6 : ZMod 3176075794139636163491)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (13, 1), (71, 1), (31282141181322133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (13, 1), (71, 1), (31282141181322133, 1)] : List FactorBlock).map factorBlockValue).prod) = 3176075794139636163491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_11
      · exact prime_oneHundredNineteenDM_13
      · exact prime_oneHundredNineteenDM_71
      · exact prime_oneHundredNineteenDM_31282141181322133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3176075794139636163491) ^ 1588037897069818081745 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 3176075794139636163491) ^ 635215158827927232698 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 3176075794139636163491) ^ 288734163103603287590 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 3176075794139636163491) ^ 244313522626125858730 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 3176075794139636163491) ^ 44733461889290650190 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 3176075794139636163491) ^ 101530 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_4801149329623946370427 : Nat.Prime 4801149329623946370427 := by
  apply lucas_primality 4801149329623946370427 (3 : ZMod 4801149329623946370427)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (2681267, 1), (12975558633731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (2681267, 1), (12975558633731, 1)] : List FactorBlock).map factorBlockValue).prod) = 4801149329623946370427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_23
      · exact prime_oneHundredNineteenDM_2681267
      · exact prime_oneHundredNineteenDM_12975558633731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4801149329623946370427) ^ 2400574664811973185213 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 4801149329623946370427) ^ 1600383109874648790142 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 4801149329623946370427) ^ 208745623027128103062 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 4801149329623946370427) ^ 1790627091454878 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 4801149329623946370427) ^ 370014846 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_13736937653415353690267 : Nat.Prime 13736937653415353690267 := by
  apply lucas_primality 13736937653415353690267 (2 : ZMod 13736937653415353690267)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83, 1), (659, 1), (2709199, 1), (46350616811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83, 1), (659, 1), (2709199, 1), (46350616811, 1)] : List FactorBlock).map factorBlockValue).prod) = 13736937653415353690267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_83
      · exact prime_oneHundredNineteenDM_659
      · exact prime_oneHundredNineteenDM_2709199
      · exact prime_oneHundredNineteenDM_46350616811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13736937653415353690267) ^ 6868468826707676845133 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 13736937653415353690267) ^ 165505272932715104702 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 13736937653415353690267) ^ 20845125422481568574 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 13736937653415353690267) ^ 5070479375422534 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 13736937653415353690267) ^ 296370115406 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_19407446188454069752687 : Nat.Prime 19407446188454069752687 := by
  apply lucas_primality 19407446188454069752687 (3 : ZMod 19407446188454069752687)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (16487, 1), (19073, 1), (10286236220731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (16487, 1), (19073, 1), (10286236220731, 1)] : List FactorBlock).map factorBlockValue).prod) = 19407446188454069752687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_16487
      · exact prime_oneHundredNineteenDM_19073
      · exact prime_oneHundredNineteenDM_10286236220731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 19407446188454069752687) ^ 9703723094227034876343 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 19407446188454069752687) ^ 6469148729484689917562 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 19407446188454069752687) ^ 1177136300628014178 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 19407446188454069752687) ^ 1017535059427151982 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 19407446188454069752687) ^ 1886739306 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_22812201574697378882447 : Nat.Prime 22812201574697378882447 := by
  apply lucas_primality 22812201574697378882447 (5 : ZMod 22812201574697378882447)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (139, 1), (11261, 1), (99821153922769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (139, 1), (11261, 1), (99821153922769, 1)] : List FactorBlock).map factorBlockValue).prod) = 22812201574697378882447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_73
      · exact prime_oneHundredNineteenDM_139
      · exact prime_oneHundredNineteenDM_11261
      · exact prime_oneHundredNineteenDM_99821153922769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 22812201574697378882447) ^ 11406100787348689441223 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 22812201574697378882447) ^ 312495911982155875102 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 22812201574697378882447) ^ 164116558091348049514 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 22812201574697378882447) ^ 2025770497708674086 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 22812201574697378882447) ^ 228530734 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_26256715911372349922027 : Nat.Prime 26256715911372349922027 := by
  apply lucas_primality 26256715911372349922027 (2 : ZMod 26256715911372349922027)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (150670193, 1), (87133079836741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (150670193, 1), (87133079836741, 1)] : List FactorBlock).map factorBlockValue).prod) = 26256715911372349922027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_150670193
      · exact prime_oneHundredNineteenDM_87133079836741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 26256715911372349922027) ^ 13128357955686174961013 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 26256715911372349922027) ^ 174266159673482 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 26256715911372349922027) ^ 301340386 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_52477850723865048950759 : Nat.Prime 52477850723865048950759 := by
  apply lucas_primality 52477850723865048950759 (7 : ZMod 52477850723865048950759)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4057, 1), (2091807901, 1), (3091855847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4057, 1), (2091807901, 1), (3091855847, 1)] : List FactorBlock).map factorBlockValue).prod) = 52477850723865048950759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_4057
      · exact prime_oneHundredNineteenDM_2091807901
      · exact prime_oneHundredNineteenDM_3091855847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 52477850723865048950759) ^ 26238925361932524475379 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 52477850723865048950759) ^ 12935136979015294294 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 52477850723865048950759) ^ 25087318342558 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 52477850723865048950759) ^ 16972929308714 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_659373007363936977132817 : Nat.Prime 659373007363936977132817 := by
  apply lucas_primality 659373007363936977132817 (7 : ZMod 659373007363936977132817)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (13736937653415353690267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (13736937653415353690267, 1)] : List FactorBlock).map factorBlockValue).prod) = 659373007363936977132817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_13736937653415353690267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 659373007363936977132817) ^ 329686503681968488566408 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 659373007363936977132817) ^ 219791002454645659044272 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (7 : ZMod 659373007363936977132817) ^ 48 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_4417815713378002539529361 : Nat.Prime 4417815713378002539529361 := by
  apply lucas_primality 4417815713378002539529361 (3 : ZMod 4417815713378002539529361)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (29, 1), (31, 1), (137, 1), (413901017, 1), (1083280327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (29, 1), (31, 1), (137, 1), (413901017, 1), (1083280327, 1)] : List FactorBlock).map factorBlockValue).prod) = 4417815713378002539529361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_29
      · exact prime_oneHundredNineteenDM_31
      · exact prime_oneHundredNineteenDM_137
      · exact prime_oneHundredNineteenDM_413901017
      · exact prime_oneHundredNineteenDM_1083280327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4417815713378002539529361) ^ 2208907856689001269764680 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 4417815713378002539529361) ^ 883563142675600507905872 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 4417815713378002539529361) ^ 152338472875103535845840 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 4417815713378002539529361) ^ 142510184302516210952560 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 4417815713378002539529361) ^ 32246830024656952843280 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 4417815713378002539529361) ^ 10673604393144080 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 4417815713378002539529361) ^ 4078183276541680 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_4613081487580689516488033 : Nat.Prime 4613081487580689516488033 := by
  apply lucas_primality 4613081487580689516488033 (5 : ZMod 4613081487580689516488033)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (97, 1), (719, 1), (17207, 1), (17160791887493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (97, 1), (719, 1), (17207, 1), (17160791887493, 1)] : List FactorBlock).map factorBlockValue).prod) = 4613081487580689516488033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_97
      · exact prime_oneHundredNineteenDM_719
      · exact prime_oneHundredNineteenDM_17207
      · exact prime_oneHundredNineteenDM_17160791887493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4613081487580689516488033) ^ 2306540743790344758244016 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 659011641082955645212576 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 47557541109079273365856 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 6415968689263824084128 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 268093304328511042976 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 268815187424 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_12867181197021754972914947 : Nat.Prime 12867181197021754972914947 := by
  apply lucas_primality 12867181197021754972914947 (2 : ZMod 12867181197021754972914947)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (197, 1), (293, 1), (8329, 1), (13382175235016897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (197, 1), (293, 1), (8329, 1), (13382175235016897, 1)] : List FactorBlock).map factorBlockValue).prod) = 12867181197021754972914947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_197
      · exact prime_oneHundredNineteenDM_293
      · exact prime_oneHundredNineteenDM_8329
      · exact prime_oneHundredNineteenDM_13382175235016897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12867181197021754972914947) ^ 6433590598510877486457473 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 12867181197021754972914947) ^ 65315640594019060776218 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 12867181197021754972914947) ^ 43915294187787559634522 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 12867181197021754972914947) ^ 1544865073480820623474 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 12867181197021754972914947) ^ 961516418 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_127667658083698610593332151 : Nat.Prime 127667658083698610593332151 := by
  apply lucas_primality 127667658083698610593332151 (13 : ZMod 127667658083698610593332151)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (16040611, 1), (146938921, 1), (361103651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (16040611, 1), (146938921, 1), (361103651, 1)] : List FactorBlock).map factorBlockValue).prod) = 127667658083698610593332151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_16040611
      · exact prime_oneHundredNineteenDM_146938921
      · exact prime_oneHundredNineteenDM_361103651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 127667658083698610593332151) ^ 63833829041849305296666075 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (13 : ZMod 127667658083698610593332151) ^ 42555886027899536864444050 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (13 : ZMod 127667658083698610593332151) ^ 25533531616739722118666430 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (13 : ZMod 127667658083698610593332151) ^ 7959027127065085650 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (13 : ZMod 127667658083698610593332151) ^ 868848479455614150 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (13 : ZMod 127667658083698610593332151) ^ 353548510878109650 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_341479998078242400179252501 : Nat.Prime 341479998078242400179252501 := by
  apply lucas_primality 341479998078242400179252501 (10 : ZMod 341479998078242400179252501)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 4), (59, 1), (617, 1), (2657, 1), (1412201054819831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 4), (59, 1), (617, 1), (2657, 1), (1412201054819831, 1)] : List FactorBlock).map factorBlockValue).prod) = 341479998078242400179252501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_59
      · exact prime_oneHundredNineteenDM_617
      · exact prime_oneHundredNineteenDM_2657
      · exact prime_oneHundredNineteenDM_1412201054819831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 341479998078242400179252501) ^ 170739999039121200089626250 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (10 : ZMod 341479998078242400179252501) ^ 68295999615648480035850500 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (10 : ZMod 341479998078242400179252501) ^ 5787796577597328816597500 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (10 : ZMod 341479998078242400179252501) ^ 553452184891802917632500 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (10 : ZMod 341479998078242400179252501) ^ 128520887496515769732500 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (10 : ZMod 341479998078242400179252501) ^ 241806927500 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_1026932548965225320247095113 : Nat.Prime 1026932548965225320247095113 := by
  apply lucas_primality 1026932548965225320247095113 (10 : ZMod 1026932548965225320247095113)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (11, 1), (29, 2), (660760322542495611959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (11, 1), (29, 2), (660760322542495611959, 1)] : List FactorBlock).map factorBlockValue).prod) = 1026932548965225320247095113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_11
      · exact prime_oneHundredNineteenDM_29
      · exact prime_oneHundredNineteenDM_660760322542495611959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1026932548965225320247095113) ^ 513466274482612660123547556 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (10 : ZMod 1026932548965225320247095113) ^ 342310849655075106749031704 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (10 : ZMod 1026932548965225320247095113) ^ 146704649852175045749585016 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (10 : ZMod 1026932548965225320247095113) ^ 93357504451384120022463192 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (10 : ZMod 1026932548965225320247095113) ^ 35411467205697424836106728 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (10 : ZMod 1026932548965225320247095113) ^ 1554168 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_3702362084427259707206632381 : Nat.Prime 3702362084427259707206632381 := by
  apply lucas_primality 3702362084427259707206632381 (2 : ZMod 3702362084427259707206632381)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (211, 1), (3463, 1), (271003, 1), (103871723856029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (211, 1), (3463, 1), (271003, 1), (103871723856029, 1)] : List FactorBlock).map factorBlockValue).prod) = 3702362084427259707206632381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_211
      · exact prime_oneHundredNineteenDM_3463
      · exact prime_oneHundredNineteenDM_271003
      · exact prime_oneHundredNineteenDM_103871723856029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3702362084427259707206632381) ^ 1851181042213629853603316190 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3702362084427259707206632381) ^ 1234120694809086569068877460 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3702362084427259707206632381) ^ 740472416885451941441326476 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3702362084427259707206632381) ^ 17546739736622083920410580 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3702362084427259707206632381) ^ 1069119862670303120764260 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3702362084427259707206632381) ^ 13661701473516011657460 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3702362084427259707206632381) ^ 35643599114220 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_4396554975257370902307875953 : Nat.Prime 4396554975257370902307875953 := by
  apply lucas_primality 4396554975257370902307875953 (5 : ZMod 4396554975257370902307875953)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (41, 1), (101, 1), (5161889773, 1), (4285064009893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (41, 1), (101, 1), (5161889773, 1), (4285064009893, 1)] : List FactorBlock).map factorBlockValue).prod) = 4396554975257370902307875953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_41
      · exact prime_oneHundredNineteenDM_101
      · exact prime_oneHundredNineteenDM_5161889773
      · exact prime_oneHundredNineteenDM_4285064009893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4396554975257370902307875953) ^ 2198277487628685451153937976 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 4396554975257370902307875953) ^ 1465518325085790300769291984 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 4396554975257370902307875953) ^ 107233048177009046397753072 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 4396554975257370902307875953) ^ 43530247279775949527800752 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 4396554975257370902307875953) ^ 851733603118411824 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (5 : ZMod 4396554975257370902307875953) ^ 1026018506399664 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_5627590368329434754954081219 : Nat.Prime 5627590368329434754954081219 := by
  apply lucas_primality 5627590368329434754954081219 (2 : ZMod 5627590368329434754954081219)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (586067, 1), (4801149329623946370427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (586067, 1), (4801149329623946370427, 1)] : List FactorBlock).map factorBlockValue).prod) = 5627590368329434754954081219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_586067
      · exact prime_oneHundredNineteenDM_4801149329623946370427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5627590368329434754954081219) ^ 2813795184164717377477040609 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 5627590368329434754954081219) ^ 9602298659247892740854 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 5627590368329434754954081219) ^ 1172134 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_7034487960411793443692601521 : Nat.Prime 7034487960411793443692601521 := by
  apply lucas_primality 7034487960411793443692601521 (3 : ZMod 7034487960411793443692601521)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (7, 1), (17, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (7, 1), (17, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 7034487960411793443692601521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_7
      · exact prime_oneHundredNineteenDM_17
      · exact prime_oneHundredNineteenDM_171401
      · exact prime_oneHundredNineteenDM_714027719
      · exact prime_oneHundredNineteenDM_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7034487960411793443692601521) ^ 3517243980205896721846300760 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 7034487960411793443692601521) ^ 1406897592082358688738520304 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 7034487960411793443692601521) ^ 1004926851487399063384657360 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 7034487960411793443692601521) ^ 413793409435987849628976560 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 7034487960411793443692601521) ^ 41041113881551411273520 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 7034487960411793443692601521) ^ 9851841564727536080 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 7034487960411793443692601521) ^ 1165105819412316880 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_14068975920823586887385203043 : Nat.Prime 14068975920823586887385203043 := by
  apply lucas_primality 14068975920823586887385203043 (2 : ZMod 14068975920823586887385203043)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7034487960411793443692601521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7034487960411793443692601521, 1)] : List FactorBlock).map factorBlockValue).prod) = 14068975920823586887385203043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_7034487960411793443692601521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 14068975920823586887385203043) ^ 7034487960411793443692601521 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 14068975920823586887385203043) ^ 2 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_28137951841647173774770406099 : Nat.Prime 28137951841647173774770406099 := by
  apply lucas_primality 28137951841647173774770406099 (2 : ZMod 28137951841647173774770406099)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (42099221, 1), (10780197878953463899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (42099221, 1), (10780197878953463899, 1)] : List FactorBlock).map factorBlockValue).prod) = 28137951841647173774770406099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_31
      · exact prime_oneHundredNineteenDM_42099221
      · exact prime_oneHundredNineteenDM_10780197878953463899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 28137951841647173774770406099) ^ 14068975920823586887385203049 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 28137951841647173774770406099) ^ 907675865859586250799045358 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 28137951841647173774770406099) ^ 668372268495114761738 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 28137951841647173774770406099) ^ 2610151702 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_35172439802058967218463007609 : Nat.Prime 35172439802058967218463007609 := by
  apply lucas_primality 35172439802058967218463007609 (3 : ZMod 35172439802058967218463007609)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (1171, 1), (237019, 1), (336031, 1), (4285489367539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (1171, 1), (237019, 1), (336031, 1), (4285489367539, 1)] : List FactorBlock).map factorBlockValue).prod) = 35172439802058967218463007609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_11
      · exact prime_oneHundredNineteenDM_1171
      · exact prime_oneHundredNineteenDM_237019
      · exact prime_oneHundredNineteenDM_336031
      · exact prime_oneHundredNineteenDM_4285489367539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 35172439802058967218463007609) ^ 17586219901029483609231503804 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 35172439802058967218463007609) ^ 3197494527459906110769364328 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 35172439802058967218463007609) ^ 30036242358718161587073448 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 35172439802058967218463007609) ^ 148395022348668111917032 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 35172439802058967218463007609) ^ 104670223289098229682568 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 35172439802058967218463007609) ^ 8207333348783272 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_35172439802058967218463007623 : Nat.Prime 35172439802058967218463007623 := by
  apply lucas_primality 35172439802058967218463007623 (3 : ZMod 35172439802058967218463007623)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (401, 1), (3361, 1), (3600307, 1), (1208088707119531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (401, 1), (3361, 1), (3600307, 1), (1208088707119531, 1)] : List FactorBlock).map factorBlockValue).prod) = 35172439802058967218463007623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_401
      · exact prime_oneHundredNineteenDM_3361
      · exact prime_oneHundredNineteenDM_3600307
      · exact prime_oneHundredNineteenDM_1208088707119531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 35172439802058967218463007623) ^ 17586219901029483609231503811 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 35172439802058967218463007623) ^ 11724146600686322406154335874 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 35172439802058967218463007623) ^ 87711819955259269871478822 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 35172439802058967218463007623) ^ 10464873490645333894216902 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 35172439802058967218463007623) ^ 9769289063976757320546 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (3 : ZMod 35172439802058967218463007623) ^ 29114120175762 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_140689759208235868873852030493 : Nat.Prime 140689759208235868873852030493 := by
  apply lucas_primality 140689759208235868873852030493 (2 : ZMod 140689759208235868873852030493)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (35172439802058967218463007623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (35172439802058967218463007623, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_35172439802058967218463007623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 140689759208235868873852030493) ^ 70344879604117934436926015246 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (2 : ZMod 140689759208235868873852030493) ^ 4 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineteenDM_140689759208235868873852030501 : Nat.Prime 140689759208235868873852030501 := by
  apply lucas_primality 140689759208235868873852030501 (6 : ZMod 140689759208235868873852030501)
  · rw [← oneHundredNineteenDMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 3), (277, 1), (32135038499, 1), (10536894547169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 3), (277, 1), (32135038499, 1), (10536894547169, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineteenDM_2
      · exact prime_oneHundredNineteenDM_3
      · exact prime_oneHundredNineteenDM_5
      · exact prime_oneHundredNineteenDM_277
      · exact prime_oneHundredNineteenDM_32135038499
      · exact prime_oneHundredNineteenDM_10536894547169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 140689759208235868873852030501) ^ 70344879604117934436926015250 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 140689759208235868873852030501) ^ 46896586402745289624617343500 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 140689759208235868873852030501) ^ 28137951841647173774770406100 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 140689759208235868873852030501) ^ 507905267899768479688996500 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 140689759208235868873852030501) ^ 4378079684348719500 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide
    · change (6 : ZMod 140689759208235868873852030501) ^ 13352108496334500 ≠ 1
      rw [← oneHundredNineteenDMFastPow_eq_pow]
      decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030400 : Nat.totient 140689759208235868873852030400 = 45398783408065799221592064000 := by
  rw [← show ((([(2, 6), (5, 2), (7, 1), (17, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030400 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_5, prime_oneHundredNineteenDM_7, prime_oneHundredNineteenDM_17, prime_oneHundredNineteenDM_171401, prime_oneHundredNineteenDM_714027719, prime_oneHundredNineteenDM_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030401 : Nat.totient 140689759208235868873852030401 = 92250104125585383499167360000 := by
  rw [← show ((([(3, 1), (61, 1), (22621, 1), (70571, 1), (1023277, 1), (470630547421, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030401 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_3, prime_oneHundredNineteenDM_61, prime_oneHundredNineteenDM_22621, prime_oneHundredNineteenDM_70571, prime_oneHundredNineteenDM_1023277, prime_oneHundredNineteenDM_470630547421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030402 : Nat.totient 140689759208235868873852030402 = 64344499674184099739039403600 := by
  rw [← show ((([(2, 1), (19, 1), (29, 1), (127667658083698610593332151, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030402 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_19, prime_oneHundredNineteenDM_29, prime_oneHundredNineteenDM_127667658083698610593332151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030403 : Nat.totient 140689759208235868873852030403 = 140611040619811591457552601600 := by
  rw [← show ((([(1789, 1), (2126587, 1), (12896381, 1), (2867484876241, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030403 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_1789, prime_oneHundredNineteenDM_2126587, prime_oneHundredNineteenDM_12896381, prime_oneHundredNineteenDM_2867484876241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030404 : Nat.totient 140689759208235868873852030404 = 45779949856465590675557265408 := by
  rw [← show ((([(2, 2), (3, 2), (83, 1), (113, 2), (373, 1), (2477, 1), (3991077561580867, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030404 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_3, prime_oneHundredNineteenDM_83, prime_oneHundredNineteenDM_113, prime_oneHundredNineteenDM_373, prime_oneHundredNineteenDM_2477, prime_oneHundredNineteenDM_3991077561580867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030405 : Nat.totient 140689759208235868873852030405 = 112138647720383248231455221760 := by
  rw [← show ((([(5, 1), (293, 1), (3877, 1), (1557481, 1), (5556319, 1), (2862326239, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030405 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_5, prime_oneHundredNineteenDM_293, prime_oneHundredNineteenDM_3877, prime_oneHundredNineteenDM_1557481, prime_oneHundredNineteenDM_5556319, prime_oneHundredNineteenDM_2862326239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030406 : Nat.totient 140689759208235868873852030406 = 70340461788404556434386469920 := by
  rw [← show ((([(2, 1), (15923, 1), (4417815713378002539529361, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030406 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_15923, prime_oneHundredNineteenDM_4417815713378002539529361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030407 : Nat.totient 140689759208235868873852030407 = 78877275742062926284039752960 := by
  rw [← show ((([(3, 1), (7, 1), (53, 1), (47582281, 1), (2656574897467719719, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030407 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_3, prime_oneHundredNineteenDM_7, prime_oneHundredNineteenDM_53, prime_oneHundredNineteenDM_47582281, prime_oneHundredNineteenDM_2656574897467719719]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030408 : Nat.totient 140689759208235868873852030408 = 64680065906544038043811142400 := by
  rw [← show ((([(2, 3), (13, 1), (263, 1), (9551, 1), (538548168759442385429, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030408 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_13, prime_oneHundredNineteenDM_263, prime_oneHundredNineteenDM_9551, prime_oneHundredNineteenDM_538548168759442385429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030409 : Nat.totient 140689759208235868873852030409 = 139733408144010298017292992000 := by
  rw [← show ((([(151, 1), (7529, 1), (23029, 1), (795189341, 1), (6757757639, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030409 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_151, prime_oneHundredNineteenDM_7529, prime_oneHundredNineteenDM_23029, prime_oneHundredNineteenDM_795189341, prime_oneHundredNineteenDM_6757757639]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030410 : Nat.totient 140689759208235868873852030410 = 34054472820499266335437036800 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (11, 1), (971, 1), (2003, 1), (6988005883, 1), (31368597763, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030410 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_3, prime_oneHundredNineteenDM_5, prime_oneHundredNineteenDM_11, prime_oneHundredNineteenDM_971, prime_oneHundredNineteenDM_2003, prime_oneHundredNineteenDM_6988005883, prime_oneHundredNineteenDM_31368597763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030411 : Nat.totient 140689759208235868873852030411 = 134545719765419843107150278784 := by
  rw [← show ((([(23, 1), (4967, 1), (11853576017, 1), (103894151639963, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030411 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_23, prime_oneHundredNineteenDM_4967, prime_oneHundredNineteenDM_11853576017, prime_oneHundredNineteenDM_103894151639963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030412 : Nat.totient 140689759208235868873852030412 = 69661919607961449636567510000 := by
  rw [← show ((([(2, 2), (103, 1), (341479998078242400179252501, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030412 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_103, prime_oneHundredNineteenDM_341479998078242400179252501]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030413 : Nat.totient 140689759208235868873852030413 = 90241680923733209818522932000 := by
  rw [← show ((([(3, 2), (47, 1), (59, 1), (65106751, 1), (86585283623066159, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030413 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_3, prime_oneHundredNineteenDM_47, prime_oneHundredNineteenDM_59, prime_oneHundredNineteenDM_65106751, prime_oneHundredNineteenDM_86585283623066159]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030414 : Nat.totient 140689759208235868873852030414 = 60294336577829340345868308768 := by
  rw [← show ((([(2, 1), (7, 1), (47317, 1), (273126599, 1), (777594629002747, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030414 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_7, prime_oneHundredNineteenDM_47317, prime_oneHundredNineteenDM_273126599, prime_oneHundredNineteenDM_777594629002747]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030415 : Nat.totient 140689759208235868873852030415 = 109184911532613081979115710464 := by
  rw [← show ((([(5, 1), (37, 1), (337, 1), (228171525083, 1), (9890071056629, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030415 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_5, prime_oneHundredNineteenDM_37, prime_oneHundredNineteenDM_337, prime_oneHundredNineteenDM_228171525083, prime_oneHundredNineteenDM_9890071056629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030416 : Nat.totient 140689759208235868873852030416 = 46896585724336595263557811200 := by
  rw [← show ((([(2, 4), (3, 1), (70676777, 1), (5244488141, 1), (7907540131, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030416 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_3, prime_oneHundredNineteenDM_70676777, prime_oneHundredNineteenDM_5244488141, prime_oneHundredNineteenDM_7907540131]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030417 : Nat.totient 140689759208235868873852030417 = 132413891018664249005631593472 := by
  rw [← show ((([(17, 1), (155440836073, 1), (53241274286720537, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030417 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_17, prime_oneHundredNineteenDM_155440836073, prime_oneHundredNineteenDM_53241274286720537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030418 : Nat.totient 140689759208235868873852030418 = 70338590789061837571903782208 := by
  rw [← show ((([(2, 1), (15173, 1), (46307, 1), (526373, 1), (190204497743003, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030418 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_15173, prime_oneHundredNineteenDM_46307, prime_oneHundredNineteenDM_526373, prime_oneHundredNineteenDM_190204497743003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030419 : Nat.totient 140689759208235868873852030419 = 93716071805800397774901496320 := by
  rw [← show ((([(3, 1), (1423, 1), (8377, 1), (1200946841, 1), (3275850185743, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030419 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_3, prime_oneHundredNineteenDM_1423, prime_oneHundredNineteenDM_8377, prime_oneHundredNineteenDM_1200946841, prime_oneHundredNineteenDM_3275850185743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030420 : Nat.totient 140689759208235868873852030420 = 56275903683294347549540812160 := by
  rw [← show ((([(2, 2), (5, 1), (7034487960411793443692601521, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030420 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_5, prime_oneHundredNineteenDM_7034487960411793443692601521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030421 : Nat.totient 140689759208235868873852030421 = 95869267863466925885952153600 := by
  rw [← show ((([(7, 1), (11, 1), (13, 1), (19, 1), (1094963, 1), (212514941, 1), (31789660873, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030421 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_7, prime_oneHundredNineteenDM_11, prime_oneHundredNineteenDM_13, prime_oneHundredNineteenDM_19, prime_oneHundredNineteenDM_1094963, prime_oneHundredNineteenDM_212514941, prime_oneHundredNineteenDM_31789660873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030422 : Nat.totient 140689759208235868873852030422 = 46896574933428886226693173248 := by
  rw [← show ((([(2, 1), (3, 4), (4264193, 1), (99456199, 1), (2047758613933, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030422 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_3, prime_oneHundredNineteenDM_4264193, prime_oneHundredNineteenDM_99456199, prime_oneHundredNineteenDM_2047758613933]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030423 : Nat.totient 140689759208235868873852030423 = 136210528354721656131697752000 := by
  rw [← show ((([(41, 1), (131, 1), (8163547831, 1), (3208694665773523, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030423 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_41, prime_oneHundredNineteenDM_131, prime_oneHundredNineteenDM_8163547831, prime_oneHundredNineteenDM_3208694665773523]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030424 : Nat.totient 140689759208235868873852030424 = 70344669692715038976728871712 := by
  rw [← show ((([(2, 3), (335117, 1), (52477850723865048950759, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030424 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_335117, prime_oneHundredNineteenDM_52477850723865048950759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030425 : Nat.totient 140689759208235868873852030425 = 73289548863527446958513591040 := by
  rw [← show ((([(3, 1), (5, 2), (43, 1), (613982357, 1), (71052093012238589, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030425 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_3, prime_oneHundredNineteenDM_5, prime_oneHundredNineteenDM_43, prime_oneHundredNineteenDM_613982357, prime_oneHundredNineteenDM_71052093012238589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030426 : Nat.totient 140689759208235868873852030426 = 69553027145685454329217252224 := by
  rw [← show ((([(2, 1), (89, 1), (47623, 1), (2338689173, 1), (7096647417623, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030426 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_89, prime_oneHundredNineteenDM_47623, prime_oneHundredNineteenDM_2338689173, prime_oneHundredNineteenDM_7096647417623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030427 : Nat.totient 140689759208235868873852030427 = 138491461012111901374903168800 := by
  rw [← show ((([(71, 1), (659, 1), (22091, 1), (136114172542979742973, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030427 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_71, prime_oneHundredNineteenDM_659, prime_oneHundredNineteenDM_22091, prime_oneHundredNineteenDM_136114172542979742973]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030428 : Nat.totient 140689759208235868873852030428 = 38744980159763267236566720000 := by
  rw [← show ((([(2, 2), (3, 1), (7, 2), (31, 1), (251, 1), (89597, 1), (343207110292651133, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030428 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_3, prime_oneHundredNineteenDM_7, prime_oneHundredNineteenDM_31, prime_oneHundredNineteenDM_251, prime_oneHundredNineteenDM_89597, prime_oneHundredNineteenDM_343207110292651133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030429 : Nat.totient 140689759208235868873852030429 = 139674924439595417112407077536 := by
  rw [← show ((([(139, 1), (52153, 1), (19407446188454069752687, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030429 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_139, prime_oneHundredNineteenDM_52153, prime_oneHundredNineteenDM_19407446188454069752687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030430 : Nat.totient 140689759208235868873852030430 = 56275903683294347549540812168 := by
  rw [← show ((([(2, 1), (5, 1), (14068975920823586887385203043, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030430 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_5, prime_oneHundredNineteenDM_14068975920823586887385203043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030431 : Nat.totient 140689759208235868873852030431 = 90485288580989271066819369984 := by
  rw [← show ((([(3, 2), (29, 1), (1297, 1), (23719, 1), (17522078748213780197, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030431 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_3, prime_oneHundredNineteenDM_29, prime_oneHundredNineteenDM_1297, prime_oneHundredNineteenDM_23719, prime_oneHundredNineteenDM_17522078748213780197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030432 : Nat.totient 140689759208235868873852030432 = 63894819474541849149630144000 := by
  rw [← show ((([(2, 5), (11, 1), (1171, 1), (237019, 1), (336031, 1), (4285489367539, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030432 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_11, prime_oneHundredNineteenDM_1171, prime_oneHundredNineteenDM_237019, prime_oneHundredNineteenDM_336031, prime_oneHundredNineteenDM_4285489367539]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030433 : Nat.totient 140689759208235868873852030433 = 140689709544502849699514240928 := by
  rw [← show ((([(4718083, 1), (7089619, 1), (4206045951343529, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030433 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_4718083, prime_oneHundredNineteenDM_7089619, prime_oneHundredNineteenDM_4206045951343529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030434 : Nat.totient 140689759208235868873852030434 = 38971312407081665035290894336 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (17, 1), (23, 1), (4613081487580689516488033, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030434 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_3, prime_oneHundredNineteenDM_13, prime_oneHundredNineteenDM_17, prime_oneHundredNineteenDM_23, prime_oneHundredNineteenDM_4613081487580689516488033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030435 : Nat.totient 140689759208235868873852030435 = 96472977742377528464105865216 := by
  rw [← show ((([(5, 1), (7, 1), (233717500609, 1), (17199000483384449, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030435 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_5, prime_oneHundredNineteenDM_7, prime_oneHundredNineteenDM_233717500609, prime_oneHundredNineteenDM_17199000483384449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030436 : Nat.totient 140689759208235868873852030436 = 70344879604117934436926015216 := by
  rw [← show ((([(2, 2), (35172439802058967218463007609, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030436 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_35172439802058967218463007609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030437 : Nat.totient 140689759208235868873852030437 = 93761126597207880653252078592 := by
  rw [← show ((([(3, 1), (2927, 1), (45146593, 1), (354889808269035289, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030437 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_3, prime_oneHundredNineteenDM_2927, prime_oneHundredNineteenDM_45146593, prime_oneHundredNineteenDM_354889808269035289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030438 : Nat.totient 140689759208235868873852030438 = 70228987134894693305061617952 := by
  rw [← show ((([(2, 1), (607, 1), (26493997, 1), (178763147, 1), (24469118563, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030438 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_607, prime_oneHundredNineteenDM_26493997, prime_oneHundredNineteenDM_178763147, prime_oneHundredNineteenDM_24469118563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030439 : Nat.totient 140689759208235868873852030439 = 140653504830877238256068574720 := by
  rw [← show ((([(3881, 1), (40497313, 1), (895143443271670063, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030439 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_3881, prime_oneHundredNineteenDM_40497313, prime_oneHundredNineteenDM_895143443271670063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030440 : Nat.totient 140689759208235868873852030440 = 35363881907702306668880271360 := by
  rw [← show ((([(2, 3), (3, 2), (5, 1), (19, 1), (211, 1), (3463, 1), (271003, 1), (103871723856029, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030440 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_3, prime_oneHundredNineteenDM_5, prime_oneHundredNineteenDM_19, prime_oneHundredNineteenDM_211, prime_oneHundredNineteenDM_3463, prime_oneHundredNineteenDM_271003, prime_oneHundredNineteenDM_103871723856029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030441 : Nat.totient 140689759208235868873852030441 = 140689736396034294176466980692 := by
  rw [← show ((([(6167303, 1), (22812201574697378882447, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030441 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_6167303, prime_oneHundredNineteenDM_22812201574697378882447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030442 : Nat.totient 140689759208235868873852030442 = 60179571213527255535278286336 := by
  rw [← show ((([(2, 1), (7, 1), (557, 1), (7727, 1), (2334900312219571567777, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030442 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_7, prime_oneHundredNineteenDM_557, prime_oneHundredNineteenDM_7727, prime_oneHundredNineteenDM_2334900312219571567777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030443 : Nat.totient 140689759208235868873852030443 = 85222311226450494850025127200 := by
  rw [← show ((([(3, 1), (11, 1), (1931, 1), (1612823, 1), (1368924715224806567, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030443 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_3, prime_oneHundredNineteenDM_11, prime_oneHundredNineteenDM_1931, prime_oneHundredNineteenDM_1612823, prime_oneHundredNineteenDM_1368924715224806567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030444 : Nat.totient 140689759208235868873852030444 = 70339645999417877873965762560 := by
  rw [← show ((([(2, 2), (13441, 1), (1573619289703, 1), (1662919566157, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030444 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_13441, prime_oneHundredNineteenDM_1573619289703, prime_oneHundredNineteenDM_1662919566157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030445 : Nat.totient 140689759208235868873852030445 = 112491907202807827243986416064 := by
  rw [← show ((([(5, 1), (1879, 1), (352065557, 1), (42534581323081763, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030445 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_5, prime_oneHundredNineteenDM_1879, prime_oneHundredNineteenDM_352065557, prime_oneHundredNineteenDM_42534581323081763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030446 : Nat.totient 140689759208235868873852030446 = 46590333733379299783961986560 := by
  rw [← show ((([(2, 1), (3, 1), (199, 1), (661, 1), (2842933297, 1), (62703246890527, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030446 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_3, prime_oneHundredNineteenDM_199, prime_oneHundredNineteenDM_661, prime_oneHundredNineteenDM_2842933297, prime_oneHundredNineteenDM_62703246890527]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030447 : Nat.totient 140689759208235868873852030447 = 128223577681947682088570836992 := by
  rw [← show ((([(13, 1), (79, 1), (387825637, 1), (353228330158537153, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030447 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_13, prime_oneHundredNineteenDM_79, prime_oneHundredNineteenDM_387825637, prime_oneHundredNineteenDM_353228330158537153]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030448 : Nat.totient 140689759208235868873852030448 = 70200434179486828901457178560 := by
  rw [← show ((([(2, 4), (487, 1), (810301391, 1), (22282656120377959, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030448 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_487, prime_oneHundredNineteenDM_810301391, prime_oneHundredNineteenDM_22282656120377959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030449 : Nat.totient 140689759208235868873852030449 = 80336131320850376162582087424 := by
  rw [← show ((([(3, 3), (7, 1), (1613, 1), (12899, 1), (41269, 1), (866934580455847, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030449 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_3, prime_oneHundredNineteenDM_7, prime_oneHundredNineteenDM_1613, prime_oneHundredNineteenDM_12899, prime_oneHundredNineteenDM_41269, prime_oneHundredNineteenDM_866934580455847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030450 : Nat.totient 140689759208235868873852030450 = 56275807660307755070601682320 := by
  rw [← show ((([(2, 1), (5, 2), (586067, 1), (4801149329623946370427, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030450 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_5, prime_oneHundredNineteenDM_586067, prime_oneHundredNineteenDM_4801149329623946370427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030451 : Nat.totient 140689759208235868873852030451 = 132413887220929576591686222208 := by
  rw [← show ((([(17, 1), (34858727, 1), (237411658455564283589, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030451 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_17, prime_oneHundredNineteenDM_34858727, prime_oneHundredNineteenDM_237411658455564283589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030452 : Nat.totient 140689759208235868873852030452 = 45157468391944533523211249664 := by
  rw [← show ((([(2, 2), (3, 1), (37, 1), (167, 1), (239, 1), (5227, 1), (1518842160892481233, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030452 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_3, prime_oneHundredNineteenDM_37, prime_oneHundredNineteenDM_167, prime_oneHundredNineteenDM_239, prime_oneHundredNineteenDM_5227, prime_oneHundredNineteenDM_1518842160892481233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030453 : Nat.totient 140689759208235868873852030453 = 139372118433655470237709641456 := by
  rw [← show ((([(107, 1), (50077, 1), (26256715911372349922027, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030453 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_107, prime_oneHundredNineteenDM_50077, prime_oneHundredNineteenDM_26256715911372349922027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030454 : Nat.totient 140689759208235868873852030454 = 63701058183628276545869578240 := by
  rw [← show ((([(2, 1), (11, 1), (257, 1), (597438929, 1), (41649823415891969, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030454 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_11, prime_oneHundredNineteenDM_257, prime_oneHundredNineteenDM_597438929, prime_oneHundredNineteenDM_41649823415891969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030455 : Nat.totient 140689759208235868873852030455 = 75019233422564897455059252480 := by
  rw [← show ((([(3, 1), (5, 1), (4903, 1), (73517161, 1), (26020797708646759, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030455 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_3, prime_oneHundredNineteenDM_5, prime_oneHundredNineteenDM_4903, prime_oneHundredNineteenDM_73517161, prime_oneHundredNineteenDM_26020797708646759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030456 : Nat.totient 140689759208235868873852030456 = 60295588895572145529368613120 := by
  rw [← show ((([(2, 3), (7, 1), (2717291, 1), (24250644403, 1), (38125454137, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030456 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_7, prime_oneHundredNineteenDM_2717291, prime_oneHundredNineteenDM_24250644403, prime_oneHundredNineteenDM_38125454137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030457 : Nat.totient 140689759208235868873852030457 = 134572669266443098280705482752 := by
  rw [← show ((([(23, 1), (998353, 1), (14797247, 1), (414066027480449, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030457 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_23, prime_oneHundredNineteenDM_998353, prime_oneHundredNineteenDM_14797247, prime_oneHundredNineteenDM_414066027480449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030458 : Nat.totient 140689759208235868873852030458 = 46896586387842884332293694152 := by
  rw [← show ((([(2, 1), (3, 2), (3146913907, 1), (2483734212240360983, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030458 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_3, prime_oneHundredNineteenDM_3146913907, prime_oneHundredNineteenDM_2483734212240360983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030459 : Nat.totient 140689759208235868873852030459 = 127060360798082434444046207520 := by
  rw [← show ((([(19, 1), (31, 1), (67, 1), (908008271987, 1), (3926291898239, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030459 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_19, prime_oneHundredNineteenDM_31, prime_oneHundredNineteenDM_67, prime_oneHundredNineteenDM_908008271987, prime_oneHundredNineteenDM_3926291898239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030460 : Nat.totient 140689759208235868873852030460 = 48154906818129997924259020800 := by
  rw [← show ((([(2, 2), (5, 1), (13, 1), (29, 1), (47, 1), (53, 1), (6581, 1), (331871, 1), (3429700669139, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030460 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_5, prime_oneHundredNineteenDM_13, prime_oneHundredNineteenDM_29, prime_oneHundredNineteenDM_47, prime_oneHundredNineteenDM_53, prime_oneHundredNineteenDM_6581, prime_oneHundredNineteenDM_331871, prime_oneHundredNineteenDM_3429700669139]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030461 : Nat.totient 140689759208235868873852030461 = 93792964547704421438222442048 := by
  rw [← show ((([(3, 1), (454159, 1), (53990197, 1), (1912574647167469, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030461 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_3, prime_oneHundredNineteenDM_454159, prime_oneHundredNineteenDM_53990197, prime_oneHundredNineteenDM_1912574647167469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030462 : Nat.totient 140689759208235868873852030462 = 69181154997969740497866856800 := by
  rw [← show ((([(2, 1), (61, 1), (6571, 1), (29267793559, 1), (5996270350439, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030462 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_61, prime_oneHundredNineteenDM_6571, prime_oneHundredNineteenDM_29267793559, prime_oneHundredNineteenDM_5996270350439]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030463 : Nat.totient 140689759208235868873852030463 = 119823125219463195533108847456 := by
  rw [← show ((([(7, 1), (157, 1), (48437485823, 1), (2642915032645219, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030463 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_7, prime_oneHundredNineteenDM_157, prime_oneHundredNineteenDM_48437485823, prime_oneHundredNineteenDM_2642915032645219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030464 : Nat.totient 140689759208235868873852030464 = 45299769518134930687229952000 := by
  rw [← show ((([(2, 9), (3, 1), (41, 1), (101, 1), (5161889773, 1), (4285064009893, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030464 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_3, prime_oneHundredNineteenDM_41, prime_oneHundredNineteenDM_101, prime_oneHundredNineteenDM_5161889773, prime_oneHundredNineteenDM_4285064009893]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030465 : Nat.totient 140689759208235868873852030465 = 102290048614122719636940940800 := by
  rw [← show ((([(5, 1), (11, 1), (3583, 1), (98887, 1), (553481, 1), (13044008409863, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030465 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_5, prime_oneHundredNineteenDM_11, prime_oneHundredNineteenDM_3583, prime_oneHundredNineteenDM_98887, prime_oneHundredNineteenDM_553481, prime_oneHundredNineteenDM_13044008409863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030466 : Nat.totient 140689759208235868873852030466 = 70273878429739942870469047920 := by
  rw [← show ((([(2, 1), (1039, 1), (21317, 1), (3176075794139636163491, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030466 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_1039, prime_oneHundredNineteenDM_21317, prime_oneHundredNineteenDM_3176075794139636163491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030467 : Nat.totient 140689759208235868873852030467 = 93748751001693615126517529328 := by
  rw [← show ((([(3, 2), (2239, 1), (37039, 1), (188497949592909006203, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030467 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_3, prime_oneHundredNineteenDM_2239, prime_oneHundredNineteenDM_37039, prime_oneHundredNineteenDM_188497949592909006203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030468 : Nat.totient 140689759208235868873852030468 = 64667232023733921551485501440 := by
  rw [← show ((([(2, 2), (17, 1), (43, 1), (4282273, 1), (32701811, 1), (343588771969, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030468 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_17, prime_oneHundredNineteenDM_43, prime_oneHundredNineteenDM_4282273, prime_oneHundredNineteenDM_32701811, prime_oneHundredNineteenDM_343588771969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030469 : Nat.totient 140689759208235868873852030469 = 139531779727893817275530695680 := by
  rw [← show ((([(127, 1), (4673, 1), (6869, 1), (34511947569701930831, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030469 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_127, prime_oneHundredNineteenDM_4673, prime_oneHundredNineteenDM_6869, prime_oneHundredNineteenDM_34511947569701930831]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030470 : Nat.totient 140689759208235868873852030470 = 31697406276307720155556208640 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (7, 1), (73, 1), (1607, 1), (140647657, 1), (40604292994541, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030470 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_3, prime_oneHundredNineteenDM_5, prime_oneHundredNineteenDM_7, prime_oneHundredNineteenDM_73, prime_oneHundredNineteenDM_1607, prime_oneHundredNineteenDM_140647657, prime_oneHundredNineteenDM_40604292994541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030471 : Nat.totient 140689759208235868873852030471 = 138395044382763456203360256000 := by
  rw [← show ((([(109, 1), (181, 1), (593, 1), (2930593, 1), (4103431729145351, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030471 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_109, prime_oneHundredNineteenDM_181, prime_oneHundredNineteenDM_593, prime_oneHundredNineteenDM_2930593, prime_oneHundredNineteenDM_4103431729145351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030472 : Nat.totient 140689759208235868873852030472 = 69144127245096246903776001280 := by
  rw [← show ((([(2, 3), (59, 1), (8171, 1), (22375373, 1), (1630328022651197, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030472 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_59, prime_oneHundredNineteenDM_8171, prime_oneHundredNineteenDM_22375373, prime_oneHundredNineteenDM_1630328022651197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030473 : Nat.totient 140689759208235868873852030473 = 86562488406737646357996084480 := by
  rw [← show ((([(3, 1), (13, 1), (5471, 1), (659373007363936977132817, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030473 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_3, prime_oneHundredNineteenDM_13, prime_oneHundredNineteenDM_5471, prime_oneHundredNineteenDM_659373007363936977132817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030474 : Nat.totient 140689759208235868873852030474 = 70340324407160058544017750480 := by
  rw [← show ((([(2, 1), (15443, 1), (1057690939, 1), (4306674366049381, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030474 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_15443, prime_oneHundredNineteenDM_1057690939, prime_oneHundredNineteenDM_4306674366049381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030475 : Nat.totient 140689759208235868873852030475 = 112551807366588695099081624360 := by
  rw [← show ((([(5, 2), (5627590368329434754954081219, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030475 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_5, prime_oneHundredNineteenDM_5627590368329434754954081219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030476 : Nat.totient 140689759208235868873852030476 = 42392251191283608706164057600 := by
  rw [← show ((([(2, 2), (3, 3), (11, 2), (179, 1), (14957, 1), (657366109, 1), (6117141491, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030476 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_3, prime_oneHundredNineteenDM_11, prime_oneHundredNineteenDM_179, prime_oneHundredNineteenDM_14957, prime_oneHundredNineteenDM_657366109, prime_oneHundredNineteenDM_6117141491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030477 : Nat.totient 140689759208235868873852030477 = 120585301164707325222386073600 := by
  rw [← show ((([(7, 2), (21377, 1), (450301, 1), (10003657, 1), (29816588057, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030477 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_7, prime_oneHundredNineteenDM_21377, prime_oneHundredNineteenDM_450301, prime_oneHundredNineteenDM_10003657, prime_oneHundredNineteenDM_29816588057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030478 : Nat.totient 140689759208235868873852030478 = 66642517519690674729719382840 := by
  rw [← show ((([(2, 1), (19, 1), (3702362084427259707206632381, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030478 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_19, prime_oneHundredNineteenDM_3702362084427259707206632381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030479 : Nat.totient 140689759208235868873852030479 = 93787386335017986750348070400 := by
  rw [← show ((([(3, 1), (21977, 1), (62627, 1), (4444217, 1), (7666832210951, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030479 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_3, prime_oneHundredNineteenDM_21977, prime_oneHundredNineteenDM_62627, prime_oneHundredNineteenDM_4444217, prime_oneHundredNineteenDM_7666832210951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030480 : Nat.totient 140689759208235868873852030480 = 53829125249000658212230277120 := by
  rw [← show ((([(2, 4), (5, 1), (23, 1), (4053126731, 1), (18864898813017137, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030480 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_5, prime_oneHundredNineteenDM_23, prime_oneHundredNineteenDM_4053126731, prime_oneHundredNineteenDM_18864898813017137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030481 : Nat.totient 140689759208235868873852030481 = 139662826659270643553604935232 := by
  rw [← show ((([(137, 1), (1026932548965225320247095113, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030481 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_137, prime_oneHundredNineteenDM_1026932548965225320247095113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030482 : Nat.totient 140689759208235868873852030482 = 46895603225046825116118143760 := by
  rw [← show ((([(2, 1), (3, 1), (47699, 1), (528792879631, 1), (929643341663, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030482 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_3, prime_oneHundredNineteenDM_47699, prime_oneHundredNineteenDM_528792879631, prime_oneHundredNineteenDM_929643341663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030483 : Nat.totient 140689759208235868873852030483 = 140286636668604978617373480768 := by
  rw [← show ((([(349, 1), (6873567479, 1), (58648223132008073, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030483 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_349, prime_oneHundredNineteenDM_6873567479, prime_oneHundredNineteenDM_58648223132008073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030484 : Nat.totient 140689759208235868873852030484 = 60241545509341273842233129472 := by
  rw [← show ((([(2, 2), (7, 1), (1117, 1), (1360213, 1), (1457389, 1), (2269179614687, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030484 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_7, prime_oneHundredNineteenDM_1117, prime_oneHundredNineteenDM_1360213, prime_oneHundredNineteenDM_1457389, prime_oneHundredNineteenDM_2269179614687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030485 : Nat.totient 140689759208235868873852030485 = 70620265234891095332884070400 := by
  rw [← show ((([(3, 2), (5, 1), (17, 1), (148193, 1), (732506743, 1), (1694188519151, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030485 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_3, prime_oneHundredNineteenDM_5, prime_oneHundredNineteenDM_17, prime_oneHundredNineteenDM_148193, prime_oneHundredNineteenDM_732506743, prime_oneHundredNineteenDM_1694188519151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030486 : Nat.totient 140689759208235868873852030486 = 64899923576315412663480769920 := by
  rw [← show ((([(2, 1), (13, 1), (2437, 1), (9059, 1), (41406427, 1), (5919507744571, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030486 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_13, prime_oneHundredNineteenDM_2437, prime_oneHundredNineteenDM_9059, prime_oneHundredNineteenDM_41406427, prime_oneHundredNineteenDM_5919507744571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030487 : Nat.totient 140689759208235868873852030487 = 126327131575329075850820736000 := by
  rw [← show ((([(11, 1), (83, 1), (4111, 1), (132761, 1), (282340849468204369, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030487 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_11, prime_oneHundredNineteenDM_83, prime_oneHundredNineteenDM_4111, prime_oneHundredNineteenDM_132761, prime_oneHundredNineteenDM_282340849468204369]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030488 : Nat.totient 140689759208235868873852030488 = 46765705951369430067087360000 := by
  rw [← show ((([(2, 3), (3, 1), (401, 1), (3361, 1), (3600307, 1), (1208088707119531, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030488 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_3, prime_oneHundredNineteenDM_401, prime_oneHundredNineteenDM_3361, prime_oneHundredNineteenDM_3600307, prime_oneHundredNineteenDM_1208088707119531]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030489 : Nat.totient 140689759208235868873852030489 = 132150406246154612953254858240 := by
  rw [← show ((([(29, 1), (37, 1), (8009, 1), (769007, 1), (21288946847504111, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030489 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_29, prime_oneHundredNineteenDM_37, prime_oneHundredNineteenDM_8009, prime_oneHundredNineteenDM_769007, prime_oneHundredNineteenDM_21288946847504111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030490 : Nat.totient 140689759208235868873852030490 = 54460550657951429568475147200 := by
  rw [← show ((([(2, 1), (5, 1), (31, 1), (42099221, 1), (10780197878953463899, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030490 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_5, prime_oneHundredNineteenDM_31, prime_oneHundredNineteenDM_42099221, prime_oneHundredNineteenDM_10780197878953463899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030491 : Nat.totient 140689759208235868873852030491 = 79564943629304769330196992000 := by
  rw [← show ((([(3, 1), (7, 1), (97, 1), (199501, 1), (4952692709, 1), (69901258927, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030491 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_3, prime_oneHundredNineteenDM_7, prime_oneHundredNineteenDM_97, prime_oneHundredNineteenDM_199501, prime_oneHundredNineteenDM_4952692709, prime_oneHundredNineteenDM_69901258927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030492 : Nat.totient 140689759208235868873852030492 = 70344879604117934436926015244 := by
  rw [← show ((([(2, 2), (35172439802058967218463007623, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030492 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_35172439802058967218463007623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030493 : Nat.totient 140689759208235868873852030493 = 140689759208235868873852030492 := by
  rw [← show ((([(140689759208235868873852030493, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030493 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_140689759208235868873852030493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030494 : Nat.totient 140689759208235868873852030494 = 46813285175471609623306261056 := by
  rw [← show ((([(2, 1), (3, 2), (983, 1), (1567, 1), (8219, 1), (617374214330106637, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030494 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_3, prime_oneHundredNineteenDM_983, prime_oneHundredNineteenDM_1567, prime_oneHundredNineteenDM_8219, prime_oneHundredNineteenDM_617374214330106637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030495 : Nat.totient 140689759208235868873852030495 = 112551807366588695099081624392 := by
  rw [← show ((([(5, 1), (28137951841647173774770406099, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030495 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_5, prime_oneHundredNineteenDM_28137951841647173774770406099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030496 : Nat.totient 140689759208235868873852030496 = 70344879604117934436926015232 := by
  rw [← show ((([(2, 5), (4396554975257370902307875953, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030496 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_4396554975257370902307875953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030497 : Nat.totient 140689759208235868873852030497 = 88456431522613343436347742720 := by
  rw [← show ((([(3, 1), (19, 1), (229, 1), (7229, 1), (1490987229154148736281, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030497 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_3, prime_oneHundredNineteenDM_19, prime_oneHundredNineteenDM_229, prime_oneHundredNineteenDM_7229, prime_oneHundredNineteenDM_1490987229154148736281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030498 : Nat.totient 140689759208235868873852030498 = 54042161027491370886242773200 := by
  rw [← show ((([(2, 1), (7, 1), (11, 1), (71, 1), (12867181197021754972914947, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030498 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_7, prime_oneHundredNineteenDM_11, prime_oneHundredNineteenDM_71, prime_oneHundredNineteenDM_12867181197021754972914947]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030499 : Nat.totient 140689759208235868873852030499 = 129867468018932705090329006560 := by
  rw [← show ((([(13, 1), (64308691, 1), (168286572181422532853, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030499 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_13, prime_oneHundredNineteenDM_64308691, prime_oneHundredNineteenDM_168286572181422532853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030500 : Nat.totient 140689759208235868873852030500 = 37381827716256139238852505600 := by
  rw [← show ((([(2, 2), (3, 1), (5, 3), (277, 1), (32135038499, 1), (10536894547169, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030500 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_2, prime_oneHundredNineteenDM_3, prime_oneHundredNineteenDM_5, prime_oneHundredNineteenDM_277, prime_oneHundredNineteenDM_32135038499, prime_oneHundredNineteenDM_10536894547169]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineteenDM_140689759208235868873852030501 : Nat.totient 140689759208235868873852030501 = 140689759208235868873852030500 := by
  rw [← show ((([(140689759208235868873852030501, 1)] : List FactorBlock).map factorBlockValue).prod) = 140689759208235868873852030501 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineteenDM_140689759208235868873852030501]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredNineteenDM : certifiedKill 1 140689759208235868873852030399 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredNineteenDM_140689759208235868873852030400, phi_oneHundredNineteenDM_140689759208235868873852030401, phi_oneHundredNineteenDM_140689759208235868873852030402,
    phi_oneHundredNineteenDM_140689759208235868873852030403, phi_oneHundredNineteenDM_140689759208235868873852030404, phi_oneHundredNineteenDM_140689759208235868873852030405,
    phi_oneHundredNineteenDM_140689759208235868873852030406, phi_oneHundredNineteenDM_140689759208235868873852030407, phi_oneHundredNineteenDM_140689759208235868873852030408,
    phi_oneHundredNineteenDM_140689759208235868873852030409, phi_oneHundredNineteenDM_140689759208235868873852030410, phi_oneHundredNineteenDM_140689759208235868873852030411,
    phi_oneHundredNineteenDM_140689759208235868873852030412, phi_oneHundredNineteenDM_140689759208235868873852030413, phi_oneHundredNineteenDM_140689759208235868873852030414,
    phi_oneHundredNineteenDM_140689759208235868873852030415, phi_oneHundredNineteenDM_140689759208235868873852030416, phi_oneHundredNineteenDM_140689759208235868873852030417,
    phi_oneHundredNineteenDM_140689759208235868873852030418, phi_oneHundredNineteenDM_140689759208235868873852030419, phi_oneHundredNineteenDM_140689759208235868873852030420,
    phi_oneHundredNineteenDM_140689759208235868873852030421, phi_oneHundredNineteenDM_140689759208235868873852030422, phi_oneHundredNineteenDM_140689759208235868873852030423,
    phi_oneHundredNineteenDM_140689759208235868873852030424, phi_oneHundredNineteenDM_140689759208235868873852030425, phi_oneHundredNineteenDM_140689759208235868873852030426,
    phi_oneHundredNineteenDM_140689759208235868873852030427, phi_oneHundredNineteenDM_140689759208235868873852030428, phi_oneHundredNineteenDM_140689759208235868873852030429,
    phi_oneHundredNineteenDM_140689759208235868873852030430, phi_oneHundredNineteenDM_140689759208235868873852030431, phi_oneHundredNineteenDM_140689759208235868873852030432,
    phi_oneHundredNineteenDM_140689759208235868873852030433, phi_oneHundredNineteenDM_140689759208235868873852030434, phi_oneHundredNineteenDM_140689759208235868873852030435,
    phi_oneHundredNineteenDM_140689759208235868873852030436, phi_oneHundredNineteenDM_140689759208235868873852030437, phi_oneHundredNineteenDM_140689759208235868873852030438,
    phi_oneHundredNineteenDM_140689759208235868873852030439, phi_oneHundredNineteenDM_140689759208235868873852030440, phi_oneHundredNineteenDM_140689759208235868873852030441,
    phi_oneHundredNineteenDM_140689759208235868873852030442, phi_oneHundredNineteenDM_140689759208235868873852030443, phi_oneHundredNineteenDM_140689759208235868873852030444,
    phi_oneHundredNineteenDM_140689759208235868873852030445, phi_oneHundredNineteenDM_140689759208235868873852030446, phi_oneHundredNineteenDM_140689759208235868873852030447,
    phi_oneHundredNineteenDM_140689759208235868873852030448, phi_oneHundredNineteenDM_140689759208235868873852030449, phi_oneHundredNineteenDM_140689759208235868873852030450,
    phi_oneHundredNineteenDM_140689759208235868873852030451, phi_oneHundredNineteenDM_140689759208235868873852030452, phi_oneHundredNineteenDM_140689759208235868873852030453,
    phi_oneHundredNineteenDM_140689759208235868873852030454, phi_oneHundredNineteenDM_140689759208235868873852030455, phi_oneHundredNineteenDM_140689759208235868873852030456,
    phi_oneHundredNineteenDM_140689759208235868873852030457, phi_oneHundredNineteenDM_140689759208235868873852030458, phi_oneHundredNineteenDM_140689759208235868873852030459,
    phi_oneHundredNineteenDM_140689759208235868873852030460, phi_oneHundredNineteenDM_140689759208235868873852030461, phi_oneHundredNineteenDM_140689759208235868873852030462,
    phi_oneHundredNineteenDM_140689759208235868873852030463, phi_oneHundredNineteenDM_140689759208235868873852030464, phi_oneHundredNineteenDM_140689759208235868873852030465,
    phi_oneHundredNineteenDM_140689759208235868873852030466, phi_oneHundredNineteenDM_140689759208235868873852030467, phi_oneHundredNineteenDM_140689759208235868873852030468,
    phi_oneHundredNineteenDM_140689759208235868873852030469, phi_oneHundredNineteenDM_140689759208235868873852030470, phi_oneHundredNineteenDM_140689759208235868873852030471,
    phi_oneHundredNineteenDM_140689759208235868873852030472, phi_oneHundredNineteenDM_140689759208235868873852030473, phi_oneHundredNineteenDM_140689759208235868873852030474,
    phi_oneHundredNineteenDM_140689759208235868873852030475, phi_oneHundredNineteenDM_140689759208235868873852030476, phi_oneHundredNineteenDM_140689759208235868873852030477,
    phi_oneHundredNineteenDM_140689759208235868873852030478, phi_oneHundredNineteenDM_140689759208235868873852030479, phi_oneHundredNineteenDM_140689759208235868873852030480,
    phi_oneHundredNineteenDM_140689759208235868873852030481, phi_oneHundredNineteenDM_140689759208235868873852030482, phi_oneHundredNineteenDM_140689759208235868873852030483,
    phi_oneHundredNineteenDM_140689759208235868873852030484, phi_oneHundredNineteenDM_140689759208235868873852030485, phi_oneHundredNineteenDM_140689759208235868873852030486,
    phi_oneHundredNineteenDM_140689759208235868873852030487, phi_oneHundredNineteenDM_140689759208235868873852030488, phi_oneHundredNineteenDM_140689759208235868873852030489,
    phi_oneHundredNineteenDM_140689759208235868873852030490, phi_oneHundredNineteenDM_140689759208235868873852030491, phi_oneHundredNineteenDM_140689759208235868873852030492,
    phi_oneHundredNineteenDM_140689759208235868873852030493, phi_oneHundredNineteenDM_140689759208235868873852030494, phi_oneHundredNineteenDM_140689759208235868873852030495,
    phi_oneHundredNineteenDM_140689759208235868873852030496, phi_oneHundredNineteenDM_140689759208235868873852030497, phi_oneHundredNineteenDM_140689759208235868873852030498,
    phi_oneHundredNineteenDM_140689759208235868873852030499, phi_oneHundredNineteenDM_140689759208235868873852030500, phi_oneHundredNineteenDM_140689759208235868873852030501]

end TotientTailPeriodKiller
end Erdos249257
